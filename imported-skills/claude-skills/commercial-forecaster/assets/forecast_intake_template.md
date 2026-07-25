# Forecast Intake Template

**Time to fill:** ~20 minutes for Head of Commercial / RevOps / VP Sales.

This template captures the four inputs the `commercial-forecaster` skill needs:

1. **Opportunities** — current pipeline with stage / amount / close-date / age / last-activity
2. **Historical conversion** — stage-to-stage % over last 4 quarters AND last 12 quarters
3. **Cohorts** — per-cohort starting ARR + per-quarter retention + expansion
4. **Funnel history** — per-stage conversion across the last 12 quarters

The output is a single JSON file that feeds all three scripts:

- `scripts/bookings_forecaster.py --input intake.json --profile {saas|api|enterprise-software|marketplace|services}`
- `scripts/cohort_arr_projector.py --input intake.json`
- `scripts/funnel_confidence_scorer.py --input intake.json`

---

## Section 1 — Target period

The quarter / period you're forecasting for.

- Start date (YYYY-MM-DD): __________
- End date (YYYY-MM-DD): __________
- Industry profile (saas / api / enterprise-software / marketplace / services): __________

---

## Section 2 — Opportunities (pipeline snapshot)

Export from your CRM (Salesforce / HubSpot / Pipedrive). One row per opportunity:

| opp_id | stage | amount | close_date | age_days | last_activity_days |
|---|---|---|---|---|---|
| OPP-101 | commit | 180000 | 2026-06-15 | 45 | 3 |
| OPP-102 | verbal | 95000 | 2026-06-22 | 60 | 7 |
| ... | ... | ... | ... | ... | ... |

**Stage values to use** (case-insensitive): `discovery`, `demo_completed`, `proposal`,
`negotiation`, `verbal`, `commit`, `contract_out`, `closed_won_pending`.

**Hygiene check:**
- Filter out any opp older than 365 days that has not moved stage
- Confirm close_date is realistic — if it's already past, the CRM hygiene is the problem first

---

## Section 3 — Historical conversion (last 4Q and last 12Q)

Stage-to-stage conversion percentage, computed from your CRM history.

**Last 4 quarters (recent regime):**

| Stage | Conversion % |
|---|---:|
| discovery | _____ |
| demo_completed | _____ |
| proposal | _____ |
| negotiation | _____ |
| verbal | _____ |
| commit | _____ |

**Last 12 quarters (long-run prior):**

| Stage | Conversion % |
|---|---:|
| discovery | _____ |
| demo_completed | _____ |
| proposal | _____ |
| negotiation | _____ |
| verbal | _____ |
| commit | _____ |

The skill blends 70% last-4Q + 30% last-12Q automatically.

---

## Section 4 — Cohorts

One row per acquisition cohort (typically by quarter):

For each cohort:

- cohort_id (e.g., "2025-Q1")
- acquisition_quarter (e.g., "2025-Q1")
- starting_arr (USD)
- gross_retention_pct_q1, q2, q3, q4 (each is the % of starting ARR retained in that projection
  quarter — typically 85-95)
- expansion_arr_pct_q1, q2, q3, q4 (each is the % expansion ARR — typically 4-15)

If you don't have per-quarter retention for a cohort, leave them blank and the skill will apply
conservative defaults (92%/91%/90%/89% GRR, 4%/6%/8%/10% expansion).

---

## Section 5 — Funnel history (per-stage conversion across 12 quarters)

One row per funnel stage. The conversion_pct_history is a 12-element list of the per-quarter
conversion rate for that stage transition.

- stage_name (e.g., "discovery_to_demo")
- conversion_pct_history (list of 12 numbers, oldest first)

This feeds `funnel_confidence_scorer.py` to compute per-stage CoV and confidence band.

---

## JSON skeleton (paste into `intake.json`)

```json
{
  "target_period": {
    "start_date": "2026-06-01",
    "end_date": "2026-06-30"
  },
  "opportunities": [
    {
      "opp_id": "OPP-101",
      "stage": "commit",
      "amount": 180000,
      "close_date": "2026-06-15",
      "age_days": 45,
      "last_activity_days": 3
    },
    {
      "opp_id": "OPP-102",
      "stage": "verbal",
      "amount": 95000,
      "close_date": "2026-06-22",
      "age_days": 60,
      "last_activity_days": 7
    }
  ],
  "historical_conversion": {
    "stage_X_to_Y_pct_last_4q": {
      "discovery": 0.32,
      "demo_completed": 0.52,
      "proposal": 0.60,
      "negotiation": 0.72,
      "verbal": 0.84,
      "commit": 0.91
    },
    "stage_X_to_Y_pct_last_12q": {
      "discovery": 0.38,
      "demo_completed": 0.58,
      "proposal": 0.67,
      "negotiation": 0.76,
      "verbal": 0.87,
      "commit": 0.93
    }
  },
  "cohorts": [
    {
      "cohort_id": "2025-Q1",
      "acquisition_quarter": "2025-Q1",
      "starting_arr": 1200000,
      "gross_retention_pct_q1": 93,
      "gross_retention_pct_q2": 91,
      "gross_retention_pct_q3": 90,
      "gross_retention_pct_q4": 89,
      "expansion_arr_pct_q1": 5,
      "expansion_arr_pct_q2": 8,
      "expansion_arr_pct_q3": 10,
      "expansion_arr_pct_q4": 11
    }
  ],
  "projection_horizon_quarters": 4,
  "funnel_stages": [
    {
      "stage_name": "discovery_to_demo",
      "conversion_pct_history": [35, 37, 33, 36, 38, 35, 34, 37, 36, 35, 36, 37]
    },
    {
      "stage_name": "demo_to_proposal",
      "conversion_pct_history": [55, 52, 58, 56, 54, 57, 53, 55, 58, 54, 56, 55]
    }
  ]
}
```

---

## Quality gates before running the scripts

- [ ] All opportunities have a stage from the allowed list
- [ ] All opportunities have a close_date (no nulls — fix CRM hygiene first)
- [ ] Last-4Q AND last-12Q conversion provided for at least 4 stages
- [ ] At least 3 cohorts with starting_arr (4+ preferred for leak detection)
- [ ] At least 4 quarters of conversion_pct_history per funnel stage (12 preferred)
- [ ] Industry profile selected

---

## Next steps after intake

1. Save as `intake.json` in your working directory
2. Run `bookings_forecaster.py --input intake.json --profile <profile>` → 3-tier forecast + assumption block
3. Run `cohort_arr_projector.py --input intake.json` → cohort heatmap + leaky callout
4. Run `funnel_confidence_scorer.py --input intake.json` → per-stage confidence bands
5. Assemble the board slide: commit + best-case + pipe-only + assumption block + cohort heatmap + per-stage CoV
6. **The assumption block goes on the slide.** No assumption block = theatre.
