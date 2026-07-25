# Commercial Policy Design — Intake

**Time to fill out: ~20 minutes.** Output of this intake feeds directly into the three skill scripts:

- `discount_matrix_builder.py` ← Section 4 (current deals) + Section 5 (constraints) + Section 6 (industry)
- `exception_router.py` ← Section 7 (exception flow) + audit trail spec
- `policy_linter.py` ← runs against the matrix output once built

Re-pricings or major matrix revisions create a *new* intake — do not edit in place. Version the intake the same way you version the matrix.

---

## 1. Policy owner

| Field | Value |
|---|---|
| Head of Deal Desk / Commercial owner | |
| CFO sign-off contact | |
| CRO / VP Sales sign-off contact | |
| GC / legal contact for exceptions | |
| Target publish date | |
| Version | v1.0.0 |

## 2. Scope

- [ ] New-business discounts
- [ ] Renewal discounts
- [ ] Expansion/upsell discounts
- [ ] Partner/channel-sourced discounts
- [ ] Multi-product bundle discounts

Anything unchecked is **out of scope** for this matrix.

## 3. Industry profile

Pick one (drives the `--profile` flag and tunes the base band widths):

- [ ] `saas` — subscription seat-based or hybrid; typical product GM 75-85%
- [ ] `enterprise-software` — large ACVs; longer cycles; multi-year norm
- [ ] `api` — usage-based; tight bands; consumption-led
- [ ] `marketplace` — take-rate model; thinnest bands
- [ ] `services` — labor-bound; aggressive escalation on small discounts

## 4. Current deal corpus (data backing)

Pull from CRM the **last 4 quarters of closed-won + closed-lost** deals. Aim for n ≥ 50, n ≥ 200 preferred. Each row:

| Field | Notes |
|---|---|
| `arr` | Annual recurring revenue, USD |
| `discount_pct` | Discount taken off list, 0-100 |
| `term_months` | Contract term in months |
| `payment_terms_days` | NET-30 / NET-45 / NET-60 / etc. |
| `strategic_value` | one of: `standard`, `logo`, `expansion`, `lighthouse` |
| `win_lost` | `win` or `lost` |
| `nrr_12mo` | 12-month NRR for the cohort that signed (for closed-won; 0 for closed-lost) |

Save as JSON, populate the `current_deals` array in the intake JSON below.

## 5. Target constraints

| Field | Value | Sourced from |
|---|---|---|
| `min_margin_pct` | | CFO — the gross margin floor below which NO cell can publish |
| `max_discount_pct_without_exception` | | CRO / Head of Deal Desk — the cap above which every deal becomes an exception |
| `target_nrr` | | CFO/CRO — the NRR target the policy is designed to protect |

These three numbers are non-negotiable inputs. The matrix builder will respect them; cells that can't satisfy them will be flagged for explicit exception treatment.

## 6. Strategic-value definitions (REQUIRED — anti-pattern AP-7)

If you use any tier above `standard`, you must define it with **concrete tests**. Vague definitions get flagged by `policy_linter.py` rule L06.

| Tier | Definition (must be testable) | Example |
|---|---|---|
| `standard` | Default. No special strategic claim. | Any deal not meeting one of the below |
| `logo` | Reference-quality customer name | Top-20 named target list for 2026 GTM motion |
| `expansion` | Signed expansion path | MSA includes named BU or product-line expansion within 12 months |
| `lighthouse` | Co-marketed reference + multi-year | Public case study + 2 reference calls/year + 36-month term |

Without `strategic_value_definitions_supplied=true` in the matrix JSON, the linter will reject the matrix.

## 7. Exception flow spec

For exception requests (discount > `max_discount_pct_without_exception`):

- [ ] Required: structured submission (no Slack/email)
- [ ] Required: written justification
- [ ] Required: named approver chain (no role-only approvals)
- [ ] Required: compensating commitments per severity band (per `exception_router.COMPENSATING_LIBRARY`)
- [ ] Required: precedent-risk check across trailing 90 days
- [ ] Required: audit-trail JSON persisted to system of record (CPQ or equivalent)

Severity tiers (severity = `requested_discount` − `max_without_exception`):

| Severity range | Minimum compensating commitments |
|---|---|
| 0-5 pts over | multi-year term + annual prepay |
| 5-10 pts over | + named expansion path in writing |
| 10-20 pts over | + reference commitment + MSA tightening |
| 20+ pts over | + executive sponsor + co-marketing + kill-switch on expansion target |

## 8. Quarterly review trigger

| Check | Owner | Cadence |
|---|---|---|
| Re-pull current deals corpus; re-run `discount_matrix_builder.py` | Head of Deal Desk | Quarterly |
| Re-run `policy_linter.py` on current matrix | Head of Deal Desk | Quarterly |
| Review cells flagged `meets_target_nrr=false` | CFO + CRO | Quarterly |
| Review cells flagged `thin_data_flag=true` | Head of Deal Desk | Bi-quarterly |
| Review precedent-risk flags from `exception_router.py` | Head of Deal Desk + CRO | Quarterly |

---

## JSON skeletons

### `policy_intake.json` (feeds `discount_matrix_builder.py`)

```json
{
  "industry": "saas",
  "current_deals": [
    {
      "arr": 0,
      "discount_pct": 0,
      "term_months": 12,
      "payment_terms_days": 30,
      "strategic_value": "standard",
      "win_lost": "win",
      "nrr_12mo": 1.0
    }
  ],
  "target_constraints": {
    "min_margin_pct": 70.0,
    "max_discount_pct_without_exception": 35.0,
    "target_nrr": 1.15
  }
}
```

### `exception_request.json` (feeds `exception_router.py`)

```json
{
  "exception_request": {
    "deal_id": "",
    "requested_by": "",
    "deal_arr": 0,
    "requested_discount": 0,
    "term_months": 0,
    "payment_terms_days": 30,
    "justification": "",
    "strategic_value": "standard",
    "customer_threats": [],
    "submitted_at": ""
  },
  "policy_matrix": {
    "profile": "saas",
    "max_discount_pct_without_exception": 35.0,
    "approver_thresholds": [
      [15, "AE"], [25, "Sales Manager"], [35, "Director"], [50, "VP Sales"], [100.1, "CFO + CRO"]
    ]
  },
  "recent_exceptions": []
}
```

### `matrix.json` (output of `discount_matrix_builder.py`, input to `policy_linter.py`)

The linter expects the matrix shape emitted by the builder — `profile`, `constraints`, `cells[]` with the per-cell fields. Add the top-level boolean `strategic_value_definitions_supplied: true` once you've published the definitions from Section 6.

---

## 20-minute workflow

1. (~3 min) Fill Section 1 + Section 2 + Section 3.
2. (~6 min) Pull the deal corpus from CRM, format into `current_deals[]` JSON.
3. (~2 min) Fill Section 5 — get the three numbers from CFO + CRO.
4. (~5 min) Write Section 6 strategic-value definitions with concrete tests.
5. (~2 min) Confirm Section 7 exception flow with Head of Deal Desk.
6. (~2 min) Run the three scripts in order, lock the matrix, publish.
