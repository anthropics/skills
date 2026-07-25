# RFP Intake Template

Fill this in BEFORE running `scripts/response_drafter.py` and `scripts/winrate_predictor.py`. Save as `rfp_intake.json` — the JSON skeleton at the bottom of this file is the canonical input format.

## Step 1 — Deal context

| Field | Value | Notes |
|---|---|---|
| Buyer organization | | |
| RFP title / ID | | |
| Submission deadline | | Date format YYYY-MM-DD |
| Estimated deal size (ACV / TCV) | | |
| Deal size vs. our average | below / at / above | Above-average deals attract more competitors |
| Incumbent | name or "none" | |
| Incumbent strength | none / weak / strong | Strong = 3+ years, no displacement event |
| Relationship strength | cold / warm / champion | Champion = internal advocate willing to push for us |
| Champion name + role | | If relationship_strength = "warm" or "champion" |
| Late entry? | yes / no | "Yes" if we entered AFTER the RFP issued |
| Decision-criteria alignment | 0-100% | How well our strengths match what the buyer says they're scoring on |
| Competitor count | integer | Best estimate; ask the buyer if you can |
| Industry profile | saas / enterprise-software / services / government / healthcare | Tunes `winrate_predictor.py` |

## Step 2 — Proof-point library

For every proof point your team can produce, fill in a row. Verifiable source is **mandatory** — if you can't name where the evaluator could verify it, the proof point doesn't qualify as STRONG.

| Name | Type | Tags (match against requirement text) | Verifiable source |
|---|---|---|---|
| SOC 2 Type II report (2026) | cert | soc, 2, type, ii, certification | trust.example.com/soc2-2026.pdf |
| 24/7 SOC staffing attestation | technical_attestation | soc, 24/7, coverage, on-call, rotation | SecOps runbook v3.2 |
| ... | ... | ... | ... |

**Proof-point types:**
- `case_study` — full customer story with quantified outcome
- `cert` — third-party certification
- `customer_quote` — attributed, approved customer quote
- `technical_attestation` — internal but verifiable (runbook, architecture doc)
- `benchmark` — quantified peer comparison (Gartner, Forrester, internal)

## Step 3 — Win-themes (3-5)

Shipley discipline: each theme must thread through ≥2 requirements. Themes appearing once are decorative.

1. **Theme:** _________
   **Threads through which requirement IDs:** _________
2. **Theme:** _________
3. **Theme:** _________
4. **Theme:** _________
5. **Theme:** _________

## Step 4 — Bid/no-bid threshold (set BEFORE seeing the RFP)

Pre-commit your threshold to avoid post-hoc rationalization:

- [ ] Winrate estimate ≥ ___ %
- [ ] STRONG match ≥ ___ % on MANDATORY requirements
- [ ] Named champion at buyer org
- [ ] MANDATORY GAP count ≤ ___
- [ ] Industry profile permits (e.g., do we no-bid government RFPs by default?)

## JSON skeleton — for `response_drafter.py --input`

```json
{
  "rfp_requirements_path": "parsed.json",
  "proof_points_library": [
    {
      "name": "SOC 2 Type II report (2026)",
      "type": "cert",
      "requirement_match_tags": ["soc", "2", "type", "ii", "certification"],
      "verifiable_source": "https://trust.example.com/soc2-2026.pdf"
    },
    {
      "name": "AWS/GCP/Azure logging case study (Globex)",
      "type": "case_study",
      "requirement_match_tags": ["aws", "gcp", "azure", "logging", "integrate"],
      "verifiable_source": "globex-cs-2025.pdf"
    }
  ],
  "win_themes": [
    "operational simplicity at scale",
    "financial-services regulatory depth",
    "MTTD leadership vs Gartner peer cohort"
  ]
}
```

## JSON skeleton — for `winrate_predictor.py --input`

```json
{
  "requirement_fit_pct_strong": 60.0,
  "requirement_fit_pct_partial": 25.0,
  "requirement_fit_pct_gap": 15.0,
  "incumbent_advantage": "weak",
  "relationship_strength": "warm",
  "decision_criteria_alignment_pct": 75.0,
  "late_entry": false,
  "competitor_count": 3,
  "deal_size_vs_avg": "at"
}
```

## Running the pipeline

```bash
# 1. Parse the RFP
python scripts/rfp_parser.py --input rfp.md --output json > parsed.json

# 2. Build the proof-point matrix + GAP audit + win-theme report
python scripts/response_drafter.py --input rfp_intake.json --output markdown > matrix.md

# 3. Compute fit % from the matrix, fill into deal_context.json, then:
python scripts/winrate_predictor.py --input deal_context.json --profile enterprise-software --output markdown

# 4. Take parsed RFP + matrix + winrate into the go/no-go review.
```

## Hard rule reminder

**Never invent claims for GAP requirements.** Surface them. Leadership decides: close the gap, partner-bid, or no-bid.
