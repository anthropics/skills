# Spend Intake Template

20-minute fill-out for the annual SaaS audit / category-level spend review. Output is a JSON list you can paste into `scripts/spend_categorizer.py` and `scripts/supplier_consolidation.py`.

---

## Step 1 — Gather sources (5 minutes)

Pull line-item spend from one or more of:

- AP / accounting system export (Bill.com, Ramp, NetSuite, QuickBooks).
- SaaS-management platform export (Productiv, Zylo, Vendr, Tropic, BetterCloud).
- Corporate-card export with merchant + memo.
- Expense reimbursement export (Expensify, Concur, Navan).

Aim for the top 100-200 line items by spend. The Pareto holds — the top 20% will give you 80% of the answer.

---

## Step 2 — Fill out the spend JSON (15 minutes)

For each line item, populate the schema below. Skip prior-year fields if you don't have them — the tool degrades gracefully.

```json
[
  {
    "supplier": "Datadog",
    "description": "Monitoring + APM enterprise tier",
    "category_hint": "monitoring",
    "annual_spend": 180000,
    "frequency": "annual",
    "currency": "USD",
    "prior_year_spend": 120000
  },
  {
    "supplier": "AWS",
    "description": "EC2 + S3 + RDS production infrastructure",
    "category_hint": "cloud infrastructure",
    "annual_spend": 720000,
    "frequency": "monthly",
    "currency": "USD",
    "prior_year_spend": 480000
  },
  {
    "supplier": "Outside Counsel - Fenwick",
    "description": "legal services - contracts, employment, IP",
    "category_hint": "legal",
    "annual_spend": 95000,
    "frequency": "as-billed",
    "currency": "USD",
    "prior_year_spend": 60000
  }
]
```

### Field guide

| Field | Required? | Notes |
|---|---|---|
| `supplier` | yes | The legal entity you pay (not the brand). |
| `description` | yes | What you bought, in your words. **This drives categorization** — be specific. "Workday HR" vs "Workday Finance" categorize differently. |
| `category_hint` | optional but recommended | A short keyword (monitoring, expense, crm, legal, etc.). Helps the categorizer when the description is ambiguous. |
| `annual_spend` | yes | Annualized total (multiply monthly × 12). |
| `frequency` | optional | `annual`, `monthly`, `quarterly`, `as-billed` — informational only, doesn't change categorization. |
| `currency` | optional | Default USD. Convert before input if mixed-currency. |
| `prior_year_spend` | optional | Enables YoY growth analysis. Set to 0 for new-this-year subscriptions. |

---

## Step 3 — Run the categorizer

```bash
python scripts/spend_categorizer.py \
  --input spend.json \
  --profile tech-startup \
  --output categorized.md
```

Profiles: `tech-startup`, `scaleup`, `enterprise`, `services`, `manufacturing`.

---

## Step 4 — Build the supplier-criticality JSON for consolidation

Take the same suppliers, add criticality and switching cost. The supplier-consolidation tool needs this:

```json
[
  {
    "name": "Datadog",
    "category": "Monitoring / Observability",
    "annual_spend": 180000,
    "criticality": "tier-2",
    "contract_term_months": 12,
    "integration_count_with_other_systems": 12,
    "switching_cost_estimate": 80000,
    "renewal_date": "2026-09-15",
    "break_glass_documented": false
  },
  {
    "name": "AWS",
    "category": "Cloud Infrastructure",
    "annual_spend": 720000,
    "criticality": "tier-1",
    "contract_term_months": 36,
    "integration_count_with_other_systems": 40,
    "switching_cost_estimate": 600000,
    "renewal_date": "2027-03-31",
    "break_glass_documented": true
  }
]
```

### Criticality definitions (decide before running, don't let the tool infer)

- **tier-1** — revenue-blocking if the supplier disappears for 24h+. Identity providers, payment processors, primary cloud, primary CRM. Tier-1 should be a short list (typically 5-15 suppliers).
- **tier-2** — important but a workaround exists. Most SaaS lands here.
- **tier-3** — nice-to-have. Long-tail SaaS, productivity utilities.

### Break-glass flag

`break_glass_documented: true` means you have a written 72-hour contingency plan for what happens if this supplier disappears tomorrow. The tool **refuses to recommend tier-1 consolidation** if any cluster member has this flag false.

---

## Step 5 — Run consolidation

```bash
python scripts/supplier_consolidation.py \
  --input suppliers.json \
  --profile tech-startup \
  --output consolidation_plan.md
```

---

## Optional: purchasing-cycle data

If you have PO timestamp data, the cycle analyzer surfaces bottleneck categories:

```json
[
  {
    "category": "Outside Counsel",
    "request_date": "2026-01-05",
    "approval_date": "2026-02-15",
    "po_issued_date": "2026-02-28",
    "goods_received_date": "2026-02-28",
    "payment_date": "2026-03-30",
    "approver_hops": 4
  }
]
```

Run with:

```bash
python scripts/purchasing_cycle_analyzer.py \
  --input pos.json \
  --output cycle.md
```

---

## Quick sanity checks before you run

- [ ] Top 10 line items cover ≥ 50% of total spend (Pareto sanity check)
- [ ] Each line item has a non-empty `description` (drives categorization quality)
- [ ] Tier-1 suppliers are explicitly marked (don't let the tool guess)
- [ ] Switching-cost estimates exist for any supplier you might consolidate
- [ ] Renewal dates are populated for at least the top 20 contracts (drives renewal-cluster analysis)
