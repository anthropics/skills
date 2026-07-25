# Deal Intake — Deal Desk Review

**Time to fill out: ~20 minutes.** This is the single source of truth for the deal. Re-pricings or term changes create a *new* intake — do not edit in place.

The structured fields at the bottom (the JSON blocks) feed directly into the three scripts:

- `deal_scorer.py` → consumes the **Deal Scorecard JSON**
- `discount_approval_router.py` → consumes the **Discount Routing JSON**
- `terms_redliner.py` → consumes the **Terms JSON**

---

## 1. Deal identity

| Field | Value |
|---|---|
| Deal ID | `ACME-2026-Q2-117` |
| Customer name | |
| AE / deal owner | |
| Sales engineer (if any) | |
| Date submitted | |
| Target close date | |
| Industry / segment | |

## 2. Commercial summary

| Field | Value |
|---|---|
| ARR (annual recurring revenue, $) | |
| Total contract value (TCV, $) | |
| Term (months) | |
| List price (TCV before discount, $) | |
| Discount (%) | |
| Customer tier | `enterprise` / `mid` / `smb` |
| Industry profile | `saas` / `enterprise-software` / `services` / `marketplace` |

## 3. Margin

| Field | Value |
|---|---|
| Product gross margin (%) | |
| Implementation / onboarding cost ($) | |
| Custom dev / SOW work in scope? | `yes` / `no` |
| If yes — services margin (%) | |

## 4. Strategic flags

Check each that applies. Each flag justifies *some* commercial flexibility but the discount scorer requires at least one for above-band discounts.

- [ ] **Logo** — reference-quality customer name; shortens future sales cycles.
- [ ] **Reference** — customer has agreed (in writing) to act as a reference / case study.
- [ ] **Expansion** — committed expansion plan in the next 12 months (named, quantified).
- [ ] **Renewal** — this is a renewal with multi-year extension.

## 5. Payment shape

| Field | Value |
|---|---|
| Payment terms (days from invoice) | |
| Billing frequency | `annual upfront` / `quarterly` / `monthly` |
| Multi-year discount applied? | `yes` / `no` |
| Up-front payment offered for discount? | `yes` / `no` |

## 6. Terms — customer-flagged redlines

List each clause the customer has flagged or modified. The scripts treat each entry as a risk signal.

1. ...
2. ...
3. ...

## 7. Structured terms (for `terms_redliner.py`)

Fill in the known structured fields:

| Term | Value |
|---|---|
| Auto-renew? | `true` / `false` |
| Auto-renew notice days | |
| Indemnity cap (multiple of fees, or `null` if uncapped) | |
| Liability cap (multiple of annual fees) | |
| DPA present? | `true` / `false` |
| EU personal data involved? | `true` / `false` |
| IP assignment | `vendor` / `customer` / `ambiguous` / `perpetual_license_back` |
| MFN clause present? | `true` / `false` |
| Exclusivity clause present? | `true` / `false` |
| Exclusivity compensated? | `true` / `false` |
| Non-solicit term (years) | |
| Governing law | |
| Vendor home jurisdiction | |

---

## 8. JSON skeletons — paste these into files for the scripts

### Deal Scorecard JSON (`deal.json`)

```json
{
  "deal_id": "ACME-2026-Q2-117",
  "customer_name": "Acme Corp",
  "arr": 240000,
  "term_months": 24,
  "discount_pct": 28.0,
  "payment_terms_days": 60,
  "list_price": 333333,
  "gross_margin_pct": 78.0,
  "customer_tier": "enterprise",
  "strategic_value": {
    "logo": true,
    "reference": false,
    "expansion": true,
    "renewal": false
  },
  "term_redlines": [
    "uncapped indemnity",
    "MFN pricing"
  ]
}
```

Run:

```bash
python3 scripts/deal_scorer.py --input deal.json --profile saas
```

### Discount Routing JSON (`discount.json`)

```json
{
  "deal_id": "ACME-2026-Q2-117",
  "discount_pct": 28.0,
  "deal_size_arr": 240000,
  "customer_tier": "enterprise",
  "policy_thresholds": null
}
```

Run:

```bash
python3 scripts/discount_approval_router.py --input discount.json --profile saas
```

### Terms JSON (`deal_terms.json`)

```json
{
  "deal_id": "ACME-2026-Q2-117",
  "payment_terms_days": 60,
  "auto_renew": true,
  "auto_renew_notice_days": 90,
  "indemnity_cap": null,
  "liability_cap": 1.0,
  "dpa_present": false,
  "eu_data_involved": true,
  "ip_assignment": "ambiguous",
  "mfn_clause_present": true,
  "exclusivity_clause_present": false,
  "exclusivity_compensated": false,
  "non_solicit_years": 3,
  "governing_law": "Delaware",
  "vendor_home_jurisdiction": "Delaware"
}
```

Run:

```bash
python3 scripts/terms_redliner.py --input deal_terms.json
```

---

## 9. Reviewer checklist

Before submitting the intake to the deal desk:

- [ ] All commercial fields populated (no blanks in section 2).
- [ ] Strategic flags reflect *committed*, not hoped-for, value.
- [ ] All customer-flagged redlines listed in section 6.
- [ ] Structured terms in section 7 match the actual marked-up contract.
- [ ] JSON skeletons (section 8) saved to files.

The deal-desk packet that comes back will name the approver(s) who must sign. **The skill never approves the deal itself.**
