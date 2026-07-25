# Partnership Intake Template

**Owner:** _______________  **Date:** _______________
**Time to fill out:** ≈ 20 minutes
**Prospective partner name:** _______________

Fill this template out honestly BEFORE running `partner_tier_classifier.py`. The skill
outputs are only as good as the inputs. If you cannot honestly answer a field, write
"unknown" — do not guess. If multiple fields are "unknown," the partner has not
demonstrated enough substance to evaluate. Pause the process and go back to them.

---

## 1. Partner identity

- **Partner legal name:** _______________
- **Partner_type** (pick one): [ ] referral  [ ] reseller  [ ] oem  [ ] si_consultant
  [ ] technology  [ ] strategic_alliance
- **Who introduced them?** _______________
- **Why are they approaching us NOW?** _______________
  (If the honest answer is "they want preferential discount," classify as REFERRAL
  and proceed accordingly. Do not advance to RESELLER+.)

## 2. Independent demand evidence

This is the most important section. STRATEGIC and OEM tiers have HARD floors here.

- **Named accounts they have sold to in the last 12 months, at companies you would
  also target:**
  1. _______________
  2. _______________
  3. _______________
  4. _______________
  5. _______________

- **`named_accounts_sourced_count` (count of verifiable, reference-able named
  accounts):** _______________

- **Of their total customer base, what % are end customers (companies they sold
  directly to and own the relationship), vs intermediaries / sub-partners?**

  `end_customer_relationships_pct` (0-100): _______________

- **Sales team size — how many people on their team actively sell?**

  `sales_team_size`: _______________

  Note: "everyone is a salesperson at our company" is not an answer. Count the people
  whose comp plan includes quota.

## 3. Strategic value (which of these does this partner change?)

- **`geo_coverage`** — geographies they reach that we don't / cover poorly:
  _______________

- **`product_complement`** — what they bring that completes the customer outcome
  (whole-product reasoning per Geoffrey Moore):
  _______________

- **`brand_lift`** — does their brand carry credibility we lack?
  [ ] strong  [ ] mid  [ ] none

- **`channel_economics_advantage`** — lower CAC, faster sales cycle, better retention
  in a segment we struggle with?
  _______________

## 4. Commitments they have offered

Be precise. Vague commitments are not commitments.

- **`joint_marketing_spend`** (USD per year): _______________

- **`dedicated_resources`** — named individuals on their team dedicated to this
  partnership (not "we'll figure it out"):
  count: _______________
  names: _______________

- **`certification_completion`** — will their team complete our certification
  curriculum?
  [ ] yes, scheduled  [ ] willing but not scheduled  [ ] no

- **`sales_targets`** — specific named pipeline and closed-won targets, with a time
  horizon:
  _______________
  (Example: "12 closed-won deals over 12 months, with named target accounts
   identified in TAL.")

## 5. What they want from US

- **Revshare ask:** _______________
- **Exclusivity ask:** _______________ (territory / segment / vertical / none)
- **MDF ask:** _______________
- **Engineering integration ask:** _______________
- **Anything unusual:** _______________

## 6. Honest red-flag check

If any of these are true, the partner is a discount hunter, not a partner. Sign at
REFERRAL or do not sign at all.

- [ ] They cannot name 5 customers they have sold to in the last 12 months
- [ ] Their commercial ask is precise; their joint-value-prop ask is vague
- [ ] They want exclusive territory at signing with no performance condition
- [ ] They claim "strategic alliance" but have no exec sponsor on their side
- [ ] They are pushing for fast signing ("we have a deal we need to close this week")

---

## JSON skeleton for `partner_tier_classifier.py --input`

```json
{
  "partner_name": "",
  "partner_type": "",
  "independent_demand_evidence": {
    "named_accounts_sourced_count": 0,
    "end_customer_relationships_pct": 0,
    "sales_team_size": 0
  },
  "strategic_value": {
    "geo_coverage": "",
    "product_complement": "",
    "brand_lift": "",
    "channel_economics_advantage": ""
  },
  "commitments": {
    "joint_marketing_spend": 0,
    "dedicated_resources": 0,
    "certification_completion": false,
    "sales_targets": ""
  }
}
```

Save as `partner.json`, then run:

```
python scripts/partner_tier_classifier.py --input partner.json --profile saas --output markdown
```

Then proceed to `joint_gtm_planner.py` and `revshare_modeler.py` only if the assigned
tier is RESELLER or higher AND your partnership committee has agreed to move forward.
