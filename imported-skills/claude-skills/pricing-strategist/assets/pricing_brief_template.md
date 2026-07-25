# Pricing Strategy Brief

**Owner:** _______________  **Date:** _______________
**Time to fill out:** ≈ 20 minutes

Fill this brief out *before* running `pricing_model_picker.py`. The skill outputs are only
as good as the inputs. Be specific. If you don't know a field, write "unknown" — don't guess.

---

## 1. Product context

- **Product / feature being priced:** _______________
- **Customer-visible name:** _______________
- **One-line value prop:** _______________
- **Stage:** [ ] new launch  [ ] re-pricing  [ ] adding tier  [ ] expansion play

## 2. Customer context

- **Industry:** _______________ (e.g., "B2B SaaS — sales intelligence")
- **ICP (Ideal Customer Profile, 1 sentence):** _______________
- **Avg deal size today (annual contract value):** $_______________
- **Customer count today:** _______________
- **Geographic concentration:** _______________

## 3. Value drivers (rank top 3)

The customer outcome that pricing should track. Be specific — "saves time" is not a value
driver. "Reduces lead-research time by 6 hours/rep/week" is.

1. _______________
2. _______________
3. _______________

For each, can you measure it? [ ] yes  [ ] partly  [ ] no

## 4. Adoption curve

- [ ] Top-down enterprise sale (CIO/VP signs)
- [ ] Bottom-up / PLG (individual user adopts, expands)
- [ ] Hybrid (champion-led, exec-approved)
- [ ] Viral (referral loops within or across orgs)

## 5. Consumption pattern (assign 0.0 - 1.0 to each)

How does customer value scale with what they use?

- **Seat-based** (more users = more value): _______________
- **Usage-based** (more events / API calls / volume = more value): _______________
- **Value-based** (measurable customer outcome = more value): _______________
- **Hybrid** (multiple drivers, no single dominant): _______________

## 6. Competitive pricing landscape

List the 3-5 closest competitors and their pricing model:

| Competitor | Pricing model | Notable mechanics |
|---|---|---|
|   |   |   |
|   |   |   |
|   |   |   |

## 7. Strategic constraints

- **Margin floor (gross margin %):** _______________
- **Discount envelope (max % off list):** _______________
- **Sales motion (self-serve / inside / field):** _______________
- **Any contractual / regulatory pricing constraints?** _______________

## 8. Anti-goals

What pricing outcomes would be a *failure* even if NRR looks fine?

- _______________
- _______________

---

## JSON skeleton (for the script)

Copy this into a file (e.g., `brief.json`) and fill in. Then run:

```bash
python scripts/pricing_model_picker.py --input brief.json --profile saas --output markdown
```

```json
{
  "industry": "",
  "deal_size_avg": 0,
  "customer_count": 0,
  "value_drivers": [
    ""
  ],
  "adoption_curve": "",
  "consumption_pattern": {
    "seat-based": 0.0,
    "usage-based": 0.0,
    "value-based": 0.0,
    "hybrid": 0.0
  },
  "competitor_pricing_models": [
    ""
  ]
}
```

---

## After running the picker

1. Take the top 1-2 model recommendations into a 30-min review with Product + Finance.
2. If a model is selected, run a **Van Westendorp PSM survey** (≥ 30 respondents, preferably 100+).
3. Feed survey data to `wtp_analyzer.py` to get the Range of Acceptable Prices.
4. Run `packaging_designer.py` on your feature list to draft Good/Better/Best tiers.
5. Pressure-test in pricing committee. The skill output is one input, not the decision.
