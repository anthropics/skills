# SaaS Pricing Canon

Curated, opinionated knowledge base for pricing model selection. This is the source material
behind `pricing_model_picker.py`'s scoring rules.

## Core principle

Pricing is a product decision, not a finance decision. The pricing model encodes how customers
experience value capture — get it wrong and every other GTM lever (sales, retention, expansion)
compounds the mistake.

---

## The five pricing models

### 1. Subscription seat-based

Customers pay per user, per period. Works when:
- Value scales linearly with user count
- Usage variance per seat is low
- Procurement prefers predictable line items
- Competitive set already trains the market on seat pricing

Failure modes: usage power-law (top 10% of users drive 80% of value) leaves money on the table;
"seat sprawl" makes customers hide users; expansion is gated on hiring, which is slow.

### 2. Usage-based (consumption)

Customers pay for what they consume — API calls, tokens, GB stored, messages sent. Works when:
- Value is tightly coupled to a measurable unit
- Usage variance across customers is high (power-law)
- Customer wants to start small and scale
- The metering infrastructure exists

Failure modes: bill-shock (variance scares procurement); cohort-NRR volatility; "cost of a query"
becomes a feature-velocity tax; revenue forecasting becomes hard.

### 3. Value-based

Price is anchored to the customer's economic outcome (revenue lift, cost saved, time recovered).
Works when:
- The value driver is measurable and attributable
- Customer count is small enough to calibrate per-account
- Deal size is large enough to justify the sales motion
- ROI proof is part of the product (not a slide)

Failure modes: requires instrumented ROI per customer; doesn't scale operationally beyond ~50-200
accounts without specialization; collapses to "whatever they'll pay" when value isn't measurable.

### 4. Freemium

Free tier acquires users, paid tiers monetize. Works when:
- Adoption is bottom-up / viral / PLG
- Free-tier cost-to-serve is < 5% of paid LTV
- There is a natural upgrade trigger inside the free experience
- Sales motion is self-serve or low-touch

Failure modes: enterprise sale + freemium dilutes positioning; free-tier costs balloon faster than
conversion; the "free forever for 10 users" cliff trains customers to game it.

### 5. Hybrid

Combinations — seat + usage overage, platform + per-event, base + value uplift. Works when:
- Multiple value drivers exist (seats AND usage)
- Customer segments split on dominant driver
- Deal sizes are large enough to absorb pricing-page complexity

Failure modes: cognitive load on the prospect; CS overhead in tier-to-tier moves; invoice disputes;
hybrid sometimes hides "we couldn't decide" — which customers detect.

---

## Authoritative sources

1. **David Skok — For Entrepreneurs**.
   "SaaS Metrics 2.0" + "Unit Economics" series. The canonical playbook on CAC, LTV, and how
   pricing model interacts with both. https://www.forentrepreneurs.com/saas-metrics-2/

2. **Tomasz Tunguz — Theory Ventures blog**.
   Years of empirical posts on Cloud 100 pricing patterns, hybrid-pricing adoption curves,
   usage-based unit economics. https://tomtunguz.com/

3. **Patrick Campbell — ProfitWell / Paddle research**.
   The largest body of public SaaS pricing data. Key findings: prospects who see clear value
   metrics convert 2x; freemium converts 2-5% on average; bad packaging is the #1 churn cause.
   https://www.paddle.com/resources

4. **Madhavan Ramanujam — Monetizing Innovation (Wiley, 2016)**.
   Simon-Kucher partner. The "9 Pricing Mistakes" frame: feature shock, minivation, hidden gem,
   undead. Establishes the discipline that pricing comes before product, not after.

5. **Bessemer Venture Partners — State of the Cloud + Memos**.
   Annual benchmarks: Rule of 40, NRR by ACV band, pricing-model mix in Cloud 100. The
   reference for "what good looks like" in SaaS.
   https://www.bvp.com/atlas

6. **Ron Shevlin — Cornerstone Advisors / Forbes columns**.
   Pricing psychology applied to financial services SaaS — anchoring, decoy effect, charm
   pricing's diminishing returns in B2B.

7. **Stanford GSB pricing research (Bertini, Gourville, Anderson)**.
   Academic foundation on price-quality signaling, reference price formation, and the
   penny-gap problem (the $0 → $0.01 conversion cliff). See Bertini & Gourville HBR 2012,
   "Pricing to Create Shared Value."

8. **Kyle Poyar — OpenView / Growth Unhinged**.
   Practitioner depth on PLG monetization, packaging redesigns, and the shift from seat to
   hybrid pricing in 2020-2025 cohort. https://www.growthunhinged.com/

## How this skill uses the canon

- `pricing_model_picker.py` weights consumption-pattern signals per the Skok/Tunguz/Campbell
  empirical priors.
- Industry profiles (`saas`, `api`, `ai-tools`, `enterprise-software`, `marketplace`) encode
  default biases observed in BVP and ProfitWell cohort data.
- The "value-based requires measurable driver" gate comes directly from Ramanujam's "minivation"
  failure mode.
- Freemium scoring penalties for high-ACV deals come from Poyar's documented PLG-to-enterprise
  transition patterns.
