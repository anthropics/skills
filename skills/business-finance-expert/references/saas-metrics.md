# SaaS Financial Metrics — Deep Dive

## Revenue Metrics

### ARR / MRR
- **MRR** (Monthly Recurring Revenue): Normalized monthly value of all active subscription contracts. Exclude one-time fees, professional services, and usage overages (unless recurring).
- **ARR** = MRR × 12. The standard unit for communicating with investors and boards at $1M+ scale.
- **ACV** (Annual Contract Value): Total annualized value of a contract. Useful for comparing deal sizes across different contract lengths.
- **TCV** (Total Contract Value): Total value over the full contract term. For a 3-year $100K/year deal, TCV = $300K but ACV = $100K.
- **ARR Bridge / Waterfall** (do this monthly):
  - Beginning ARR
  - + New ARR (new logos)
  - + Expansion ARR (upsells, cross-sells, seat additions)
  - − Contraction ARR (downgrades)
  - − Churned ARR (cancellations)
  - = Ending ARR
  - Net New ARR = New + Expansion − Contraction − Churn

### ARPU / ARPA
- **ARPU** (Average Revenue Per User): MRR / Total Active Users
- **ARPA** (Average Revenue Per Account): MRR / Total Active Accounts (more useful for B2B multi-seat)
- Track ARPA trend to assess pricing power and upsell effectiveness

---

## Retention Metrics

### Churn (Types)
- **Logo Churn Rate** (Customer Churn): # Customers Lost / Beginning # Customers. Measures customer count loss.
- **Revenue Churn Rate** (Gross Revenue Churn): ARR Lost to Cancellations / Beginning ARR × 100. Measures revenue loss from cancellations only — excludes expansions and contractions.
- **Net Revenue Churn**: (Churned ARR + Contracted ARR − Expanded ARR) / Beginning ARR × 100. Can be negative (good — means expansion outpaces churn).

### Gross Revenue Retention (GRR)
- GRR = (Beginning ARR − Churned ARR − Contracted ARR) / Beginning ARR × 100
- Measures how much revenue is retained from the existing base, excluding upsells
- **GRR Benchmarks**: Best-in-class: >90%; Good: 85–90%; Needs attention: <80%
- GRR is capped at 100% (cannot expand; expansion is captured in NRR)

### Net Revenue Retention (NRR) / Net Dollar Retention (NDR)
- **Formula**: NRR = (Beginning ARR + Expansion − Contraction − Churn) / Beginning ARR × 100
- Measured for a cohort of customers over 12 months
- NRR > 100%: existing customers alone would grow the business even with zero new customer acquisition
- **NRR Benchmarks**:
  - Median across all SaaS: ~102%
  - Median for public SaaS companies: ~114%
  - Best-in-class (top quartile): >120%
  - Investor threshold for premium valuation: >120%
- **Valuation impact**: Public SaaS companies with NRR >120% trade at ~9.3x EV/Revenue vs. ~3.1x for those below 100% (Software Equity Group). McKinsey found 21x vs. 9x EV/Revenue for >120% vs. <120% NRR companies. Each 10pp of NRR above 100% adds ~1–2x to EV/Revenue.

---

## Unit Economics

### Customer Acquisition Cost (CAC)
- **Fully-loaded CAC** = (Total S&M Spend) / (New Customers Acquired in Period)
- Includes: salaries + benefits + commissions + marketing spend + tools
- Always use fully-loaded — many teams understate CAC by excluding headcount costs
- **Blended CAC vs. Paid CAC**: Separate organic/SEO channels (low CAC) from paid channels (high CAC) to understand true channel economics

### Customer Lifetime Value (LTV)
- **LTV** = ARPA × Gross Margin % / Customer Churn Rate
- Alternative: LTV = (ARPA × Gross Margin %) / MRR Churn Rate (monthly churn basis)
- Example: $1,000 ARPA, 75% GM, 2% monthly churn → LTV = $1,000 × 0.75 / 0.02 = $37,500
- Use gross margin in LTV — not revenue — because LTV represents contribution after COGS

### LTV:CAC Ratio
- **Formula**: LTV / CAC
- **Benchmarks**:
  - Below 1:1 → burning money on every customer; unsustainable
  - 1:1–3:1 → marginal; likely requires improvement
  - 3:1 → minimum healthy threshold (widely cited industry standard)
  - 4:1+ → excellent unit economics
  - >6:1 → may be under-investing in growth (leaving money on table)
- **Segment by cohort**: SMB, Mid-Market, Enterprise will show dramatically different LTV:CAC ratios

### CAC Payback Period
- **Formula**: CAC / (ARPA × Gross Margin %) — expressed in months
- Tells you how many months of gross profit it takes to recover the cost of acquiring a customer
- **Benchmarks by ACV segment**:
  - SMB (<$15K ACV): 8–12 months (healthy)
  - Mid-Market ($15K–$100K ACV): 14–18 months
  - Enterprise (>$100K ACV): 18–24 months
  - Overall median across B2B SaaS: ~15–16 months
- Companies with <12 month payback period are considered highly capital efficient

---

## Efficiency Metrics

### Rule of 40
- **Definition**: ARR Growth Rate (%) + FCF Margin (%) ≥ 40
- Popularized by Brad Feld; validated by Bain & Company research
- Bain found companies consistently above 40 generate 2x higher valuations and outperform the S&P 500 by ~15%
- Use FCF margin as the profitability input (not EBITDA) for the most rigorous version
- **Benchmarks**: Top-quartile public SaaS companies score 40–60+; median is around 20–30
- **At scale**: as growth decelerates naturally, profitability must improve to maintain Rule of 40

### Rule of X (Bessemer Venture Partners)
- Evolution of Rule of 40 that weights growth more heavily than profitability
- **Formula**: (ARR Growth Rate × Multiplier) + FCF Margin %
- Growth multiplier ≈ 2.0–2.3x (as of 2024), reflecting compounding value of growth vs. linear value of margin
- Correlation with EV/Revenue: Rule of X (r=0.64) outperforms Rule of 40 (r=0.30)
- Example: 30% growth × 2.3 + 15% FCF margin = 84 Rule of X score

### Burn Multiple (Craft Ventures / David Sacks)
- **Formula**: Net Cash Burn / Net New ARR
- Measures how efficiently the company converts cash burn into ARR growth
- **Benchmarks**:
  - <1x: Exceptional (every $1 burned generates >$1 of new ARR)
  - 1x–1.5x: Great (capital-efficient growth)
  - 1.5x–2x: Good (acceptable for early stage)
  - 2x–3x: Concerning (requires explanation)
  - >3x: Burning capital inefficiently; investors will apply heavy scrutiny
- Bessemer's related "Efficiency Score" = NNARR / Burn (inverse of Burn Multiple)
- Median burn multiple improved from 2.5x (2021) to 1.8x (2024)

### Magic Number
- **Formula**: (Current Quarter ARR − Prior Quarter ARR) × 4 / Prior Quarter S&M Spend
- Measures how much ARR you generate for every dollar of S&M spend
- **Benchmarks**:
  - >1.0: Excellent — pour more into S&M; every $1 of S&M generates $1+ of ARR
  - 0.75–1.0: Good
  - 0.5–0.75: Moderate; optimize before scaling
  - <0.5: Inefficient; investigate before increasing S&M spend
- Useful for determining when to step on the growth accelerator vs. optimize

### SaaS Quick Ratio (Bessemer Venture Partners)
- **Formula**: (New MRR + Expansion MRR) / (Churned MRR + Contraction MRR)
- Created by Mamoon Hamid (Kleiner Perkins); popularized by Bessemer
- **Benchmarks**:
  - >4: Best-in-class (generate $4 of new/expansion revenue for every $1 lost) — Bessemer's top-performer threshold
  - 2–4: Good
  - <2: Concerning; churn is meaningfully offsetting growth

---

## Growth Metrics

### ARR Growth Rate
- YoY ARR Growth is the primary growth metric for investors
- **Stage benchmarks**:
  - Seed / pre-Series A: 3x+ ARR growth (triple, triple, double, double, double rule)
  - Series A ($1M–$5M ARR): >100% YoY
  - Series B ($5M–$20M ARR): 80–120% YoY
  - Series C ($20M–$50M ARR): 50–80% YoY
  - Growth stage ($50M–$100M ARR): 40–60% YoY
  - Pre-IPO ($100M+ ARR): 30–50% YoY (Rule of 40 applies most)

### T2D3 Framework (Triple, Triple, Double, Double, Double)
- Classic SaaS growth path to $100M ARR:
  - Year 1: $2M ARR → $6M (3x)
  - Year 2: $6M → $18M (3x)
  - Year 3: $18M → $36M (2x)
  - Year 4: $36M → $72M (2x)
  - Year 5: $72M → $144M (2x)

---

## Gross Margin Benchmarks (SaaS)
- Pure software SaaS (Datadog, Atlassian model): 80–85%
- SaaS with services component (Veeva, Guidewire): 65–75%
- Infrastructure SaaS (Snowflake, MongoDB): 70–75%
- Overall public SaaS median: 72–78%
- Companies above 80% gross margin trade at ~7.2x revenue vs. ~3.5x for those below 60%

**COGS components for SaaS:**
- Cloud hosting / infrastructure (AWS, GCP, Azure)
- Customer support headcount (often 4–8% of revenue)
- Third-party software embedded in product
- Professional services / implementation (if revenue-generating)
- Depreciation of capitalized software (ASC 350-40)

---

## Cohort Analysis
Track customers by acquisition cohort (month/quarter joined) to understand:
- Revenue retention curves — how fast does revenue decay?
- Expansion curves — do long-tenured customers expand above initial contract?
- Ideal customer profile validation — which segments show best NRR curves?

Best-in-class SaaS cohorts show expansion that more than offsets churn within 12–18 months (NRR > 120%).
