# RevOps Metrics Guide

Complete reference for Revenue Operations metrics hierarchy, definitions, formulas, interpretation guidelines, and common mistakes.

---

## Metrics Hierarchy

Revenue Operations metrics are organized in a hierarchy from leading indicators (pipeline activity) through lagging indicators (efficiency outcomes):

```
Level 1: Activity Metrics (Leading)
  ├── Pipeline created ($, #)
  ├── Meetings booked
  ├── Proposals sent
  └── Demo completion rate

Level 2: Pipeline Metrics (Mid-funnel)
  ├── Pipeline coverage ratio
  ├── Stage conversion rates
  ├── Sales velocity
  ├── Deal aging
  └── Pipeline hygiene score

Level 3: Revenue Metrics (Outcomes)
  ├── Bookings (new, expansion, renewal)
  ├── Revenue (ARR, MRR, TCV)
  ├── Win rate
  └── Average deal size

Level 4: Efficiency Metrics (Unit Economics)
  ├── Magic Number
  ├── LTV:CAC Ratio
  ├── CAC Payback Period
  ├── Burn Multiple
  ├── Rule of 40
  └── Net Dollar Retention

Level 5: Strategic Metrics (Board-Level)
  ├── Revenue per employee
  ├── Gross margin trend
  ├── NRR cohort analysis
  └── Customer health score
```

---

## Core Metric Definitions

### Pipeline Coverage Ratio

**Formula:** Total Weighted Pipeline / Quota Target

**What it measures:** Whether there is sufficient pipeline to meet revenue targets.

**Interpretation:**
- 4x+: Strong coverage, selective deal pursuit possible
- 3-4x: Healthy coverage, standard operations
- 2-3x: At risk, accelerate pipeline generation
- <2x: Critical, immediate pipeline intervention needed

**Common Mistakes:**
- Including closed-won deals in the pipeline total
- Not weighting by stage probability
- Using annual quota against quarterly pipeline
- Ignoring deal quality in favor of quantity

**Best Practice:** Measure coverage ratio weekly. Track by quarter to identify seasonal gaps early.

---

### Stage Conversion Rates

**Formula:** # Deals advancing to Stage N+1 / # Deals entering Stage N

**What it measures:** Efficiency of progression through each pipeline stage.

**Typical SaaS Conversion Benchmarks:**
| Stage Transition | Median Rate | Top Quartile |
|-----------------|-------------|--------------|
| Lead to Qualification | 15-25% | 30%+ |
| Qualification to Proposal | 40-50% | 60%+ |
| Proposal to Negotiation | 50-60% | 70%+ |
| Negotiation to Close | 60-70% | 80%+ |
| Overall Win Rate | 15-25% | 30%+ |

**Common Mistakes:**
- Not standardizing stage exit criteria (subjective stages)
- Comparing conversion rates across different sales motions (PLG vs enterprise)
- Ignoring stage skipping (deals that jump stages inflate later conversion rates)
- Not segmenting by deal size or segment

---

### Sales Velocity

**Formula:** (# Opportunities x Avg Deal Size x Win Rate) / Avg Sales Cycle Days

**What it measures:** The rate at which the pipeline generates revenue, measured as revenue per day.

**Components:**
1. **# Opportunities** -- Volume of qualified deals in pipeline
2. **Avg Deal Size** -- Average contract value of won deals
3. **Win Rate** -- Percentage of deals that close
4. **Avg Sales Cycle** -- Days from opportunity creation to close

**Optimization levers:**
- Increase opportunity volume (marketing/SDR investment)
- Increase deal size (pricing, packaging, upsell)
- Increase win rate (sales enablement, competitive positioning)
- Decrease cycle length (champion building, MEDDPICC adherence)

**Common Mistakes:**
- Using all pipeline deals instead of qualified opportunities
- Not normalizing for segment (SMB velocity vs Enterprise velocity)
- Conflating calendar time with active selling time
- Ignoring velocity trend in favor of absolute number

---

### MAPE (Mean Absolute Percentage Error)

**Formula:** mean(|Actual - Forecast| / |Actual|) x 100

**What it measures:** Average forecast error magnitude as a percentage.

**Interpretation:**
| MAPE | Rating | Action |
|------|--------|--------|
| <10% | Excellent | Maintain current methodology |
| 10-15% | Good | Minor calibration adjustments |
| 15-25% | Fair | Methodology review needed |
| >25% | Poor | Fundamental process overhaul |

**Common Mistakes:**
- Using forecast vs. target instead of forecast vs. actual
- Not distinguishing between bias (systematic) and variance (random)
- Measuring only at the aggregate level (masks individual rep errors)
- Comparing MAPE across different time horizons (monthly vs quarterly)

---

### Forecast Bias

**Formula:** mean(Forecast - Actual) / mean(Actual) x 100

**What it measures:** Systematic tendency to over-forecast or under-forecast.

**Types:**
- **Positive bias (over-forecasting):** Forecast consistently exceeds actual. Often indicates optimistic deal assessment, insufficient qualification, or sandbagging reversal.
- **Negative bias (under-forecasting):** Actual consistently exceeds forecast. Often indicates conservative call culture, late-stage deals arriving unexpectedly, or poor pipeline visibility.

**Healthy Range:** Bias within +/- 5% of actual is considered well-calibrated.

---

### Magic Number

**Formula:** Net New ARR / Prior Period S&M Spend

**What it measures:** Efficiency of sales & marketing spend in generating new revenue.

**Interpretation:**
- >1.0: Extremely efficient, consider increasing GTM investment
- 0.75-1.0: Healthy efficiency, optimize and scale
- 0.50-0.75: Acceptable, focus on channel/spend optimization
- <0.50: Inefficient, audit spend allocation and productivity

**Common Mistakes:**
- Using total revenue instead of net new ARR
- Including expansion ARR (Magic Number measures new logo efficiency)
- Using current period spend instead of prior period (lag effect)
- Not separating sales spend from marketing spend for diagnostics

---

### LTV:CAC Ratio

**Formula:** Customer Lifetime Value / Customer Acquisition Cost

**Where:**
- LTV = (ARPA x Gross Margin) / Churn Rate
- ARPA = Average Revenue Per Account (annualized)
- CAC = Total S&M Spend / New Customers Acquired

**Target:** >3:1 is healthy; >5:1 may indicate under-investment in growth

**Common Mistakes:**
- Using revenue instead of gross-margin-weighted revenue in LTV
- Not including all acquisition costs (SDR, marketing, sales engineering)
- Using blended churn instead of cohort-specific churn
- Comparing across segments without normalizing (enterprise LTV:CAC is naturally higher)

---

### CAC Payback Period

**Formula:** CAC / (ARPA_monthly x Gross Margin)

**What it measures:** Months to recover the cost of acquiring a customer.

**Interpretation:**
- <12 months: Excellent capital efficiency
- 12-18 months: Healthy, especially for mid-market/enterprise
- 18-24 months: Acceptable for enterprise, concerning for SMB
- >24 months: Capital-intensive, needs optimization

**Common Mistakes:**
- Using revenue instead of gross-margin contribution
- Ignoring expansion revenue in payback calculation (conservative approach)
- Comparing SMB payback to enterprise payback without context

---

### Burn Multiple

**Formula:** Net Burn / Net New ARR

**What it measures:** How much cash is consumed for each dollar of new ARR.

**Interpretation (David Sacks framework):**
- <1.0x: Amazing -- hyper-efficient growth
- 1.0-1.5x: Great -- strong capital efficiency
- 1.5-2.0x: Good -- healthy burn rate
- 2.0-3.0x: Suspect -- needs attention
- >3.0x: Bad -- unsustainable without course correction

**Common Mistakes:**
- Using gross burn instead of net burn
- Not annualizing ARR when using quarterly burn
- Ignoring the denominator quality (all new ARR is not equal)

---

### Rule of 40

**Formula:** Revenue Growth Rate (%) + Free Cash Flow Margin (%)

**What it measures:** Balance between growth and profitability.

**Interpretation:**
- >60%: Elite SaaS company
- 40-60%: Strong performance
- 20-40%: Acceptable, optimize one dimension
- <20%: Needs significant improvement

**Common Mistakes:**
- Using EBITDA margin instead of FCF margin
- Comparing early-stage (growth-heavy) with late-stage (margin-heavy)
- Not considering the composition (80% growth + -40% margin vs 30% + 10%)

---

### Net Dollar Retention (NDR)

**Formula:** (Beginning ARR + Expansion - Contraction - Churn) / Beginning ARR x 100

**What it measures:** Revenue retention and expansion from existing customers.

**Interpretation:**
- >130%: World-class expansion (Snowflake, Datadog)
- 120-130%: Excellent land-and-expand
- 110-120%: Strong retention with moderate expansion
- 100-110%: Stable base, limited expansion
- <100%: Net revenue contraction -- critical concern

**Common Mistakes:**
- Including new logos in the calculation
- Not normalizing for cohort age (newer cohorts expand differently)
- Confusing gross retention with net retention
- Using logo retention as a proxy for dollar retention

---

## Metric Interdependencies

Understanding how metrics relate prevents conflicting optimizations:

1. **Magic Number and LTV:CAC** -- Both use S&M spend but measure different horizons. Magic Number is period-specific; LTV:CAC is lifetime.

2. **Burn Multiple and Rule of 40** -- Both measure efficiency but from different angles. Burn Multiple is cash-focused; Rule of 40 balances growth with profitability.

3. **Pipeline Coverage and Sales Velocity** -- High coverage with low velocity means pipeline is stagnating. Both must be healthy.

4. **NDR and LTV** -- NDR directly impacts LTV. Improving NDR is the highest-leverage way to improve LTV:CAC.

5. **Win Rate and Deal Size** -- Often inversely correlated. Moving upmarket increases deal size but may reduce win rate.

---

## Measurement Cadence

| Metric | Cadence | Owner |
|--------|---------|-------|
| Pipeline Coverage | Weekly | Sales Leadership |
| Stage Conversion | Bi-weekly | Sales Ops |
| Sales Velocity | Monthly | RevOps |
| Forecast Accuracy (MAPE) | Monthly/Quarterly | RevOps |
| Magic Number | Quarterly | CRO/CFO |
| LTV:CAC | Quarterly | Finance/RevOps |
| CAC Payback | Quarterly | Finance |
| Burn Multiple | Quarterly | CFO |
| Rule of 40 | Quarterly/Annual | CEO/Board |
| NDR | Quarterly | CS/RevOps |
