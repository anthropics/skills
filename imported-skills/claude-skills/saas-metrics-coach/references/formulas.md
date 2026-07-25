# SaaS Metric Formulas

Complete reference with worked examples for all metrics calculated by the SaaS Metrics Coach.

## ARR (Annual Recurring Revenue)
```
ARR = MRR × 12
```

**Example:**
- Current MRR: $50,000
- ARR = $50,000 × 12 = **$600,000**

**When to use:** Quick snapshot of annualized revenue run rate. Not the same as actual annual revenue if you have seasonality or one-time fees.

## MoM MRR Growth Rate
```
MoM Growth % = ((MRR_now - MRR_last) / MRR_last) × 100
```

**Example:**
- Current MRR: $50,000
- Last month MRR: $45,000
- Growth = (($50,000 - $45,000) / $45,000) × 100 = **11.1%**

**Interpretation:**
- Negative = losing revenue
- 0-5% = slow growth (concerning for early stage)
- 5-15% = healthy growth
- >15% = strong growth (early stage)

## Monthly Churn Rate
```
Churn % = (Customers lost / Customers at start of month) × 100
```

**Example:**
- Customers at start of month: 100
- Customers lost during month: 5
- Churn = (5 / 100) × 100 = **5%**

**Annualized impact:** 5% monthly = ~46% annual churn (compounding effect)

**Critical context:** Churn tolerance varies by segment:
- Enterprise: >3% is critical
- SMB: >8% is critical
- Always confirm segment before judging severity

## ARPA (Avg Revenue Per Account)
```
ARPA = MRR / Total active customers
```

## CAC (Customer Acquisition Cost)
```
CAC = Total Sales & Marketing spend / New customers acquired
```
Example: $20k spend / 10 customers → CAC $2,000

## LTV (Customer Lifetime Value)
```
LTV = (ARPA / Monthly Churn Rate) × Gross Margin %
```

**Simplified (no gross margin data):**
```
LTV = ARPA / Monthly Churn Rate
```

**Example:**
- ARPA: $500
- Monthly churn: 5% (0.05)
- Gross margin: 70% (0.70)
- LTV = ($500 / 0.05) × 0.70 = **$7,000**

**Simplified (no margin):** $500 / 0.05 = **$10,000**

**Why it matters:** LTV tells you the total revenue you can expect from an average customer. Must be at least 3x your CAC to have sustainable unit economics.

## LTV:CAC Ratio
```
LTV:CAC = LTV / CAC
```
Example: LTV $10k / CAC $2k = 5:1

## CAC Payback Period
```
Payback (months) = CAC / (ARPA × Gross Margin %)
Simplified: Payback = CAC / ARPA
```
Example: CAC $2k / ARPA $500 = 4 months

## NRR (Net Revenue Retention)
```
NRR % = ((MRR_start + Expansion MRR - Churned MRR - Contraction MRR) / MRR_start) × 100
```
Simplified (no expansion data): NRR ≈ (1 - Revenue Churn Rate) × 100

## Rule of 40
```
Score = Annualized MoM Growth % + Net Profit Margin %
Healthy: ≥ 40
```
