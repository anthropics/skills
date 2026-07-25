# Financial Planning Reference

Startup financial modeling frameworks. Build models that drive decisions, not models that impress investors.

---

## 1. Startup Financial Modeling

### Bottoms-Up vs Top-Down

**Top-down model (don't use for operating):**
```
TAM = $10B
SOM = 1% = $100M
Revenue = $100M in year 5
```
This is marketing. You cannot manage a company against these numbers.

**Bottoms-up model (use this):**
```
Year 1 Revenue Build:
  Sales headcount: 3 AEs by Q1, +2 in Q2, +3 in Q4
  Ramp curve: Month 1-3 = 25%, Month 4-6 = 75%, Month 7+ = 100%
  Quota per ramped AE: $600K ARR
  Effective quota (weighted for ramp): $1.2M ARR in Year 1
  Win rate: 25%
  Average deal: $48K ACV
  Pipeline needed: $1.2M / 25% = $4.8M ARR pipeline
  Required meetings to create that pipeline: $4.8M / (conversion 20%) / ($48K ACV × 0.5 to meeting) = ~200 meetings
```

Now you have something actionable. You know how many SDR calls, how many marketing leads, what conversion rate you need to hold. Every assumption is visible and challengeable.

### Building the Operating Model

#### Revenue Engine

**New ARR Model (SaaS):**
```
Month N New ARR:
  = Quota-carrying reps (fully ramped equivalent)
  × Attainment rate (typically 70-80% of quota)
  × Average deal size
  + PLG / self-serve (if applicable)

Quota-carrying reps (ramped equivalent):
  = Sum(each rep × their ramp factor)

Ramp schedule:
  Month 1-2: 0% (onboarding)
  Month 3: 25%
  Month 4-6: 50%
  Month 7-9: 75%
  Month 10+: 100%
```

**ARR Bridge (most important recurring visual):**
```
Beginning ARR
  + New ARR (new logos)
  + Expansion ARR (upsells, seat growth)
  - Churned ARR (cancellations)
  - Contraction ARR (downgrades)
= Ending ARR

Net ARR Added = New + Expansion - Churn - Contraction

Net Dollar Retention (NDR):
  = (Beginning ARR + Expansion - Churn - Contraction) / Beginning ARR × 100
  Target: > 110% for growth-stage SaaS
  World-class: > 130% (Snowflake, Twilio-tier)
```

**MRR and ARR Relationship:**
```
ARR = MRR × 12 (simple, always use this)
Never mix monthly and annual contracts in MRR without normalization.
Annual contract booked = ACV / 12 = monthly contribution to ARR
Multi-year contracts: book each year at annual value (not multi-year total)
```

#### Headcount Model

Headcount is usually 60-80% of total costs. Model it carefully.

```
For each role:
  - Start date
  - Department
  - Annual salary (from salary bands)
  - Loaded cost (salary × 1.25-1.45 depending on benefits + recruiting method)
  - Productive from (ramp period)
  - Impact on revenue (for revenue-generating roles)

Total headcount cost = Σ (each FTE × loaded cost × months active / 12)
```

**Department headcount ratios (Series A benchmarks):**
```
Sales (S&M): 20-30% of headcount
Engineering/Product (R&D): 40-50% of headcount
Customer Success: 15-20% of headcount
G&A: 10-15% of headcount
```

#### COGS Model

Gross margin is the most important long-term indicator of business quality.

**COGS for SaaS:**
```
1. Hosting / Infrastructure (AWS, GCP, Azure)
   - Scale with customer count or usage
   - Should be 5-15% of ARR for mature SaaS
   - If > 20%: infrastructure optimization needed

2. Customer Success headcount
   - Ratio: 1 CSM per $1M-$3M ARR (varies by segment)
   - SMB: 1 CSM per $500K ARR (high-touch required)
   - Enterprise: 1 CSM per $2-5M ARR (strategic accounts)

3. Third-party licensing / APIs
   - Per-customer or usage-based pass-through costs
   - Critical to model at scale (margin killer if not tracked)

4. Payment processing
   - 2.2-2.9% of revenue for Stripe/Braintree
   - Can negotiate to 1.8-2.2% at scale (> $5M ARR)
```

**Gross Margin targets:**
```
SaaS: > 65% acceptable, > 75% good, > 80% exceptional
Marketplace: 50-70%
Hardware + software: 40-60%
Services + software: 30-50%
```

**If gross margin < 65%:**
- Infrastructure cost optimization (rightsizing, reserved instances)
- CS headcount review (automation, pooled CSMs)
- Pricing model review (usage-based pricing if cost is usage-driven)
- Third-party cost renegotiation

#### Opex Model

```
Sales & Marketing:
  - AE/SDR/SE salaries + OTE (on-target earnings)
  - Marketing programs (demand gen budget)
  - Tools and technology (CRM, SEO, ads platforms)
  - Events and travel
  - Benchmark: 40-60% of revenue at growth stage, targeting < 30% at scale

Research & Development:
  - Engineering salaries
  - Product management
  - Design
  - Technical infrastructure for development
  - Benchmark: 20-35% of revenue

General & Administrative:
  - Finance, legal, HR, admin
  - Office costs
  - SaaS tools / software licenses
  - D&O insurance
  - Benchmark: 8-15% (target < 10% at scale)
```

### Financial Model Do's and Don'ts

| Do | Don't |
|----|-------|
| Build assumptions tab with all inputs | Hardcode numbers in formulas |
| Model monthly (not quarterly) at early stage | Use annual model for first 3 years |
| Start with headcount plan, build costs from it | Guess at expense line items |
| Show model to actual customers or users | Show model to investors before internal stress-test |
| Version your model | Overwrite old versions |
| Reconcile cash flow to P&L monthly | Trust P&L without cash flow model |
| Include a sensitivity table | Present single-scenario forecast |

---

## 2. Three-Statement Model for Startups

### Why All Three Matter

The P&L tells you if you're profitable. The cash flow statement tells you if you're alive. The balance sheet tells you if you're solvent.

Startups that only track P&L miss the gap between revenue recognition and cash collection.

### P&L Structure

```
                        Q1      Q2      Q3      Q4     FY
Revenue
  Subscription ARR    $400K   $520K   $680K   $840K  $2,440K
  Professional Svcs    $40K    $50K    $60K    $65K    $215K
Total Revenue         $440K   $570K   $740K   $905K  $2,655K

COGS
  Infrastructure       $35K    $42K    $52K    $62K    $191K
  CS Headcount         $75K    $75K   $100K   $100K    $350K
  3rd Party Licensing  $15K    $18K    $22K    $28K     $83K
Total COGS            $125K   $135K   $174K   $190K    $624K

Gross Profit          $315K   $435K   $566K   $715K  $2,031K
Gross Margin          71.6%   76.3%   76.5%   79.0%   76.5%

Operating Expenses
  Sales & Marketing   $380K   $420K   $480K   $520K  $1,800K
  Research & Dev      $320K   $340K   $380K   $400K  $1,440K
  General & Admin     $120K   $130K   $140K   $150K    $540K
Total Opex            $820K   $890K  $1000K  $1070K  $3,780K

EBITDA              ($505K) ($455K) ($434K) ($355K) ($1,749K)
EBITDA Margin       (114.8%)(79.8%) (58.6%) (39.2%)  (65.9%)
```

### Cash Flow Statement

```
                        Q1      Q2      Q3      Q4
Operating Activities
  Net Income          ($510K) ($460K) ($440K) ($360K)
  Add: D&A               $8K     $8K     $8K    $10K
  Working Capital Changes:
    AR increase         ($45K)  ($50K)  ($60K)  ($55K)
    AP increase          $20K    $15K    $20K    $15K
    Deferred Rev change  $80K    $60K    $80K    $90K
Operating Cash Flow   ($447K) ($427K) ($392K) ($300K)

Investing Activities
  Capex                 ($15K)   ($8K)  ($10K)  ($12K)
Free Cash Flow        ($462K) ($435K) ($402K) ($312K)

Financing Activities
  None                    $0      $0      $0      $0

Net Change in Cash    ($462K) ($435K) ($402K) ($312K)

Beginning Cash       $3,500K $3,038K $2,603K $2,201K
Ending Cash          $3,038K $2,603K $2,201K $1,889K
Runway (months)         13.1    12.1    10.9    10.1
```

**Key insight from this model:**
The deferred revenue offset (customers paying annually upfront) is reducing cash burn by ~$80-90K/quarter versus a pure monthly billing model. This is the CFO's lever — push for annual billing.

### Balance Sheet: The Startup Version

At early stage, track these specifically:

```
Assets:
  Cash: Your lifeline. Monitor daily.
  Accounts Receivable: What customers owe you. Age it monthly.
  Prepaid Expenses: Software licenses, insurance paid upfront.

Liabilities:
  Accounts Payable: What you owe vendors. Maximize terms.
  Accrued Liabilities: Salaries owed, commissions earned but not paid.
  Deferred Revenue: Customer prepayments. Liability until service delivered, but cash is yours.
  Debt/Convertible Notes: Face value + interest accrual.

Equity:
  Common Stock: Founder shares
  Preferred Stock: Investor shares
  APIC: Additional paid-in capital
  Accumulated Deficit: Your running losses (expected for startups)
```

---

## 3. SaaS Metrics That Matter

### The Hierarchy of SaaS Metrics

```
Tier 1 (existential): ARR, Runway, Net Dollar Retention
Tier 2 (strategic): Gross Margin, Burn Multiple, LTV:CAC
Tier 3 (operational): CAC Payback, Churn Rate, ACV
Tier 4 (diagnostic): Logo Churn vs Revenue Churn, Expansion Rate, NPS
```

Never report Tier 4 metrics to your board if Tier 1 metrics are off-track.

### Core Metric Definitions

**ARR (Annual Recurring Revenue):**
```
ARR = Sum of all active annual contract values (normalized to annual)
What it is NOT: bookings, billings, or TCV
When to use MRR: Companies with mostly monthly contracts
When to use ARR: Companies with majority annual contracts
```

**Net Dollar Retention (NDR / NRR):**
```
NDR = (Beginning MRR + Expansion MRR - Churned MRR - Contraction MRR)
      / Beginning MRR × 100

The benchmark everyone quotes: 100% means existing customers are flat.
> 100% means existing customers grow revenue on their own.
World-class (Snowflake, Datadog): 130%+

Why it matters: NDR > 100% means revenue growth even if you sign zero new customers.
At NDR = 120% and $5M ARR: you will reach $7M ARR in 24 months without a single new sale.
```

**Gross Revenue Retention (GRR):**
```
GRR = (Beginning MRR - Churned MRR - Contraction MRR) / Beginning MRR × 100

GRR measures the floor of your retention (ignoring expansion).
GRR is always ≤ NDR.
Target: > 85% for SMB SaaS, > 90% for mid-market, > 95% for enterprise.
```

**Logo Churn vs Revenue Churn:**
```
Logo churn: % of customers who cancel (ignores size)
Revenue churn: % of ARR that cancels (accounts for size)

Why the distinction matters:
  You could have 10% logo churn but 3% revenue churn (churning small customers)
  Or 5% logo churn but 12% revenue churn (churning large customers) — much worse

Report both. If they diverge significantly, investigate immediately.
```

**ACV (Annual Contract Value):**
```
ACV = Total contract value / contract term in years
Not to be confused with ARR (which only counts recurring, not one-time fees)

Rising ACV: You're moving upmarket (good for efficiency, check if ICP is changing)
Falling ACV: You're moving downmarket (check burn multiple — may not be economic)
```

**Rule of 40:**
```
Rule of 40 = Revenue Growth Rate % + EBITDA Margin %
Target: > 40%

Example: 60% growth + (-15%) EBITDA margin = 45. Passing.
Example: 20% growth + 5% EBITDA margin = 25. Failing at growth stage.

At early stage (< $5M ARR): Rule of 40 doesn't apply. Growth is the only metric.
At growth stage ($5-20M ARR): Starting to matter.
At scale ($20M+ ARR): Board and investors will hold you to this.
```

---

## 4. FP&A for Startups: What to Measure When

### Metrics by Stage

**Pre-seed / Seed (< $1M ARR):**
```
Focus on: Cash, pipeline, customer conversations
Measure: Monthly cash burn, weeks of runway, NPS / customer satisfaction
Don't obsess over: EBITDA margin, gross margin (too early)
Frequency: Weekly cash check, monthly everything else
```

**Series A ($1-5M ARR):**
```
Focus on: Repeatable sales, unit economics
Measure: MRR growth, LTV:CAC, CAC payback by channel, gross margin
Don't obsess over: Profitability, G&A efficiency
Build now: Monthly financial close (< 5 business days), basic FP&A model
Frequency: Monthly board pack, weekly leadership metrics
```

**Series B ($5-20M ARR):**
```
Focus on: Scalable go-to-market, operational efficiency
Measure: NDR, burn multiple, revenue per FTE, OKR attainment
Start building: Budget vs actuals, department-level P&L
Build now: Finance team (first financial controller), ERP or NetSuite
Frequency: Monthly board pack + quarterly deep dive
```

**Series C+ ($20M+ ARR):**
```
Focus on: Path to profitability, market leadership
Measure: Rule of 40, free cash flow, CAC efficiency by segment
Must have: FP&A team, full three-statement model, 5-year plan
Frequency: Monthly financial close (< 3 business days), quarterly earnings prep
```

### Reporting Cadence

**Weekly (CFO + leadership):**
- Cash balance (CFO checks daily, reports weekly)
- Pipeline / sales metrics (if in a sales-led motion)
- Any metric that changed dramatically vs. prior week

**Monthly (board + leadership):**
- Full financial dashboard (ARR, gross margin, burn, runway)
- Budget vs actual with explanations for > 10% variances
- Unit economics update
- Headcount change summary

**Quarterly (board + investors):**
- Full three-statement model vs budget
- Cohort analysis update
- Scenario planning review and trigger assessment
- Next quarter outlook

---

## 5. Budget vs Actual Analysis Framework

### The Purpose of BvA

Budget vs actual is not about being right. It's about understanding *why* you were wrong, so you can make better decisions.

The CFO who reports "we missed budget by 15%" without explanation is failing. The CFO who says "we missed budget by 15% because enterprise deals took 30 more days to close than modeled — here's what we're doing about it" is doing their job.

### BvA Template

```
Category              Budget    Actual    $ Var   % Var   Explanation
-------------------------------------------------------------------
ARR                  $2,400K   $2,280K  ($120K)   (5%)   2 enterprise deals slipped to Q1
New ARR               $400K     $350K   ($50K)   (13%)   Above
Expansion ARR         $120K     $140K    $20K     17%    PLG motion outperforming
Churn                 ($60K)    ($80K)  ($20K)   (33%)   2 unexpected SMB churns (now fixed)
Gross Margin           75.0%    73.2%    -1.8%    n/a    Infrastructure over-provisioned
S&M Spend            $820K     $840K   ($20K)    (2%)   Within tolerance
R&D Spend            $680K     $710K   ($30K)    (4%)   Backfill hire started month early
G&A Spend            $140K     $148K    ($8K)    (6%)   Legal fees for new customer contract
Cash Burn (net)      $580K     $648K   ($68K)   (12%)   Driven by ARR shortfall + costs
Runway (mo)           14.5      13.0    (1.5)     n/a   Tracking; fundraise target unchanged
```

### Variance Thresholds

```
< ±5%: Note in appendix, no explanation needed in main pack
5-10%: One-line explanation required
> 10%: Full paragraph: what happened, why, what changes
> 20%: Board conversation required (model assumption was wrong, or unexpected event)
```

### Forecasting vs Budgeting

**Budget:** Set at start of year. Fixed expectation. Updated quarterly.
**Forecast:** Rolling 3-month outlook. Updated monthly. Should converge with budget over time.

```
Common mistake: Treating forecast as wishful thinking ("what we hope happens")
Correct approach: Forecast is your best current estimate given all known information.
                  If forecast diverges from budget by > 15%, the budget is wrong.
                  Reforecast and communicate to board.
```

**Rolling forecast (recommended for startups):**
```
Always have a 12-month forward model.
Update it monthly with actuals replacing the first month.
The forecast should always reflect your current operational reality, not your hope.
```

---

## Key Formulas Reference

```python
# ARR and growth
ARR_growth_yoy = (ending_ARR - beginning_ARR) / beginning_ARR

# Net Dollar Retention
NDR = (beginning_MRR + expansion_MRR - churn_MRR - contraction_MRR) / beginning_MRR

# Burn Multiple
burn_multiple = net_cash_burn / net_new_ARR

# Rule of 40
rule_of_40 = revenue_growth_pct + ebitda_margin_pct

# LTV (SaaS)
LTV = (ARPA * gross_margin_pct) / monthly_churn_rate

# CAC Payback (months)
cac_payback = CAC / (ARPA * gross_margin_pct)

# Magic Number (sales efficiency)
magic_number = (net_new_ARR * 4) / prior_quarter_S_and_M_spend

# Gross margin
gross_margin = (revenue - COGS) / revenue

# Quick Ratio (growth efficiency)
quick_ratio = (new_MRR + expansion_MRR) / (churned_MRR + contraction_MRR)
# Target: > 4 for high-growth SaaS
```
