# Cash Management Reference

Cash is the oxygen of a startup. You can be unprofitable for years. You cannot be out of cash for a day.

---

## 1. Cash Flow Management

### The Cash Equation

```
Ending Cash = Beginning Cash
            + Cash collected from customers
            - Cash paid to employees
            - Cash paid to vendors
            - Cash paid for infrastructure
            - Debt service
            +/- Financing activities

Note: This is NOT the P&L. Revenue recognition ≠ cash collected.
```

### Where Cash Hides (and Leaks)

**Cash sources you might be under-using:**
- Deferred revenue (annual billing locks in cash 12 months early)
- Customer deposits on enterprise contracts
- Vendor payment terms (Net 60 instead of Net 30 = free float)
- AWS/GCP startup credits (often $25K–$100K available, widely unused)
- Revenue-based financing on predictable MRR
- Venture debt (non-dilutive, available post-Series A)

**Cash drains that sneak up on you:**
- Annual software licenses paid in Q1 (budget for the lump sum)
- Event sponsorships (often 6-12 months in advance)
- Recruiting fees (15-25% of first-year salary, due on hire)
- Legal fees (data room prep, fundraise close = $50K–$200K surprise)
- Late-paying enterprise customers (Net 60 in contract, pays Net 90 in practice)

### Cash Flow vs P&L: The Gap

**Scenario: $1M enterprise deal signed December 31**

```
P&L impact (accrual):
  December revenue: $83K (1/12 of annual)

Cash impact:
  If billed annually upfront:  +$1,000K in December (GREAT)
  If billed quarterly:         +$250K in December (good)
  If billed monthly:           +$83K in December (fine)
  If Net 60 terms:             +$0 in December, +$83K in February (cash drag)
```

**The CFO's job:** Maximize the timing difference between cash in and cash out.
- Collect from customers as early as possible (annual upfront, early payment discounts)
- Pay vendors as late as possible (maximize payment terms)
- Never confuse deferred revenue (a liability) with actual cash (it is cash — just count it right)

---

## 2. Treasury and Banking Strategy

### Account Structure

```
Operating Account (primary bank):
  Balance: 3-6 months of operating expenses
  Purpose: Payroll, vendor payments, day-to-day ops
  Product: Business checking or high-yield business savings
  Bank: Chase, SVB successor (First Citizens), Mercury, Brex

Reserve Account (secondary or same bank):
  Balance: Everything above operating float
  Purpose: Reserve; move to operating as needed
  Product: Money market fund or T-Bill ladder
  Target yield (2024-2025): 4.5%–5.2%
  Products: Vanguard VMFXX, Fidelity SPAXX, or direct T-Bills via TreasuryDirect

Emergency Account (separate bank):
  Balance: 1-2 months expenses
  Purpose: If primary bank has issues (SVB taught this lesson)
  Product: Business savings
```

**FDIC coverage:** $250K per depositor per institution. For balances above $250K at a single bank, either:
- Use CDARS/ICS (bank sweeps into multiple FDIC-insured accounts automatically)
- Spread across multiple banks
- Move excess to T-Bills (backed by US government, not FDIC, but safer)

**After SVB (March 2023):** Every CFO should have at least 2 banking relationships. If one bank fails or freezes, you can make payroll.

### Yield on Cash

At $3M cash, the difference between 0% (checking) and 5% (T-Bills) is $150K/year.
That's a month of runway for a $150K/month burn company. **Get yield on reserves.**

```
Monthly yield on $3M at 5%: ~$12,500
Annual: ~$150,000
This is not optional. Set it up once and automate.
```

---

## 3. AR/AP Optimization

### Accounts Receivable: Get Paid Faster

**Billing model impact on cash:**
```
                Annual Upfront  Quarterly    Monthly    Net 30 Monthly
Cash Day 1:      100% of ACV     25% of ACV    8.3%       0%
Cash Month 2:    0% (done)       0%            8.3%       8.3%
12-month total:  100%            100%          100%       100%

For $100K ACV customer, Year 1 cash:
  Annual upfront:  $100K immediately
  Monthly Net 30:  $8.3K × 11 months = $91.7K (1 month lag)
  Cash benefit:    $100K vs $91.7K = $8.3K benefit + no collection risk
```

**Push for annual billing. Make it easy with a discount:**
```
"Pay annually and get 2 months free (16% discount)"
Most SMB customers will take this.
Enterprise: use MSA structure with annual invoicing, not month-to-month.
```

**AR Aging Policy:**
```
> 0-30 days: Current. No action.
> 30-60 days: Friendly reminder from AR team.
> 60-90 days: Escalate to Customer Success.
> 90 days:    CFO or CEO-level outreach. Consider collections.
> 120 days:   Reserve for bad debt. Legal/collections.

Reserve policy: 50% of 90-120 day AR, 100% of > 120 days
```

**What slows down collections:**
- Wrong contact (billing contact vs. user) — get finance contact during onboarding
- Enterprise PO required — know this upfront, not when invoice is due
- Credit holds or budget freeze — your CSM should surface these early
- Invoice errors — every wrong invoice extends payment by 30-60 days

### Accounts Payable: Pay Slower

**Standard terms by vendor type:**
```
SaaS tools:      Net 30 default. Push for Net 45 or Net 60 at scale.
Cloud providers: Pay as you go. Apply for credits first.
Professional services (agencies, lawyers): Net 30 minimum. Get Net 45 where possible.
Rent/office:     Whatever the lease says. Negotiate quarterly payments if you can.
Payroll:         Pay on time. Never delay payroll. Ever.
```

**Early payment discount trap:**
```
"2/10 Net 30" means: 2% discount if you pay in 10 days, else pay in 30.
Annual cost of NOT taking this: 2% × (365/(30-10)) = ~36% APY
ALWAYS take early payment discounts > 2%.
Never take discounts < 1%.
```

**AP workflow:**
1. All invoices → finance inbox (not individual employees)
2. Approval required above threshold ($500 for startups)
3. Pay at end of terms, not when invoice arrives
4. Batch payments weekly (not daily) to reduce processing overhead

---

## 4. Runway Extension Tactics

Use these when you need to extend runway without raising. Ranked by speed and impact.

### Tier 1: Fast Cash (Days)

**Annual billing campaign:**
```
Target: Existing monthly customers
Offer: 2 months free (16% discount) or 1 month free (8% discount) for annual upfront
Process: CSM-led email campaign to all monthly customers
Impact: $X MRR × 12 × conversion rate = immediate cash injection
Timeline: 2-4 weeks
No dilution. No debt. High impact.
```

**Prepayment incentive for pipeline:**
```
For deals in late stage, offer annual upfront pricing with 10-15% discount.
Close rate may increase. Cash timing dramatically improves.
```

### Tier 2: Cost Control (2-4 Weeks)

**Hiring freeze:**
```
Every unfilled role = salary × 1.25 per month.
For a 30-person company, 3 open roles at $150K average:
  Monthly savings: 3 × $150K × 1.25 / 12 = $47K/month
  Over 6 months: $280K
Impact: Immediate. No blood.
```

**Software audit:**
```
Pull all credit card charges and ACH debits.
Cancel any subscription not used in 30 days.
Typical savings: $3K-$15K/month at Series A stage.
Tools: Vendr, Spendesk, or just a spreadsheet of recurring charges.
```

**Cloud cost optimization:**
```
Right-size instances (dev/staging don't need prod-scale)
Reserve instances (1-year reserved = 30-40% savings vs on-demand)
Delete unused resources (load balancers, IPs, old snapshots)
Typical savings: 20-35% of current cloud bill
```

### Tier 3: Vendor Renegotiation (2-6 Weeks)

**Payment term extension:**
```
Ask key vendors for Net 60 instead of Net 30.
$500K in AP × 30 days = $500K × (30/365) = ~$41K cash float improvement
Won't always work, but vendors often say yes to good customers.
```

**Renewal timing:**
```
Push annual renewals to later in the year.
Preserve cash for Q1 (typically heaviest sales hiring quarter).
```

**Vendor credits:**
```
AWS: AWS Activate (up to $100K for qualified startups)
GCP: Google for Startups (up to $200K)
Azure: Microsoft for Startups (up to $150K)
Stripe: Revenue share programs
Hubspot: Startup pricing (90% off)
```

### Tier 4: Financing (Weeks to Months)

**Revenue-based financing:**
```
Providers: Clearco, Capchase, Pipe, Arc
Structure: Advance 3-6 months of MRR. Repay with % of monthly revenue.
Cost: Typically 6-12% annualized.
Speed: 1-2 weeks to close.
When to use: Bridge to next ARR milestone before raising equity.
When NOT to use: When burn rate is structural (will consume the advance fast).
```

**Venture debt:**
```
Providers: SVB (now First Citizens), Western Technology Investment, Hercules, TriplePoint
Structure: Term loan, typically 3-6x monthly gross burn
Interest: Prime + 2-4% + warrants
When available: Post-Series A, when revenue is predictable
Typical timing: Add alongside an equity round (don't raise debt when you need equity)
Impact: Extends runway 3-6 months without dilution
When NOT to use: If you might trip financial covenants (minimum cash, revenue)
```

**Convertible bridge:**
```
Existing investors write bridge note: $500K-$2M at favorable terms.
Structure: Converts at discount (10-20%) or cap into next equity round.
When to use: You're 60-90 days from closing an equity round and need cash to get there.
When NOT to use: As a long-term strategy. Bridge-to-bridge is a death spiral.
```

### Tier 5: Structural Cost Reduction (Weeks + Impact on Morale)

**Salary deferrals (founders first):**
```
Founders take 20-30% salary reduction, accrued for future repayment.
Signals commitment to team and investors.
Only ask employees to follow if founders go first.
Always pay market rate to key non-founder employees — you can't afford to lose them.
```

**Reduction in force (RIF):**
```
Threshold: If burn multiple > 3x and growth < 20% YoY, a RIF is likely necessary.
Sizing: Model to achieve at least 12 months runway without fundraising.
Rule: Don't do a RIF twice. Size it right the first time.
  Two small RIFs destroy morale worse than one decisive one.
Process: Legal counsel required. WARN Act (60-day notice) if > 100 employees.
Focus cuts: G&A and underperforming sales roles first. Protect engineering and key revenue.
```

---

## 5. When to Cut vs When to Invest

### The Framework

**Cut when:**
- Burn multiple > 2x and growth is decelerating
- Runway < 9 months with no fundraise imminent
- LTV:CAC declining for 3+ consecutive months
- Any spend category with no measurable return in 90 days
- Headcount in functions not directly tied to near-term revenue or product-market fit

**Invest when:**
- Magic number > 1 (every dollar in S&M returns > $1 in gross profit)
- LTV:CAC > 3x in a specific channel (pour money in)
- Gross margin > 70% (unit economics are healthy; growth is the constraint)
- Cohort data improving (retention getting better → LTV going up → invest in growth)
- CAC payback < 12 months (you get your money back fast enough to keep reinvesting)

### The False Economy Trap

**Don't cut:** 
- Top-of-funnel demand gen that generates qualified pipeline (if CAC payback is < 12 months, this is your best investment)
- Engineering capacity on core product (technical debt compounds and slows you down permanently)
- Key account managers on your largest customers (churn from top customers is catastrophic)

**Cut these first:**
- Conference sponsorships with no measurable pipeline
- Tools and subscriptions with < 5 users or < 30% utilization
- Agency spend that could be done in-house
- Roadmap items that aren't tied to retention or expansion revenue
- Any G&A spend that isn't legally required

### Decision Triggers (Pre-Define These)

Don't make these decisions in a crisis. Define the triggers now:

```
At 12 months runway:  Review all discretionary spend. Start fundraise process.
At 9 months runway:   Implement hiring freeze. Fundraise is mandatory.
At 6 months runway:   Cut non-essential spend 20%. If no fundraise term sheet, run RIF model.
At 4 months runway:   Execute RIF. Explore all financing options. Notify board.
At 3 months runway:   Emergency plan only. All options on table (bridge, strategic, wind down).
```

---

## Key Formulas

```python
# Net burn
net_burn = gross_burn - revenue_collected

# Runway (months)
runway_months = cash_balance / net_burn

# Cash conversion cycle
ccc = days_sales_outstanding + days_inventory_held - days_payable_outstanding
# Lower CCC = better cash efficiency

# Days Sales Outstanding (DSO)
dso = (accounts_receivable / revenue) * 30  # monthly revenue

# Days Payable Outstanding (DPO)
dpo = (accounts_payable / cogs) * 30  # target: maximize this

# Working capital
working_capital = current_assets - current_liabilities

# Quick ratio (liquidity)
quick_ratio_liquidity = (cash + ar) / current_liabilities
# Target: > 1.5 (you can pay short-term obligations without selling assets)

# Free cash flow
fcf = operating_cash_flow - capex
```
