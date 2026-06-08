# Cash Flow Management

## Operating Cash Flow Optimization

Operating cash flow (OCF) = Net Income + Non-Cash Items (D&A, SBC, amortization) ± Working Capital Changes

For SaaS companies, OCF is often better than net income due to:
- Large SBC add-back (non-cash expense)
- Deferred revenue increases (cash collected before recognition)
- Prepaid annual contracts (customers pay upfront)

**Strategies to maximize OCF:**
1. Bill annually upfront rather than monthly (accelerates cash, reduces collections risk)
2. Offer discounts for annual prepayment (e.g., 2 months free = ~17% discount; worth it for cash flow and reduced churn)
3. Automate invoicing and collections to reduce DSO
4. Negotiate extended payment terms with suppliers (increase DPO)
5. Minimize Capex by using cloud infrastructure (OpEx vs. Capex; maintains FCF)

## Working Capital Management

**Working Capital** = Current Assets − Current Liabilities

For SaaS companies, working capital dynamics differ from manufacturing:
- Low inventory
- Large deferred revenue liability (negative working capital signal in traditional analysis, but actually positive for SaaS — means customers paid ahead)
- Main working capital drivers: AR (DSO) and AP (DPO)

**Working capital best practices:**
- Review DSO monthly; >60 days is a red flag requiring collections intervention
- Segment AR aging into buckets: current, 1–30 days past due, 31–60, 61–90, 90+
- Establish credit policies: limit credit extended to new customers with poor payment history
- Automate dunning (payment reminder) sequences: email at 7, 14, 30 days past due

## Cash Conversion Cycle (CCC)

**CCC = DSO + DIO − DPO**

For SaaS companies (no inventory): **CCC = DSO − DPO**

Each component:
- **DSO** (Days Sales Outstanding) = (Accounts Receivable / Revenue) × Days in Period
  - Measures how long it takes to collect cash after recognizing revenue
  - SaaS target: 30–45 days
  - Best-in-class with annual upfront billing: negative DSO (cash before revenue recognition)
- **DIO** (Days Inventory Outstanding) = (Inventory / COGS) × Days — N/A for pure SaaS
- **DPO** (Days Payable Outstanding) = (Accounts Payable / COGS) × Days
  - Measures how long you take to pay suppliers
  - Maximize DPO: negotiate 45–60 day terms with major vendors (vs. industry standard 30 days)
  - Never pay early unless there is a meaningful discount (e.g., 2/10 net 30 = ~36% annualized return)

**CCC optimization levers:**
1. **Reduce DSO**: Auto-pay mandates, ACH over checks, early payment discounts, EIPP portals
2. **Extend DPO**: Negotiate longer payment terms; use corporate credit cards to defer payment by 30–60 days
3. For SaaS: Shift to annual upfront billing to create negative CCC (cash received before earning it)

**JP Morgan benchmark**: Median CCC for SaaS companies is −30 to +30 days; pure monthly billers may have CCC of 60–90+ days.

## Accounts Receivable Optimization

**Collection processes:**
- Invoice within 24 hours of contract signing
- Set up automated payment reminders at 7, 14, 30 days past due
- Escalate to account executive at 45 days (they have relationship leverage)
- Engage collections agency or legal at 90+ days
- Maintain an allowance for doubtful accounts (typically 1–3% of AR for B2B SaaS)

**Credit policies:**
- Require credit card or ACH for SMB customers
- Run credit checks for enterprise customers >$50K ACV
- Get personal guarantees from small businesses

**AR KPIs to track monthly:**
- DSO (target and actual)
- AR aging buckets
- Collection rate (% of invoices collected within payment terms)
- Bad debt expense as % of revenue

## Accounts Payable Optimization

**AP best practices:**
- Centralize AP processing; avoid duplicate payments with 3-way match (PO → receipt → invoice)
- Negotiate payment terms with all major vendors at contract signing; start at net 45 or net 60
- Batch payments twice monthly rather than ad hoc (preserves cash, reduces bank fees)
- Use corporate credit cards for software subscriptions: defers cash outflow 30–60 days; earns rewards
- Capture early payment discounts only when they exceed the opportunity cost of capital

**AP automation tools**: Bill.com, Tipalti, Airbase, Ramp — automate approval workflows, reduce manual entry, provide spend visibility

## Short-Term Financing

**Revolving credit facility (revolver):**
- Standby line of credit based on eligible AR (typically 80–85% of receivables <90 days old)
- Interest paid only when drawn
- Cost: SOFR + 2–4% for well-capitalized companies
- Use as insurance/bridge, not as permanent financing

**Invoice factoring / AR financing:**
- Sell receivables at a discount (1–3% fee) for immediate cash
- Expensive but useful when DSO is high and cash is needed
- Alternative: Receivables Purchase Agreements (e.g., through SVB or Mercury)

**Corporate credit cards:**
- Ramp, Brex, Airbase provide net 45–60 day float
- Spend management software with real-time controls

## Cash Forecasting

Build a rolling 13-week cash forecast for operational management:
- Start with beginning cash balance
- + Expected customer collections (from AR aging × expected collection rates)
- − Payroll disbursements (fixed — weekly or bi-weekly)
- − AP payments (from committed purchase orders and vendor contracts)
- − Rent, lease payments, debt service
- = Projected ending cash

Update weekly. Flag any projected balance below target minimum cash reserve (typically 3 months of operating expenses).

**Board-level reporting**: Report cash position + runway (months at current burn), trend in burn rate, and any covenant compliance for debt facilities.
