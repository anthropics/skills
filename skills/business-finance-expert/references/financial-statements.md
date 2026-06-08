# Financial Statements Mastery

## The Three Core Statements

### Income Statement (P&L)
Measures profitability over a period. Structure (top to bottom):
- **Revenue** (Net Revenue after returns/discounts)
- **COGS** (Cost of Goods Sold / Cost of Revenue)
- **Gross Profit** = Revenue − COGS
- **Operating Expenses**: R&D, S&M, G&A
- **EBIT** (Operating Income) = Gross Profit − OpEx
- **EBITDA** = EBIT + D&A (adds back non-cash charges)
- **Net Income** = EBIT − Interest − Taxes

For SaaS, separate subscription revenue from professional services revenue, as they carry vastly different gross margins (70–85% vs. 20–35%).

### Balance Sheet
A snapshot at a point in time. The fundamental equation: **Assets = Liabilities + Equity**

**Assets (Current → Non-Current):**
- Cash and cash equivalents
- Accounts Receivable (net of allowance)
- Prepaid expenses and other current assets
- PP&E (net of accumulated depreciation)
- Intangible assets (capitalized software, goodwill)
- Deferred contract costs (ASC 340-40)

**Liabilities (Current → Long-Term):**
- Accounts Payable
- Accrued liabilities
- Deferred Revenue (current and long-term)
- Debt (current portion and long-term)

**Equity:**
- Common stock, APIC, Retained Earnings (Accumulated Deficit)
- Stock-based compensation accumulates in APIC

### Cash Flow Statement
Three sections — the most important statement for evaluating a business's health:

**Operating Activities (Indirect Method):**
Start with Net Income → Add back D&A and SBC (non-cash) → Adjust for working capital changes:
- Increase in AR = use of cash (negative)
- Increase in Deferred Revenue = source of cash (positive) — SaaS advantage
- Increase in AP = source of cash (positive)

**Investing Activities:**
- Capex (PP&E purchases), capitalized software development costs
- Acquisitions, investments

**Free Cash Flow (FCF)** = Operating Cash Flow − Capex
This is the metric investors use to assess capital generation. For SaaS, FCF margin is the profitability input for Rule of 40.

**Financing Activities:**
- Debt issuance/repayment, equity raises, dividends, share buybacks

## Key Financial Ratios

### Liquidity
- **Current Ratio** = Current Assets / Current Liabilities (healthy: >1.5x; SaaS often lower due to deferred revenue)
- **Quick Ratio** = (Cash + AR) / Current Liabilities (healthy: >1.0x)
- **Cash Runway** = Cash Balance / Monthly Net Burn (target: 18+ months)

### Profitability
- **Gross Margin** = Gross Profit / Revenue × 100 (SaaS target: 70–85%)
- **EBITDA Margin** = EBITDA / Revenue × 100
- **Operating Margin** = EBIT / Revenue × 100
- **Net Income Margin** = Net Income / Revenue × 100
- **FCF Margin** = FCF / Revenue × 100 (best-in-class SaaS: >20%)

### Efficiency / Leverage
- **ROE** = Net Income / Shareholders' Equity (measures return on equity capital)
- **ROA** = Net Income / Total Assets (asset efficiency)
- **Debt-to-Equity** = Total Debt / Shareholders' Equity
- **Interest Coverage Ratio** = EBIT / Interest Expense (healthy: >3x)
- **Asset Turnover** = Revenue / Average Total Assets

### Working Capital
- **Days Sales Outstanding (DSO)** = (AR / Revenue) × Days in Period (target for SaaS: 30–45 days)
- **Days Payable Outstanding (DPO)** = (AP / COGS) × Days in Period (maximize to extend cash)
- **Cash Conversion Cycle (CCC)** = DSO + DIO − DPO (shorter = better)

## Common-Size Analysis

**Vertical Analysis**: Express every P&L line as a % of revenue, every B/S line as a % of total assets. Enables cross-company comparison regardless of scale.

Benchmark SaaS P&L as % of revenue (growth-stage, $10M–$50M ARR):
- Gross Margin: 70–80%
- R&D: 20–30%
- S&M: 30–50%
- G&A: 10–20%
- EBITDA: −20% to +10%

**Horizontal Analysis**: Track period-over-period change ($ and %) for each line item. Flags acceleration/deceleration in costs relative to revenue. Run horizontal analysis quarterly and annually.

## Statement Linkages (Critical for Modeling)
- Net Income flows from P&L → Retained Earnings on Balance Sheet
- D&A from P&L → added back in Operating Cash Flow
- SBC from P&L → added back in Operating Cash Flow → builds APIC on B/S
- Capex on Cash Flow Statement → increases PP&E on B/S; D&A reduces it
- Deferred Revenue on B/S → recognized as revenue on P&L over time
- AR on B/S → changes drive operating cash flow
- Net Income + B/S changes = Operating Cash Flow (the reconciliation)

## Reading and Interpreting Financial Statements: Practitioner Framework

1. **Start with gross margin trend** — compression signals pricing, infrastructure, or support cost problems
2. **Check ARR bridge / revenue waterfall** — net new ARR = new + expansion − contraction − churn
3. **Operating leverage analysis** — are operating expenses growing slower than revenue? (should converge toward profitability)
4. **FCF vs. EBITDA divergence** — large gap signals working capital issues or high capex
5. **Deferred revenue trend** — growing deferred revenue = healthy future revenue pipeline; shrinking = demand signal
6. **Cash position and runway** — absolute amount and months of runway at current burn rate
7. **Headcount productivity** — Revenue per FTE, ARR per quota-carrying rep
