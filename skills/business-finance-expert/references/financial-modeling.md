# Financial Modeling

## 3-Statement Financial Model

The integrated 3-statement model is the foundation for all valuation work. Every LBO, DCF, and M&A model is built on top of a functioning 3-statement model.

### Build Order
1. **Historical financials**: Input 3–5 years of actuals for P&L, B/S, Cash Flow
2. **Assumptions sheet**: Drive everything from explicit, auditable assumptions (growth rates, margin targets, DSO, DSO, capex % of revenue)
3. **Income Statement forecast**: Revenue → COGS → Gross Profit → OpEx → EBIT → taxes → Net Income
4. **Balance Sheet forecast**: AR, AP, deferred revenue, PP&E, debt schedule
5. **Cash Flow Statement**: Derive from NI + B/S changes (working capital) + capex + financing
6. **Circular reference check**: Revolver balance (if any) may require iterative calculations

### Key Linkages to Hard-Code
- Net Income → Retained Earnings (B/S equity)
- D&A (P&L) → added back in operating CF; reduces net PP&E on B/S
- SBC (P&L expense) → added back in CF; increases APIC on B/S
- Capex (investing CF) → increases gross PP&E on B/S
- Debt drawdowns/repayments (financing CF) → change debt on B/S; interest expense flows to P&L
- Revenue recognized (P&L) → reduces Deferred Revenue on B/S
- Cash at end of period (CF) = Cash on B/S

### Model Best Practices
- Color-code: blue for inputs/assumptions, black for formulas, green for links from other sheets
- Never hardcode numbers inside formulas
- Use named ranges or clearly labeled assumption rows
- Build in error checks: B/S must balance (Assets = Liabilities + Equity); ending cash must tie to B/S
- Use separate tabs: Assumptions, P&L, Balance Sheet, Cash Flow, Debt Schedule, Supporting Schedules

## Discounted Cash Flow (DCF) Analysis

### Formula
**Enterprise Value = Σ [FCFt / (1+WACC)^t] + Terminal Value / (1+WACC)^n**

Where FCF = EBIT(1−Tax Rate) + D&A − Capex − Change in Working Capital

### Steps
1. Project Unlevered Free Cash Flow (UFCF) for 5–10 years
2. Calculate WACC (see Corporate Finance reference)
3. Calculate Terminal Value using one of two methods:
   - **Gordon Growth Model (Perpetuity)**: TV = FCFn × (1+g) / (WACC − g), where g = long-term growth rate (typically 2–3% for mature businesses)
   - **Exit Multiple Method**: TV = Final Year EBITDA × EV/EBITDA exit multiple (use comparable company multiples)
4. Discount all cash flows and TV back to present
5. Bridge Enterprise Value to Equity Value: EV − Net Debt + Cash = Equity Value; Equity Value / Diluted Shares = Price Per Share

### Key Sensitivities (Always Model These)
- WACC ± 1–2% (discount rate sensitivity)
- Terminal growth rate ± 0.5–1.0%
- Revenue growth rate ± 5%
- EBITDA margin ± 3–5%

### DCF Common Pitfalls
- Terminal value often represents 60–80% of total EV — be rigorous about TV assumptions
- Use UFCF (unlevered) when discounting at WACC; use FCFE (levered) when discounting at cost of equity
- Avoid circular references with revolver; use iterative calculations or a debt schedule
- WACC must match the cash flow definition: UFCF → WACC; FCFE → cost of equity

## Comparable Company Analysis (Trading Comps)

### Process
1. Select 8–15 publicly traded peers (same sector, similar revenue scale, comparable growth profile)
2. Spread key financial metrics for LTM and NTM (next twelve months):
   - Revenue, Revenue Growth %, Gross Margin, EBITDA, EBITDA Margin, FCF
3. Calculate trading multiples for each comp:
   - EV/Revenue (LTM and NTM)
   - EV/EBITDA (LTM and NTM)
   - EV/Gross Profit
   - P/E (for profitable companies)
4. Determine median and 25th/75th percentile ranges
5. Apply to your company's metrics → implied valuation range

### SaaS-Specific Multiples (2024–2026 context)
- Median public SaaS EV/NTM Revenue: 4–6x
- High-growth (>30% ARR growth) premium: 8–15x
- NRR >120% earns 2–3x premium vs. peers at same growth rate
- Each 10 percentage points of NRR above 100% adds ~1–2x to EV/Revenue multiple

## Precedent Transaction Analysis (Deal Comps)

Similar to trading comps but uses acquisition prices. Key differences:
- Transactions include a **control premium** (typically 20–40% over pre-announcement price)
- Use TEV/LTM Revenue and TEV/LTM EBITDA as primary multiples
- Strategic acquirers pay more than financial buyers (synergy value)
- Account for market conditions at time of deal vs. current environment

## Leveraged Buyout (LBO) Analysis

### Purpose
Determines the maximum price a private equity firm can pay while still achieving its target return (typically 20–25% IRR or 2.0–3.0x MOIC over 5 years).

### Structure
- Typical leverage: 4–6x EBITDA in total debt (varies with market)
- Equity contribution: 30–50% of total TEV
- Returns driven by: entry multiple, exit multiple, EBITDA growth, and debt paydown

### Key Inputs
- Entry price (TEV) and entry multiple (EV/EBITDA or EV/Revenue)
- Debt structure (senior secured, second lien, mezzanine) and interest rates
- Revenue and EBITDA growth projections
- Exit year (typically 5 years) and exit multiple
- Management fees, transaction fees, and debt issuance costs

### LBO Model Output
- Returns table: IRR and MOIC at various entry/exit multiples
- Sources and uses of funds (how the deal is financed)
- Debt paydown schedule (free cash flow → debt repayment)

## Sensitivity Analysis

Always build a two-variable data table for your most critical outputs (Enterprise Value, IRR, FCF):
- X-axis: Key revenue/growth assumption (growth rate, ARR, NRR)
- Y-axis: Key margin/discount assumption (WACC, EBITDA margin, exit multiple)

Present as color-coded heat map: green for favorable outcomes, red for unfavorable.

## Monte Carlo Simulation

Used for probabilistic valuation — replaces static sensitivity tables with full probability distributions.

### Process
1. Identify 3–5 key uncertain variables (revenue growth rate, churn, gross margin)
2. Assign probability distributions to each (normal, triangular, or discrete)
3. Run 1,000–10,000 simulations sampling from those distributions
4. Output: probability distribution of enterprise value / IRR
5. Read as: "There is a 70% probability that EV falls between $X and $Y"

### Tools
- Excel with @Risk or Crystal Ball add-ins
- Python (scipy, numpy) for custom models
- Best for: fundraising scenario planning, acquisition bid ranges, capital adequacy stress tests
