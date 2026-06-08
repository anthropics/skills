# Corporate Finance for Tech Companies

## WACC (Weighted Average Cost of Capital)

**Formula**: WACC = (E/V × Cost of Equity) + (D/V × Cost of Debt × (1 − Tax Rate))

Where:
- E = Market value of equity
- D = Market value of debt
- V = E + D (total firm value)
- Cost of Debt = interest rate on borrowings (pre-tax)
- Tax rate shields debt interest (interest is tax-deductible)

### Cost of Equity (CAPM)
**Cost of Equity = Risk-Free Rate + Beta × Equity Risk Premium**
- Risk-free rate: 10-year US Treasury yield (~4.0–4.5% in 2024–2026)
- Equity Risk Premium: ~5.5–6.0% (long-run historical US market premium)
- Beta: systematic risk vs. market (public SaaS companies average beta of 1.2–1.8)
- For private companies: add illiquidity premium of 2–4% and size premium of 2–5% for micro/small caps

### WACC for Tech Companies (2024–2026)
- Early-stage private SaaS: 20–30% (high risk, pure equity funded, use for internal investment decisions)
- Growth-stage VC-backed ($20M–$100M ARR): 15–20%
- Public SaaS (large-cap): 9–13%
- WACC has risen significantly from 2020–2022 lows due to higher risk-free rates

### WACC Applications
- **Discount rate in DCF models**: Use WACC when projecting UFCF (unlevered)
- **Investment hurdle rate**: Projects/acquisitions must return above WACC to create value
- **Capital structure decisions**: If cost of debt < WACC, adding debt can reduce WACC (up to a point)

---

## Capital Structure Optimization

### Modigliani-Miller Framework
- In a world with taxes, debt creates value through the interest tax shield: Tax Shield = Tax Rate × Debt
- But too much debt creates financial distress costs that erode value
- **Optimal capital structure**: Balance tax shield benefits against distress costs

### Tech Company Capital Structure Norms
- **Pre-revenue / early stage**: 100% equity (venture capital)
- **$5M–$20M ARR**: Primarily equity with potential venture debt component (10–20% of total capital)
- **$20M–$100M ARR**: Equity + venture debt; potential for non-dilutive RBF
- **$100M+ ARR / EBITDA-positive**: Bank debt (revolvers, term loans), venture debt, potential high-yield

### Debt vs. Equity Decision Framework
Use equity when:
- High growth requiring heavy investment (CAC payback >18 months)
- Unpredictable cash flows
- Covenant-heavy debt would restrict operating flexibility
- Network effects or winner-take-all market requiring capital to capture share

Use debt when:
- Predictable recurring revenue (SaaS contracts are perfect collateral)
- EBITDA-positive or clear path to FCF within debt term
- Avoiding dilution at a lower valuation is strategically important
- Bridge to next equity milestone

---

## Revenue-Based Financing (RBF)

### Mechanics
RBF investors provide upfront capital in exchange for a share of future revenue until a fixed repayment cap (typically 1.3x–2.0x of capital advanced) is reached.

- **Repayment**: 2–10% of monthly revenue until total cap reached
- **No equity dilution, no warrants, no personal guarantees** (key advantage)
- **Flexible repayment**: In slow months, pay less; in strong months, pay more

### Key Providers (2024–2026)
- **Pipe** (pipe.com): Leading RBF marketplace; trades contracted SaaS revenue
- **Capchase**: SaaS-focused; offers both RBF and credit facilities
- **Clearco**: E-commerce and SaaS; revenue-based capital
- **Arc**: SaaS-specific debt and RBF hybrid
- **re:cap**: European RBF provider with SaaS focus

### RBF Qualification Criteria
- Minimum MRR: typically $10K–$100K+
- 6–12 months of operating history
- Consistent MRR (not lumpy or declining)
- Advance amount: typically 3–6 months of MRR

### Effective Cost of RBF
- Annualized cost depends on repayment speed; faster growth = shorter payback = higher APR
- Typical effective APR: 15–35% when repaid in 12–18 months
- Compare carefully against venture debt and bank credit lines

### When to Use RBF
- To fund sales and marketing without dilution
- Bridge to next equity round at higher valuation
- When equity markets are unfavorable
- For capital-efficient companies with predictable SaaS revenue

---

## Venture Debt

### What It Is
A loan product designed for VC-backed startups — provides capital without the dilution of an equity round. Not available to bootstrapped companies (requires institutional venture backing as implicit guarantee).

### Market Size (2024)
- Venture debt volumes hit $53.3 billion in 2024 (94.5% growth from $27.4B in 2023)
- Q1 2024: venture debt = 18.6% of total VC funding

### Structure and Terms
- **Loan size**: Typically 20–35% of the most recent equity round (some lenders up to 50%)
- **Term**: 24–48 months, often with 12-month interest-only period followed by amortization
- **Interest rate**: SOFR + 6–9%, total range approximately 8–15% annualized (2024–2026 environment)
- **Warrant coverage**: 0.5–3% of loan amount in equity warrants (strike price typically at last round price)
- **Covenants**: Minimum cash balance, MACs (material adverse change clauses), springing covenants tied to ARR or burn

### Key Lenders
- **Silicon Valley Bank (First Citizens)**: Most established; relationship-focused; best terms for top-tier VC-backed companies
- **Hercules Capital**: Business development company; publicly traded; active in growth lending
- **Western Technology Investment (WTI)**: Deep VC network; flexible structures
- **Runway Growth Capital**: Flexible structures for pre-profitability companies
- **JP Morgan Innovation Economy**: Large institutional lender with venture debt product
- **Triplepoint Capital**: Growth stage focus

### When to Use Venture Debt
- Extend runway between equity rounds without additional dilution
- Fund specific capital projects (data center, marketing initiative)
- Bridge to a known milestone (product launch, ARR target)
- Acquire a company using non-dilutive capital

### Venture Debt vs. Equity
| Factor | Venture Debt | Equity |
|---|---|---|
| Dilution | Minimal (warrant coverage) | Significant |
| Repayment | Required (principal + interest) | None |
| Speed | 2–4 weeks | 3–6 months |
| Risk | Covenant default risk | Dilution |
| Cost | 10–15% APR all-in | Implicit cost = founders' equity |

### Negotiating Venture Debt
- Push back on warrant coverage (target <1% of loan amount)
- Avoid springing covenants tied to difficult-to-predict ARR
- Negotiate a 12-month draw period (don't take all capital at once)
- Get multiple term sheets from 3+ lenders to create competition

---

## Bank Credit Facilities (Profitable Companies)

For EBITDA-positive or FCF-positive companies:
- **Revolving credit facility**: Borrowing base tied to AR; SOFR + 1.5–3.5%
- **Term loan A**: Senior secured; typically 3–5 year term; covenant-lite for strong credits
- **Covenant benchmarks**: Minimum liquidity, maximum leverage ratio (total debt / EBITDA; typically 4–5x for SaaS)
