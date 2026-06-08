# Accounting Standards for Tech Companies

## ASC 606 — Revenue Recognition

ASC 606 ("Revenue from Contracts with Customers") is the universal standard for recognizing revenue, effective for public companies from 2018, private companies from 2019.

### The Five-Step Model

**Step 1: Identify the contract**
- Written or oral agreements with commercial substance
- Requires collectability to be probable
- Modifications: treat as new contract or modification to existing depending on distinct goods/services and pricing

**Step 2: Identify performance obligations**
- A performance obligation is a promise to transfer a distinct good or service
- Distinct: customer can benefit from the good/service on its own AND it is separately identifiable
- Common SaaS bundles with multiple performance obligations:
  - SaaS subscription license + implementation services + training → potentially 3 separate POs
  - Beware: many companies incorrectly bundle these and recognize too early or too late

**Step 3: Determine transaction price**
- Fixed consideration: straightforward
- Variable consideration (discounts, refunds, volume-based pricing, usage fees): use either:
  - Expected value method (probability-weighted average)
  - Most likely amount method
- Variable consideration is constrained: only recognize amounts unlikely to reverse materially
- Non-cash consideration (barter, equity received from customer): measure at fair value

**Step 4: Allocate transaction price**
- Allocate to each PO based on **standalone selling price (SSP)**
- SSP = price you would charge if sold separately
- If not directly observable: use adjusted market assessment, expected cost plus margin, or residual approach
- Do NOT allocate based on the prices listed in the bundled contract — must use SSP

**Step 5: Recognize revenue when (or as) performance obligations are satisfied**
- **Over time**: SaaS subscriptions recognized ratably over the contract term (e.g., $120K annual contract = $10K/month)
- **Point in time**: Professional services milestones, software licenses transferred at a point
- Control transfer test: customer receives and consumes benefits simultaneously (subscription) → over time

### Deferred Revenue
- Cash received before revenue is earned → Deferred Revenue liability on B/S
- Annual upfront contracts: collect $120K in January → recognize $10K/month → $110K deferred at Jan 31
- Deferred revenue roll-forward: Beginning DR + Billings − Revenue Recognized = Ending DR
- **Investor analysis**: Growing deferred revenue = healthy sales momentum; shrinking = demand warning

### Deferred Contract Costs (ASC 340-40)
- Sales commissions paid on new and renewal contracts must be capitalized and amortized (no longer expensed immediately)
- Amortization period: useful life of the customer relationship (typically 5–7 years for most SaaS)
- Exception: contracts < 1 year can use the practical expedient and expense immediately
- Creates a B/S asset: "Deferred Contract Costs" or "Capitalized Commissions"

### SaaS-Specific ASC 606 Complexities
- **Multi-year contracts with annual price escalators**: Variable consideration; estimate and allocate
- **Contract modifications** (upgrades/downgrades mid-term):
  - Upgrade = prospective new contract if distinct services added
  - Downgrade = modification requiring catch-up or prospective adjustment
- **Right of return / refund**: Estimate refunds; constrain revenue recognition accordingly
- **Usage-based pricing (consumption)**: Recognize as usage occurs (not ratably)
- **Free trials**: Not a performance obligation if truly no charge; recognize only when billing starts

---

## ASC 718 — Stock-Based Compensation

ASC 718 requires companies to recognize the fair value of equity awards as compensation expense over the vesting period.

### Key Concepts
- **Grant date fair value**: Use Black-Scholes model (options) or probability-weighted models (RSUs, PSUs)
- **Vesting schedule**: Most SaaS companies use 4-year vesting with 1-year cliff (25% vests at 1 year; remainder monthly/quarterly thereafter)
- **Service condition**: Most common; expense recognized ratably over vesting period
- **Performance condition**: Expense recognized when performance target is probable of achievement
- **Market condition**: Fair value incorporates market condition (e.g., stock price target) via Monte Carlo; expense recognized regardless of outcome

### 409A Valuation
- Private companies must obtain an independent 409A valuation to set fair value of common stock
- Required every 12 months or after a material event (funding round, M&A)
- 409A FMV is the exercise price for options; must equal or exceed common stock FMV
- If options are granted below FMV: Section 409A penalty tax exposure for employees

### Income Statement Impact
- SBC appears as operating expense in the department of the employee (R&D, S&M, G&A)
- Non-cash → added back in operating cash flow; builds APIC on balance sheet
- Board decks often show "Non-GAAP" metrics that exclude SBC; investors should scrutinize this
- For high-growth SaaS companies, SBC can be 10–20% of revenue — materially understating GAAP profitability vs. non-GAAP

### Disclosure Requirements
- Equity award activity roll-forward (shares granted, vested, forfeited, exercised)
- Weighted average grant date fair value and Black-Scholes assumptions (vol, risk-free rate, expected term)
- Unrecognized compensation cost and weighted average remaining recognition period

---

## ASC 350-40 — Internal-Use Software

Companies that develop software for internal use (including SaaS delivered to customers) capitalize qualifying development costs.

### Three Phases and Treatment

**Phase 1 — Preliminary Project Stage**
- Activities: concept evaluation, feasibility analysis, vendor selection, technology investigation
- **Treatment: EXPENSE as incurred** (no capitalization)

**Phase 2 — Application Development Stage**
- Activities: actual coding, testing, data conversion for live environment
- **Treatment: CAPITALIZE** — these costs become an intangible asset on the B/S
- Starts when: management authorizes and commits to funding the project AND technology determination is complete
- Ends when: software is ready for its intended use

**Phase 3 — Post-Implementation / Operation Stage**
- Activities: training, maintenance, minor bug fixes, operating the software
- **Treatment: EXPENSE as incurred** — unless costs add new functionality

### Capitalization Details
- Capitalize: direct labor (developer salaries allocated to coding/testing), contractor costs, cloud computing service costs (IaaS/PaaS used in development)
- Do NOT capitalize: G&A overhead, training, data migration (unless integral to go-live), research
- **Cloud computing costs** (ASC 350-40 updated 2018): Internal-use SaaS arrangements — implementation costs can be capitalized if they would be capitalized for on-premise equivalent
- Amortization: Straight-line over useful life (typically 3–5 years)

### Why This Matters for Tech Companies
- Incorrectly capitalizing R&D/operational costs overstates assets and understates expenses
- CFOs should review capitalization policies annually and ensure clean segregation between Phase 1/2/3 activities
- In fast-moving companies, activities often blur — documentation of project phases is essential for audit support

---

## Key Accounting Areas for SaaS: Summary Table

| Topic | Standard | Key Judgment | Cash vs. GAAP Difference |
|---|---|---|---|
| Subscription revenue | ASC 606 | PO identification, SSP allocation | Major: cash upfront, revenue recognized monthly |
| Sales commissions | ASC 340-40 | Amortization period | Expense timing deferred |
| Stock compensation | ASC 718 | Fair value measurement, vesting schedule | Non-cash; adds back to CF |
| Software development | ASC 350-40 | Phase determination, what to capitalize | Capex vs. OpEx treatment |
| Deferred revenue | ASC 606 | Contract term, modification accounting | Cash liability; not real debt |
