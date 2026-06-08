# Tax Strategy for Tech Companies

## R&D Tax Credits (Federal — IRC Section 41)

The R&D tax credit is one of the most valuable and underutilized tax incentives available to technology companies. It directly reduces federal income tax liability dollar-for-dollar (not just a deduction).

### Credit Rates
- **Regular Credit Method (RRC)**: 20% of qualifying research expenses above a base amount (complex to calculate)
- **Alternative Simplified Credit (ASC) Method**: 14% of QREs exceeding 50% of the average QREs for the prior 3 years — simpler and preferred by most companies
- **Effective benefit**: Most companies see an effective credit rate of 6–8% on total qualifying expenses

### Qualified Research Expenses (QREs)
The IRS applies a four-part test to determine qualified research:
1. **Permitted purpose**: Must develop or improve a business component (function, performance, reliability, quality, cost)
2. **Technological in nature**: Must use principles of physical, biological, engineering, or computer science
3. **Elimination of uncertainty**: Must be intended to discover information to eliminate uncertainty about capability, methodology, or design
4. **Process of experimentation**: Must involve evaluation of alternatives through modeling, simulation, prototyping, or testing

**Types of QREs:**
- **Wages** (W-2 employees): For employees who directly perform, directly supervise, or directly support qualified research. Use time-tracking or project allocation to document percentage of time on qualified activities.
- **Supplies**: Materials consumed or destroyed in testing/experimentation (not capitalized equipment)
- **Contract research**: 65% of amounts paid to third-party US contractors performing qualified research
- **Cloud computing costs** (QREs post-2020 IRS guidance): AWS, GCP, Azure costs used for qualified research can qualify when properly documented and linked to qualified research projects

### Startup / Payroll Tax Offset (Section 41(h))
- Startups with <$5M in gross receipts and <5 years of revenue can offset up to **$500,000 per year** in employer payroll taxes (FICA)
- This is critical for pre-profitable companies with no income tax to offset
- Election made on Form 6765 on the tax return
- As of 2023, the limit doubled from $250K to $500K per year

### Section 174 Amortization (Important 2022 Change)
- Prior to 2022: R&D expenses were immediately deductible under Section 174
- Starting in 2022: Domestic R&D costs must be capitalized and amortized over 5 years; foreign R&D over 15 years
- This significantly increases taxable income for R&D-intensive companies in the near term
- Advocacy ongoing to restore immediate deductibility; CFOs should model both scenarios

### State R&D Tax Credits
Most states with income taxes offer their own R&D credits (separate from federal):
- **California**: 15% credit on QREs (no sunset); highly valuable for Bay Area tech companies
- **New York**: 9% credit on QREs for qualified manufacturing and R&D
- **Texas**: 6.25% franchise tax credit on QREs
- **Massachusetts**: 10% credit on QREs
- Combined federal + state credits can approach 20% of total qualifying costs in some states

### Documentation Requirements
- Time-tracking systems linking engineer hours to qualified projects
- Project documentation showing technical uncertainty and experimentation
- Contractor agreements specifying research activities
- Cloud cost allocation reports linking cloud spending to qualified projects
- Maintain contemporaneous documentation — don't reconstruct at year-end

---

## Transfer Pricing for Multinationals

When a tech company operates in multiple countries, transactions between related entities (parent-subsidiary, between subsidiaries) must be priced at arm's length.

### Key Transfer Pricing Methods
- **Comparable Uncontrolled Price (CUP)**: Compare to prices charged in similar transactions between unrelated parties
- **Cost Plus**: Cost of production + markup; common for contract manufacturers and limited-risk entities
- **Resale Price Method**: Start with resale price and subtract an appropriate gross margin; used for distributors
- **Profit Split**: Split combined profits based on relative contributions; used for complex IP arrangements
- **Transactional Net Margin Method (TNMM)**: Compare operating margin of the tested party to comparable companies; most common for tech subsidiaries

### IP Holding Structures
- Multinational tech companies often hold IP in low-tax jurisdictions (Ireland, Netherlands, Singapore)
- OECD BEPS (Base Erosion and Profit Shifting) rules have tightened acceptable structures
- Substance requirements: IP holding entity must have genuine economic substance (real employees, real decisions made locally)
- Consult specialized transfer pricing counsel before establishing any cross-border IP structure

### GILTI and Pillar Two
- **GILTI** (Global Intangible Low-Taxed Income): US minimum tax on offshore profits of US multinationals; effectively imposes ~10.5% US minimum tax on foreign profits
- **OECD Pillar Two (Global Minimum Tax)**: 15% minimum tax on large multinationals (>€750M revenue) effective in many jurisdictions; reduces benefit of traditional low-tax structures

---

## State Nexus and Sales Tax

### Nexus Issues
Economic nexus (post-South Dakota v. Wayfair, 2018): Most states impose sales tax collection requirements on remote sellers exceeding:
- $100,000 in annual sales OR
- 200 transactions into the state (thresholds vary by state)

**SaaS nexus complexity:**
- Some states treat SaaS as a taxable service (New York, Tennessee, Texas)
- Others exempt SaaS (California — for pure SaaS with no tangible personal property)
- Review each state's taxability determination for your specific product
- **Remote employees create income tax and payroll nexus** — even a single employee working from a state may create nexus obligations

### Nexus Management
- Use tax compliance software (Avalara, TaxJar, Vertex) to automate sales tax calculation and filing
- Register in nexus states proactively; penalties for failure to collect are typically the company's (not customer's) responsibility
- Conduct a nexus study annually as headcount and revenue grow into new states

---

## Entity Structure Optimization

### C-Corp vs. Pass-Through
- Venture-backed startups: **C-Corp** (Delaware) is standard and required for most institutional investors
- Pass-through (LLC, S-Corp): beneficial for profitable businesses with immediate distributions; not compatible with preferred stock structures

### Delaware C-Corp Advantages
- Preferred by VCs; well-established corporate law
- Court of Chancery resolves disputes efficiently
- Allows multiple classes of stock (common + preferred)
- Section 1202 QSBS (Qualified Small Business Stock): up to $10M (or 10x basis) in capital gains excluded from federal tax for founders and investors who hold C-Corp stock for 5+ years — potentially enormous tax benefit

### Tax Loss Carryforwards
- Net operating losses (NOLs) from early years can offset future taxable income
- Post-2017: NOLs can be carried forward indefinitely (no 20-year limit) but limited to 80% of taxable income per year
- Acquire companies with NOLs? Section 382 limits NOL utilization post-change-of-control — model carefully
