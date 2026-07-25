# SaaS Management Canon

SaaS sprawl is the dominant indirect-spend category for tech companies and the #1 driver of spend growth in scaleups. This file curates the research on SaaS portfolio management — distinct from generic procurement because SaaS has unique characteristics: per-seat pricing, auto-renew defaults, shadow-IT entry, and a viable replacement every 18 months.

---

## Sources (≥ 7)

### 1. Productiv — *State of SaaS* (annual report)

Productiv's annual benchmark across hundreds of enterprises is the most-cited SaaS sprawl data source. Key findings (most recent waves):

- **The median mid-stage company has 130-250 distinct SaaS subscriptions**, of which 30-50% are used by < 10% of licensed users.
- **License utilization median is 47%** — meaning more than half of SaaS spend buys seats nobody logs into.
- **47% of SaaS spend is shadow IT** (purchased outside the procurement process). The skill's anti-pattern list calls this out: "treat shadow IT spend as marketing's problem — it isn't."
- **Renewal is the highest-leverage moment**: 67% of SaaS purchases auto-renew without review.

Use when: framing the size of the prize for a SaaS audit.

### 2. Zylo — *SaaS Management Index* and annual benchmarks

Zylo's research focuses on SaaS economics:

- **SaaS spend grows ~30% YoY in scaleups** vs. ~10% headcount growth — meaning per-employee SaaS cost is growing.
- **Duplicate-function clusters** are extraordinarily common: most enterprises have 3-5 monitoring tools, 2-3 expense platforms, 4+ email-marketing tools. This skill's clustering logic is calibrated to Zylo's observed cluster patterns.
- **Lowest-hanging consolidation savings** are in marketing tech (often 30-40% redundancy) and developer tools.

### 3. Vendr — *SaaS Buyers Report* and pricing intelligence

Vendr's procurement-negotiation research is the practitioner's playbook for SaaS pricing leverage:

- **Median SaaS discount achievable** ranges 10-40% off list, driven by: term length, payment terms, multi-year commit, and **renewal-date timing**. Vendr's data confirms that vendors discount more aggressively at quarter-end and year-end.
- **The "MSA + Order Form" pattern** lets you re-negotiate per-order pricing without re-opening the master agreement — important for SaaS where the master may have unfavorable renewal terms locked in.

### 4. Tropic — *SaaS Cost Index* and category benchmarks

Tropic's per-category pricing benchmarks are public:

- **Per-seat pricing benchmarks** by category (CRM, ATS, HRIS, monitoring, etc.) give you the BATNA when negotiating. If you're paying 2× the Tropic median for Salesforce seats, you have leverage.
- **Tropic's analysis of consolidation success rates** shows that 60%+ of attempted SaaS consolidations fail to capture the theoretical savings, primarily due to (a) underestimated training cost, (b) loss of feature parity, (c) tier-1 single-source operational risk.

### 5. BetterCloud — *State of SaaSOps* (annual)

BetterCloud's operations research focuses on the lifecycle (onboarding → utilization → offboarding):

- **The offboarding gap:** when a SaaS tool is replaced, the old tool's licenses, data, and access often linger for 3-12 months — pure waste. SaaS audit must include an offboarding completeness check.
- **Sub-$5k SaaS purchases** are the dominant entry point for sprawl: they typically skip procurement review entirely and self-renew before anyone notices.

### 6. Gartner — *Magic Quadrant for SaaS Management Platforms (SMP)*

Gartner's SMP MQ defines the tooling category:

- **SMP capabilities:** discovery (find shadow SaaS), inventory (catalog all subscriptions), license utilization (who's actually logging in), renewal management (calendar + alerts), spend analytics (Pareto + YoY).
- The skill's deliverables (categorized spend, consolidation plan, renewal cluster analysis) are the artifacts an SMP would generate — useful when the user doesn't have an SMP licensed yet.

### 7. Tomasz Tunguz (Theory Ventures) — Long-running blog on SaaS economics

Tunguz's analysis of SaaS sprawl from the buyer side:

- **The "consumption shift"** from seat-based to usage-based pricing is changing the rationalization math: usage-based tools are harder to consolidate because their cost scales with workload, not seat count.
- **Long-tail SaaS** (the bottom 50% of subscriptions by spend) is where shadow IT lives. Killing 30 tools that cost $200/year each is psychologically harder than consolidating 3 tools that cost $90k/year each, but the operational simplification is comparable.

### 8. Patrick Campbell / ProfitWell — SaaS unit economics research

Campbell's research focuses on the seller side but the buyer-side implications are direct:

- **Annual contracts vs. monthly:** annual gives the vendor cash-flow stability and the buyer 10-30% discount, BUT it also locks in pricing and makes it harder to walk away mid-cycle. The skill's renewal-date clustering analysis flags this trade-off.
- **The "price-sensitivity range"** for SaaS pricing is wider than commonly believed — vendors will discount more than buyers expect when shown a credible alternative and a hard renewal deadline.

### 9. Bain — SaaS portfolio research (multi-year)

Bain's research on enterprise SaaS portfolios complements the practitioner sources:

- **Enterprise SaaS portfolios grow to 250-500 subscriptions** at the Fortune 1000 scale, with a power-law spend distribution: top 10 vendors capture 50-60% of spend.
- **The "category overlap"** finding (one vendor in multiple categories, e.g., Microsoft 365 spans productivity + identity + storage) is why categorizing by line-item description matters more than categorizing by vendor.

### 10. Forrester — *SaaS Portfolio Management* research

Forrester's research formalizes the SaaS portfolio governance question:

- **Three-tier governance model:** enterprise SaaS (procurement-led), departmental SaaS (FinOps-led), individual SaaS (expense-led). Each tier has different approval thresholds and review cadences.
- **Quarterly SaaS reviews** are the recommended cadence for mid-stage companies; annual is too slow when 30% of subscriptions are < 12 months old.

---

## How this skill applies the canon

- **Spend categorizer's category map** includes the duplicate-function clusters Zylo and Productiv observe: Monitoring, Expense, Email Marketing, Analytics, Security Tooling.
- **Supplier consolidation's tier-1 single-source refusal** is calibrated to Tropic and Vendr's research on failed consolidations.
- **Renewal-cluster analysis** is informed by IACCM and Vendr research on negotiation timing.
- **The sub-$5k approval anti-pattern** comes from BetterCloud and Productiv shadow-IT research.
