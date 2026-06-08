# Financial Management for Tech Leaders

## Reading the P&L (Profit & Loss Statement)

The P&L (also called the Income Statement) shows revenue, costs, and profit/loss over a time period. Every tech leader should be able to read one.

### P&L Structure
```
Revenue                          $10,000,000
  - Cost of Revenue (COGS)       ($3,000,000)
Gross Profit                     $7,000,000   [Gross Margin: 70%]
  - Research & Development (R&D) ($2,500,000)  ← Where most eng is
  - Sales & Marketing            ($2,000,000)
  - General & Administrative     ($500,000)
Operating Income (EBIT)          $2,000,000   [Operating Margin: 20%]
  - Interest / Other             ($100,000)
Net Income                       $1,900,000
```

**Where engineering appears**:
- In SaaS companies, engineering typically shows up in **R&D** (product development teams) and/or **Cost of Revenue** (infrastructure, DevOps, SRE)
- Infrastructure/cloud costs are often in COGS
- Software development (product, features) is typically in R&D

**Gross margin** is a key SaaS health metric. Software companies typically target 70-80% gross margin. If yours is 40%, you have high infrastructure or delivery costs.

## Cost Centers vs. Profit Centers

### The Distinction
- **Cost center**: A business unit that incurs costs but doesn't directly generate revenue. Measured by budget adherence and cost efficiency. Example: traditional IT departments, internal tools teams.
- **Profit center**: A business unit with direct revenue accountability. Measured by P&L. Example: a product team owning a revenue-generating product line.

### Engineering's Position

In most tech companies, engineering is treated as a cost center (R&D budget). But the framing matters enormously:

**Cost center framing**: Engineering "costs money." Cuts come first in downturns. Investment is hard to justify without ROI analysis. EMs fight for budget.

**Profit center framing**: Engineering creates revenue through product. Investment in engineering is investment in growth. Engineering is measured on outcomes (user growth, retention, conversion) not just budget.

**Recommendation**: Even if accounting treats engineering as a cost center, run internal narratives as a profit center. Tie engineering metrics to business outcomes. "This 3-engineer team owns checkout — improving conversion by 0.5% generated $400K in annual revenue."

**During layoffs**: Engineering teams perceived as cost centers are cut more aggressively than those perceived as revenue generators. Teams that can articulate their revenue connection are safer.

## Headcount Planning

### The Headcount Plan
A quarterly or annual model of how many people you plan to hire, when, at what cost, and toward what goals.

**Components**:
1. Current headcount by team and level
2. Planned hires (new roles vs. backfills)
3. Timing: when do you need them onboarded to have impact?
4. Cost model: salary + benefits + recruiting cost
5. Net headcount: accounting for expected attrition

**Critical rule**: A hire needed in Q3 should have the job req open in Q1. Recruiting takes 6-12 weeks for a typical engineer role; then add onboarding and ramp time. Headcount planning should be 2 quarters ahead of when you need the productivity.

### Attrition Modeling
Plan for attrition; don't be surprised by it. Healthy attrition for a tech company is 10-15% annually. Above 20% is a warning sign. Below 5% may indicate people feel trapped (often preceding a mass exit).

**Gross headcount growth vs. net headcount growth**: If you hire 20 people and 8 leave, your net is +12. Many leaders plan for gross hiring without modeling attrition, then are surprised that headcount barely moved.

### Headcount Approval
Most companies above 50 people require headcount approval. To get approval, you need:
- Business justification: what outcome does this hire enable?
- Financial model: fully-loaded cost, expected return
- Timing: when needed, ramp timeline
- Alternative analysis: why not contractors, freelancers, automation?

**Political reality**: Headcount is the most competitive resource in any organization. Frame requests in terms of revenue impact, risk mitigation, or strategic capability — not "we're busy."

## Fully-Loaded Engineer Cost (Detailed)

### Full Cost Model (US, 2024-2025)

**Senior Software Engineer at $165K base**:

| Cost Component | Annual | Notes |
|---------------|--------|-------|
| Base salary | $165,000 | |
| Benefits (28%) | $46,200 | Health, dental, vision, 401K match, disability |
| Payroll taxes | $12,623 | FICA, FUTA, SUTA |
| Equipment (amortized) | $2,500 | Laptop ($3,500 over 3 years) + peripherals |
| Software licenses | $2,400 | $200/mo for GitHub, Slack, cloud tools, IDEs |
| Training/conference | $3,000 | Annual professional development |
| Office/remote stipend | $1,500 | WFH stipend or allocated office space |
| Recruiting (amortized) | $4,125 | External recruiter 25% → $41K amortized over 3 years |
| Management overhead | $8,250 | Allocated EM/HR/finance time (5% of salary) |
| **Total fully-loaded** | **~$245,600** | |

**Monthly: ~$20,500**

**Rule of thumb**: Fully-loaded cost = 1.4-1.6x base salary for US employees.

### Ramp Cost
A new engineer isn't fully productive for 3-6 months. During ramp:
- Months 1-3: 20-40% productivity (learning systems, codebase, culture)
- Months 4-6: 60-80% productivity
- Month 7+: Full productivity expected

Ramp cost = lost productivity during ramp period. For a $165K engineer, that's approximately $20-40K in opportunity cost during the first 6 months.

**Total year-one cost**: Salary + benefits + recruiting + equipment + ramp = approximately $280-310K for a senior engineer in year 1.

### Attrition and Replacement Cost
- Average attrition cost: 50-200% of annual salary
- For a $165K senior engineer: $82K-$330K replacement cost
- This is why even "expensive" retention investments (higher salary, extra equity, professional development) have strong ROI

### Contractor vs. FTE Analysis
Contractors cost 1.5-2x hourly rate of an equivalent FTE (no benefits cost to employer, but billing rate premiums). They are cost-effective for:
- Short-duration projects (under 6 months)
- Highly specialized skills needed temporarily
- Burst capacity during product launches

Contractors are cost-negative for:
- Work that needs institutional knowledge (domain understanding takes months to build)
- Ongoing, steady-state work (pay the 1.5-2x premium forever)
- Work where security/confidentiality concerns exist

## ROI Analysis for Technology Investments

### Build vs. Buy ROI
```
Build ROI = (Benefits - Build Cost - Ongoing Maintenance Cost) / Build Cost

Buy ROI = (Benefits - License Cost - Integration Cost - Switching Risk) / (License + Integration)
```

**Common errors in ROI analysis**:
- Forgetting ongoing maintenance (bug fixes, upgrades, security patches, on-call)
- Forgetting integration cost for "off-the-shelf" solutions
- Not modeling total cost of ownership over 3-5 years, just year 1 cost
- Not including opportunity cost of engineering time spent building vs. other work

### Make vs. Buy Decision Example
Scenario: Should we build our own internal analytics dashboard or buy Tableau?

**Build**:
- Engineering cost: 2 engineers, 6 months = $120K
- Ongoing maintenance: 0.25 engineer FTE = $40K/year
- Custom integration: built-in
- 3-year TCO: $120K + (3 × $40K) = $240K

**Buy Tableau**:
- License: $70/user/month × 50 users = $42K/year
- Integration/setup: 1 engineer, 1 month = $20K
- Ongoing admin: 0.05 FTE = $8K/year
- 3-year TCO: $20K + (3 × $50K) = $170K

Decision: Buy, unless the custom integration provides unique competitive value.

## Budget Planning and Management

### Annual Budget Cycle

Typical timeline:
- August-September: Bottom-up planning (EMs submit headcount and program requests)
- October: Finance consolidates, compares to targets
- November: Negotiation and scenario modeling
- December: Budget finalized
- January: Approved headcount opens

**Common traps**:
- Use-it-or-lose-it budgets create year-end spending sprees. Advocate for rollover policies.
- Headcount approved but not filled still shows as budget "used" in forecasts — track this separately
- Cloud costs scale with usage unpredictably — include a variance buffer (10-15%) in cloud budget

### FinOps for Engineering Leaders

Cloud infrastructure cost is often one of the top 3 costs for a tech company, alongside people and office.

**Key FinOps principles**:
- **Cost visibility by team**: Every team should see their cloud cost and be accountable for it
- **Reserved instances / savings plans**: Commit to usage for 1-3 years for 30-60% discounts on predictable workloads
- **Right-sizing**: Periodically audit whether instances are appropriately sized (over-provisioned is common)
- **Spot instances**: For fault-tolerant workloads (batch processing, ML training), spot instances reduce cost by 60-90%

**Benchmark**: Cloud cost as % of revenue in SaaS companies typically targets 5-15%. Above 20% usually indicates either early stage infrastructure investment or a cost structure problem.

## Sources
- *High Output Management* — Andy Grove (1983), Random House
- Pragmatic Engineer newsletter — "Profit Centers vs Cost Centers at Tech Companies"
- LogRocket Blog — "Profit center vs. cost center: How company structure affects engineering"
- DontHireDevs.com — "Real Cost of Hiring a Software Engineer 2026"
- GlenCoyne.com — "Fully Loaded Employee Cost Analysis: Practical Guide"
- VanHack Blog — "How Much Does It Cost to Hire a Software Developer in 2025?"
- Koblesystems.com — P&L / Income Statement reference
- Crema.us — "Measuring the ROI of Your Software Initiatives: 2025 Guide"
