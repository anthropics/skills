# Procurement & Cost Management

## Vendor Negotiation Strategy

### Negotiation Principles for Tech Companies
- **Never accept the first quote**: SaaS vendors expect negotiation; 15–30% discounts are standard
- **Use year-end leverage**: Vendors close books on calendar quarters; buying on March 31, June 30, September 30, or December 31 extracts maximum discount
- **Annual upfront vs. monthly**: Offer annual prepay in exchange for 15–25% discount
- **Multi-year contracts**: 3-year contract with 5–10% YoY price protection in exchange for discount; avoid locking into price escalators above 5%
- **Compete vendors**: Get 3+ quotes; tell each vendor you are evaluating alternatives — even if you prefer one
- **Benchmark pricing**: Use Vendr, Sastrify, or G2's pricing benchmarks to know market rates before negotiating

### Contract Hygiene
- Auto-renewal clauses: Flag all contracts with auto-renewal provisions; calendar review 90 days before renewal
- Usage true-ups: Audit actual vs. licensed usage quarterly; don't pay for unused seats
- Right-to-audit clause: Negotiate into major contracts; useful for verifying pricing accuracy
- Termination for convenience: Push for 30-day exit clause in long-term contracts; vendors often accept for large deals

### Software Stack Cost Optimization
- Conduct quarterly SaaS audit: inventory all subscriptions, active users, utilization rate
- Tools: Zylo, Torii, Productiv, Cleanshelf — SaaS management platforms that identify waste
- Challenge every tool: Does this solve a problem not solved by an existing tool? What's the ROI?
- Consolidate: Platforms (HubSpot, Salesforce, Slack) offer better pricing for bundled products than point solutions

---

## Cloud Cost Optimization (FinOps)

### FinOps Framework
FinOps (Cloud Financial Management) is a practice that brings together finance, engineering, and operations to optimize cloud spend. The FinOps Foundation defines three phases:
1. **Inform**: Real-time visibility into cloud spend, allocation to teams/products, showback/chargeback
2. **Optimize**: Right-sizing, reserved instances, spot instances, architectural optimization
3. **Operate**: Build cost accountability into engineering culture; continuous optimization

### Key Cloud Cost Levers

**Commitment Discounts (highest ROI):**
- **AWS Reserved Instances / Savings Plans**: 1-year or 3-year commitments for EC2, RDS, Lambda; discounts of 30–60% vs. on-demand
- **GCP Committed Use Discounts**: 1- or 3-year commitments for Compute Engine; 37–55% discount
- **Azure Reserved VM Instances**: 1- or 3-year commitments; 40–72% savings
- Rule: Commit to 60–70% of baseline consumption; keep 30–40% on-demand for flexibility
- Analyze 3-month trailing usage to determine commitment baseline

**Right-Sizing:**
- Identify underutilized instances (CPU consistently <20%, memory <30%)
- Tools: AWS Compute Optimizer, GCP Recommender, Azure Advisor
- Downsize or terminate idle resources; aim to reduce instance waste by 20–30%

**Spot / Preemptible Instances:**
- 60–90% savings vs. on-demand for interruptible workloads
- Suitable for: batch processing, CI/CD pipelines, ML training jobs, data processing
- Not suitable for: production stateful services, databases, customer-facing APIs

**Storage Optimization:**
- Move infrequently accessed data to cold storage (AWS S3 Glacier, GCP Nearline, Azure Archive): 70–80% cheaper
- Delete unattached EBS volumes, snapshots older than retention policy, orphaned load balancers
- Review data transfer costs (egress is expensive): architect to minimize cross-region data movement

**Database Optimization:**
- Use read replicas for read-heavy workloads to reduce primary instance size
- Evaluate serverless database options (Aurora Serverless, AlloyDB Omni) for variable workloads
- Right-size RDS instances; Aurora is typically 30–40% more cost-efficient than multi-AZ RDS at scale

### FinOps KPIs and Metrics
- **Cloud unit cost**: Cloud spend / revenue (or per customer, per transaction) — target YoY improvement
- **Committed spend %**: % of total cloud spend under commitment discounts (target 60–70%)
- **Waste %**: % of spend on idle or underutilized resources (target <15%)
- **Coverage ratio**: % of eligible spend covered by Savings Plans / RIs (target >80% of stable workloads)
- **Forecast accuracy**: Cloud bill forecast vs. actual (target ±10%)

### FinOps Tooling
- **Native**: AWS Cost Explorer, AWS Budgets, GCP Cost Management, Azure Cost Management + Billing
- **Third-party**: CloudZero, Apptio Cloudability, Spot.io, nOps, Kubecost (Kubernetes)
- **Engineering integration**: Tag all resources with team, product, environment; enforce tagging policies via cloud policy frameworks

### Organizational FinOps Model
- Assign cloud cost responsibility to engineering teams (not just finance)
- Monthly cloud cost reviews with engineering leads
- Chargeback or showback to business units
- Set cost budgets per team; alert at 80% and 95% utilization
- Make cloud cost visible in engineer dashboards (Grafana, Datadog) alongside performance metrics

---

## Headcount Cost Modeling

Headcount is typically 60–75% of total operating expense. Accurate headcount modeling is critical.

### Fully-Loaded Cost Per Employee
Fully-loaded cost = Base Salary + Variable Comp + Benefits + Payroll Tax + Equipment + Software + Office

**Typical fully-loaded multipliers by region:**
- US (Bay Area, NYC): 1.25–1.35x of base salary
- US (other regions): 1.20–1.28x
- UK / Western Europe: 1.25–1.30x (higher employer NI contributions)
- India, Eastern Europe: 1.15–1.20x (lower benefits cost, still significant employer taxes)

**Example**: $150K base salary engineer in San Francisco = ~$195K–$210K fully-loaded cost

### Headcount Plan Best Practices
- Maintain a headcount roster in your financial model: role, department, start date, base, variable, fully-loaded cost, open vs. filled
- Model hiring timing precisely: a hire in April costs 9/12 of annual fully-loaded cost (not a full year)
- Backfill planning: assume 60–90 day average time-to-fill; model accordingly
- Plan for terminations: severance cost (typically 1–3 months salary for involuntary), benefits continuation (COBRA), outplacement
- Benchmark compensation: Levels.fyi, Radford/Mercer, Carta Total Comp for equity benchmarking
