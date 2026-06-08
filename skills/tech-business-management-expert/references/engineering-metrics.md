# Engineering Metrics

## Why Metrics Matter (and Why They Fail)

Goodhart's Law: "When a measure becomes a target, it ceases to be a good measure." Engineering teams optimize for what they're measured on. Bad metrics produce bad behavior:
- Measuring lines of code → incentivizes verbose code
- Measuring story points → incentivizes estimation inflation
- Measuring number of tickets closed → incentivizes trivial tickets

Good metrics measure outcomes (what value was delivered) and system health (how sustainably is the team operating), not activity or output.

## DORA Metrics

From Nicole Forsgren, Jez Humble, and Gene Kim's research (*Accelerate*, 2018) and ongoing State of DevOps reports. DORA (DevOps Research and Assessment) is the most empirically validated engineering performance framework.

**Four Core Metrics** (four keys):

### 1. Deployment Frequency
How often does the team deploy to production?

| Performance Tier | Benchmark |
|-----------------|-----------|
| Elite | Multiple times per day |
| High | Once per week to once per day |
| Medium | Once per month to once per week |
| Low | Less than once per month |

**Why it matters**: High deployment frequency correlates with faster feedback, smaller risk per deployment, and higher engineering satisfaction. Enables experimentation.

**How to improve**: Invest in CI/CD automation. Move to trunk-based development. Adopt feature flags to decouple deploy from release. Break down large changes into smaller increments.

### 2. Lead Time for Changes
Time from first commit to code running in production.

| Performance Tier | Benchmark |
|-----------------|-----------|
| Elite | Less than one hour |
| High | One day to one week |
| Medium | One week to one month |
| Low | More than one month |

**Why it matters**: Lead time is the core measure of delivery speed. Long lead times indicate bottlenecks in code review, testing, approval processes, or deployment pipelines.

**How to improve**: Automate testing. Reduce manual approval gates. Improve code review turnaround (target < 24 hours). Invest in fast CI/CD pipelines.

### 3. Change Failure Rate
Percentage of changes to production that result in incidents, rollbacks, or emergency fixes.

| Performance Tier | Benchmark |
|-----------------|-----------|
| Elite | 0-5% |
| High | 0-15% |
| Medium | 16-30% |
| Low | 46-60% |

**Why it matters**: Balances speed against quality. Teams that deploy very frequently with high change failure rates are just shipping bugs faster.

**How to improve**: Improve automated test coverage. Implement canary releases / progressive rollouts. Add pre-deployment smoke tests. Improve monitoring and alerting so failures are caught quickly.

**2024 DORA anomaly**: For the first time, the medium cluster recorded a lower change failure rate than the high cluster. This reflects that these values are not fixed benchmarks — they shift based on survey respondents each year.

### 4. Failed Deployment Recovery Time (MTTR)
Time to restore service after a deployment failure (formerly "Mean Time to Recovery").

| Performance Tier | Benchmark |
|-----------------|-----------|
| Elite | Less than one hour |
| High | Less than one day |
| Medium | Less than one day |
| Low | One week to one month |

**Why it matters**: No matter how good your change failure rate, incidents will happen. Recovery time is the measure of resilience.

**How to improve**: Invest in observability (monitoring, alerting, tracing). Create clear incident response runbooks. Practice incident response (game days). Enable fast rollback (one-click deploy reversal).

### DORA Benchmark Data (2024)
Elite performers deploy **182x more frequently** than low performers, have **127x faster lead times**, **8x lower change failure rates**, and recover **2,293x faster**.

The 2024 State of DevOps survey covered 39,000+ professionals globally. ~19% of teams qualified as elite performers. Key finding: AI adoption is broadly positive for software development, though impact on delivery metrics at the team level is mixed — a 25% increase in AI adoption was associated with some decrease in delivery throughput.

**Critical DORA finding** (from *Accelerate*): Technical practices alone are insufficient. Culture — psychological safety, learning from failures, cross-functional collaboration — is equally important. Teams with high psychological safety consistently outperform on all four DORA metrics.

## SPACE Framework

Developed by Nicole Forsgren, Margaret-Anne Storey, et al. (2021). Addresses limitations of DORA by capturing the human dimensions of developer productivity.

Five dimensions (SPACE acronym):

### S — Satisfaction and Well-being
- Developer satisfaction with their work and tools
- Feeling of accomplishment
- Sense of belonging on the team
- Burnout indicators (attrition, disengagement)

**How to measure**: Developer surveys (quarterly or semi-annual). eNPS (Engineer Net Promoter Score). 1-on-1 pulse checks. Attrition rate.

### P — Performance
- Quality of output (bugs introduced, code review outcomes)
- Customer satisfaction related to engineering quality
- Reliability metrics (incident rates, SLO compliance)

**How to measure**: Bug escape rate, DORA change failure rate, SLO attainment, customer satisfaction surveys correlated with engineering releases.

### A — Activity
- Volume of work done (a proxy, not a goal)
- Code commits, PRs opened/merged, tickets completed
- Design docs, code reviews completed

**Warning**: Activity is the most dangerous dimension to over-optimize. High activity with low satisfaction and low performance is a failure mode. Track it, but don't target it.

### C — Communication and Collaboration
- Integration of work across teams
- Documentation quality
- Effectiveness of code reviews as knowledge transfer
- Cross-team coordination

**How to measure**: Contribution patterns (do PRs cross teams?), documentation coverage, time-to-response in code reviews, retrospective feedback.

### E — Efficiency and Flow
- Uninterrupted time for deep work
- Friction in the development process (build times, flaky tests, environment instability)
- Ability to complete work without unnecessary delays

**How to measure**: Build times, flaky test rate, environment uptime, engineering survey questions about interruption frequency, PR cycle time.

### SPACE vs. DORA

| Aspect | DORA | SPACE |
|--------|------|-------|
| Focus | Delivery performance | Holistic developer productivity |
| Origin | Research + survey data | Research + practitioner input |
| Dimensions | 4 metrics | 5 dimensions |
| Strength | Measurable, benchmarkable | Captures human factors |
| Weakness | Misses human/quality dimensions | Harder to benchmark |

**Best practice**: Use DORA metrics for delivery performance measurement. Use SPACE dimensions to design your measurement system and ensure you're not over-indexing on delivery at the expense of developer well-being and quality.

## Flow Metrics

From *Project to Product* (Mik Kersten, 2018) and Value Stream Management. Flow metrics capture the state of work as it moves through your value stream.

### Four Key Flow Metrics

**1. Flow Velocity**
Number of work items (features, defects, risks, debt) completed per time period.
- Use: Is throughput increasing or decreasing?
- Don't conflate with story points — items are items

**2. Flow Time (Cycle Time)**
Elapsed time from when work starts ("in progress") to when it's done ("done").
- Shorter cycle time = faster feedback, lower WIP, less context switching
- Target: measure at the P85 (85th percentile), not average

**3. Flow Load (WIP — Work in Progress)**
Number of items currently in active work.
- High WIP = multitasking, slow completion, hidden bottlenecks
- WIP limits (Kanban) force prioritization and expose constraints
- Rule of thumb: WIP per engineer should be ≤ 3 items; whole team WIP should be ≤ 2x team size

**4. Flow Distribution**
Ratio of work types: Features / Bugs / Risk / Debt.
- Healthy distribution for most product teams: ~60% features, 20% debt, 10% bugs, 10% risk/infrastructure
- Imbalanced distribution is a diagnostic: high debt = velocity is suffering; high bugs = quality problems; all risk = behind on compliance/security

### Value Stream Mapping
A technique for visualizing the flow of work from idea to customer outcome:
1. Map each step in the development process (ideation → design → dev → review → QA → deploy → monitor)
2. Measure: time spent doing work (process time) vs. time waiting (lead time)
3. Calculate Flow Efficiency = Process Time / Total Lead Time
4. Typically, Flow Efficiency in software is 10-30% — most time is waiting, not working

**What the mapping reveals**: Bottlenecks, handoff delays, approval gates, environment wait times. These are where to invest to accelerate delivery.

## Dashboard Design for Engineering Leaders

### Principles
1. **Context over data**: Show metrics alongside their targets and trends — a number without context is meaningless
2. **Leading vs. lagging indicators**: Show both; lagging (past performance) tells you where you are, leading (early signals) tells you where you're going
3. **Audience-appropriate views**: Engineering team view (tactical, detailed) vs. executive view (strategic, aggregated)
4. **Fewer, better metrics**: A dashboard with 20 metrics causes nothing to improve. Pick 5-8 that genuinely drive behavior change.

### Recommended Engineering Dashboard Stack

**Engineering Team Dashboard**:
- Deployment frequency (this week vs. 4-week average)
- Lead time for changes (P50 and P85)
- Change failure rate (rolling 4 weeks)
- MTTR (rolling 4 weeks)
- On-call load: pages per rotation
- PR cycle time: open to merge
- Sprint velocity vs. commitment

**Executive Engineering Dashboard**:
- DORA performance tier trend (quarter over quarter)
- Engineering headcount and open positions
- SLO attainment (% of services meeting their SLOs)
- Tech debt backlog trend (growing or shrinking?)
- P1/P2 incident count trend
- Build health: CI pass rate, flaky test rate

### Tools for Engineering Metrics
- **LinearB**: DORA metrics, PR analytics, planning accuracy
- **Swarmia**: Engineering KPIs, team health, code review metrics
- **DX (GetDX)**: DORA + SPACE, developer experience surveys
- **Jellyfish**: Engineering investment analytics, work visibility
- **Datadog / Grafana**: Custom dashboards for operational metrics

## Common Metrics Mistakes

1. **Measuring only outputs, not outcomes**: "We shipped 24 features this quarter" is meaningless without "and customers used them in ways that drove our retention goal."

2. **Using metrics to evaluate individuals**: DORA metrics are team metrics. Using deployment frequency to evaluate an individual engineer creates gaming and destroys collaboration.

3. **Setting fixed targets without context**: An L1 team (just formed) should not be compared to an L3 team (high-performing) on DORA benchmarks. Measure improvement, not absolute position.

4. **Metric sprawl**: Tracking everything ≠ managing anything. Choose metrics tied to your current business problem.

5. **Lagging-only dashboards**: If you can only see what happened last quarter, you can't prevent what's about to happen. Combine leading indicators (PR cycle time trending up → deployment frequency will drop) with lagging indicators.

## Sources
- *Accelerate: The Science of Lean Software and DevOps* — Nicole Forsgren, Jez Humble, Gene Kim (2018)
- DORA State of DevOps Report 2024 (39,000+ respondents, Google/DORA)
- dora.dev/guides/dora-metrics/ — Official DORA metrics documentation
- LinearB Blog — "SPACE Metrics Framework for Developers Explained (2025 Edition)"
- GetDX.com — "What are Flow Metrics and How Do You Use Them?" (2024)
- Swarmia Blog — "Your practical guide to DORA metrics"
- Octopus Deploy — "Understanding the 4 DORA Metrics and Top Findings from 2024/25 DORA Report"
- Scrum.org — "4 Key Flow Metrics and How to Use Them in Scrum's Events"
- *Project to Product* — Mik Kersten (2018), IT Revolution Press
