# DevOps / SRE Practices

## SRE vs. DevOps: The Distinction

**DevOps** is a culture and set of practices for breaking down barriers between development and operations teams. It's a philosophy, not a role.

**SRE (Site Reliability Engineering)** is Google's implementation of DevOps principles into a concrete engineering discipline. Coined by Ben Treynor Sloss at Google (~2003). The key insight: SRE uses software engineering to solve operations problems.

**Core SRE thesis**: "Hope is not a strategy." Reliability is a product feature, not an afterthought. SREs apply engineering rigor (measurement, experimentation, automation) to the operational domain.

## The SLO/SLI/SLA Framework

### SLI (Service Level Indicator)
A quantitative measure of service behavior. The thing you actually measure.

Examples:
- Request success rate: `(successful requests / total requests) * 100`
- Latency: "95th percentile of request latency"
- Availability: "Percentage of minutes the service responded to health checks"
- Throughput: "Requests processed per second"

**Good SLIs** are: measurable, correlated with user experience, not easily gamed.

### SLO (Service Level Objective)
A target value for an SLI over a time window. Your internal reliability goal.

Examples:
- "99.9% of requests succeed over a rolling 30-day window"
- "95th percentile latency < 200ms for 99.5% of days"
- "Service available for 99.95% of each calendar month"

**Critical rule**: SLOs should be set based on what users actually care about, verified through user research or support data — not what's technically achievable.

**Error budget**: Derived from the SLO. If your SLO is 99.9% availability, your error budget is 0.1% of time — about 43.8 minutes/month. When you've spent your error budget, you stop shipping new features and focus on reliability.

### SLA (Service Level Agreement)
A contractual commitment to customers, with financial or legal penalties for breach. External-facing. Usually more conservative than internal SLOs (to give a buffer).

**SRE teams own internal SLOs. Business/legal/commercial teams own SLAs.** Engineering should not be making SLA commitments directly to customers.

### Hierarchy
```
SLA (external contract, stricter on paper)
  ↓ internal target with buffer
SLO (internal reliability goal)
  ↑ measured by
SLI (the actual metric)
```

## Error Budgets

The error budget is the most powerful concept in SRE for balancing velocity and reliability.

**How it works**:
1. Set SLOs (e.g., 99.9% availability)
2. Calculate error budget (e.g., 43.8 min/month of allowed downtime)
3. Track budget consumption in real time
4. When budget is nearly exhausted: freeze non-reliability features, focus on toil reduction and reliability improvements
5. When budget is healthy: accelerate velocity, experiment, take more risks

**Error budget policy**: The formal agreement between product and engineering about what happens when budget is consumed. Must be written down and agreed to in advance, not negotiated during an incident.

## Incident Management

### Severity Levels (typical)
| Level | Impact | Response SLA |
|-------|--------|-------------|
| P0/SEV1 | Complete service outage | Immediate, all hands |
| P1/SEV2 | Major feature broken, significant user impact | < 30 minutes |
| P2/SEV3 | Partial degradation, workaround exists | < 2 hours |
| P3/SEV4 | Minor issue, small % of users | < 24 hours |

### Incident Response Process
1. **Detect**: Alerting fires (PagerDuty, OpsGenie) or user report
2. **Declare**: On-call engineer declares incident, opens incident channel, assigns incident commander (IC)
3. **Communicate**: IC sends initial status to stakeholders ("We are aware of X, investigating, next update in 15 min")
4. **Investigate**: Technical responders dig in; IC manages communication, not technical work
5. **Mitigate**: Stop the bleeding — rollback, feature flag off, traffic reroute. Mitigation ≠ root cause fix.
6. **Resolve**: Service restored to normal
7. **Postmortem**: Within 48-72 hours, conduct blameless review

**Incident Commander (IC) role**: Does not do technical work during the incident. Manages communication, coordinates responders, tracks actions, makes call to escalate. This separation is critical — the best debugger becomes a poor IC.

### On-Call Rotations
- **Primary + secondary**: Primary responds first, secondary escalates if primary is unavailable
- **Follow-the-sun**: Different engineers cover different timezones, avoiding 3am pages for all
- **Rotation frequency**: Weekly rotations are standard. Too short = no context. Too long = burnout.
- **On-call compensation**: Should be paid (cash or comp time). On-call without compensation drives attrition.

**On-call health signals**:
- A healthy on-call is <2 pages/shift that require waking someone up
- If on-call averages >5 pages/week, invest in alerting cleanup and automation
- Track: time spent on-call, pages per rotation, sleep interruptions

### Toil
Google SRE definition: "Manual, repetitive, automatable work that scales linearly with service growth and provides no enduring value."

Toil examples: manually restarting services, manually adjusting config files, manually provisioning accounts, one-time database fixes.

**Guideline**: SRE teams should spend no more than 50% of their time on toil. If you're above 50%, you're not doing SRE — you're doing traditional ops with a different name. The 50% of non-toil time should go to engineering work that eliminates future toil.

## Blameless Postmortems

### What "Blameless" Actually Means
Blameless does NOT mean "no consequences" or "anything goes." It means: assume everyone involved acted with good intent on the best information available at the time. The goal is to learn and fix systems, not to find scapegoats.

**Why blamelessness works**: When people fear blame, they hide information during incidents and postmortems. Hidden information = missed learning = repeat incidents. Blamelessness creates information flow.

### Postmortem Structure (Google's standard template)
1. **Title and Date**
2. **Incident Summary**: What happened, when, how long, who was impacted
3. **Timeline**: Chronological record of what was observed and done (NOT who did it)
4. **Impact**: Quantified — X% of users affected, $Y revenue impact, Z minutes of downtime
5. **Root Cause(s)**: Usually multiple contributing factors (use "Five Whys" to dig deeper)
6. **Contributing Factors**: What in the system/process made this worse or possible?
7. **What Went Well**: Genuinely note what worked — detection speed, response coordination, etc.
8. **Action Items**: Specific, owned, time-bounded improvements. Not "be more careful."
9. **Lessons Learned**: What would others learn from this?

### Five Whys Example
Problem: The API returned errors.
- Why? The database connection pool was exhausted.
- Why? A slow query caused connections to pile up.
- Why? A missing index on a new table was added in last night's deploy.
- Why? Code review didn't catch the missing index.
- Why? No automated check exists for missing indexes on new migrations.

Root cause: Absence of automated migration validation. Action: add migration linter to CI pipeline.

**Warning**: Five Whys should lead to system fixes, not "human error" as the final answer. "Human error" is always a symptom; the root cause is why the human was in a position to make that error.

### Postmortem Anti-Patterns
- Writing the postmortem without the people who were in the incident
- Action items that say "be more careful" or "train engineers" without specific, measurable steps
- Blaming a vendor without asking "why do we depend on them this way?"
- Not tracking whether action items were actually completed

### Postmortem Cadence
- Conduct within 48-72 hours while memory is fresh
- Share broadly — postmortems are a learning artifact for the whole organization, not just the team
- Review closed action items 4-6 weeks later: were they actually done?

## Change Management

**Change failure rate** (DORA): What percentage of deployments cause incidents or require rollbacks. Elite performers: <5%. This requires investment in automated testing, feature flags, and deployment practices.

### Feature Flags
Allow deploying code without activating it. Decouple deployment from release. Benefits:
- Dark launch: deploy to production but off by default
- Canary release: enable for 1% of users, watch metrics, then expand
- Kill switch: instantly disable a feature without a redeploy
- A/B testing: route users to different implementations

**Tools**: LaunchDarkly, Unleash (open source), Flipt, AWS feature flags, Split.io

### Deployment Strategies
- **Blue/green**: Two identical environments; switch traffic instantly. Fast rollback, expensive (double infra).
- **Canary**: Gradual rollout — 1% → 10% → 50% → 100% with checks between steps
- **Rolling**: Replace instances one by one. Good for stateless services.
- **Feature flags**: Recommended for most feature-level changes regardless of deployment strategy

## AI in Incident Response (2024-2025)

Emerging capability: LLMs integrated into incident response workflows:
- Auto-generate first-draft postmortems from CloudWatch/Datadog log sequences
- Reconstruct incident timelines from log aggregation
- Suggest probable root causes from pattern matching across historical incidents
- Summarize Slack incident channel into status updates

Tools: PagerDuty AI, incident.io AI features, Datadog Watchdog, custom LLM pipelines.

**Caution**: AI-generated postmortems still need human validation. The "why" analysis (root cause, contributing factors) requires human judgment that AI frequently gets wrong.

## Sources
- *Site Reliability Engineering* — Google SRE Book (free at sre.google)
- *The Site Reliability Workbook* — Google (sre.google/workbook)
- incident.io Blog — SRE Postmortem Best Practices (2024)
- DORA State of DevOps Report 2024 (39,000+ respondents)
- PagerDuty Incident Management documentation
- Nerd Level Tech, "Mastering SRE Practices: A Complete 2025 Guide"
- USENIX SecSRE research (2024)
