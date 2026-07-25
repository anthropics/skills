# Production Discipline — The Decision: "Can our team operate production safely as it scales?"

This reference answers exactly one decision: **what's our production operating model, and is it ready for the next stage of growth?**

## The Four Pillars

Production discipline rests on four interdependent practices. Weakness in any one breaks the others.

1. **On-call rotation:** broad enough to avoid burnout; clear escalation paths
2. **Incident response:** runbooks, severity definitions, blameless postmortems
3. **Deployment cadence:** continuous OR scheduled; surprises kill teams
4. **SLO discipline:** every customer-facing service has documented SLOs + error budgets

## Pillar 1: On-Call Rotation

**The rule:** ≥ 6 people per rotation, with primary + secondary.

**Why 6:**
- Below 6, burnout accelerates exponentially (per Google SRE Workbook research)
- 6 people = on-call once every 6 weeks per person — sustainable
- Primary + secondary ensures coverage during sleep / vacation / illness

**Rotation patterns:**

- **Weekly handoff (most common):** primary changes every Monday at 9am
- **Daily handoff (Google SRE):** primary changes every day; secondary covers full week
- **Hour-based (rare):** for very large teams or 24/7 critical systems

**Compensation:**

- **On-call pay:** flat stipend OR hourly OR comp time off (varies by company)
- **Comp time off:** 1 day off per on-call week, accrued (good for retention)
- **Anti-pattern:** salary-includes-on-call without explicit compensation → drives attrition

**Burnout signals to watch:**

- Same person paged 3+ times in a week
- Pages outside business hours > 50% (system is broken, not on-call)
- Engineer requests to leave rotation
- High MTTR despite experienced rotation (incidents harder than people can handle)

## Pillar 2: Incident Response

**Severity definitions (standard 4-tier):**

| Severity | Definition | Response |
|---|---|---|
| SEV-1 | Customer-facing outage affecting all users; data loss | All-hands; CEO notified within 1h |
| SEV-2 | Customer-facing degradation; subset of users; SLO breach | On-call + IC; CTO notified within 4h |
| SEV-3 | Internal issue or limited customer impact | On-call handles; documented next-day |
| SEV-4 | Minor issue / observability gap | Filed as ticket; not a "real" incident |

**The Incident Commander role:**

For SEV-1 and SEV-2: someone owns the response. NOT the on-call engineer (they're fighting the fire). The IC role:
- Coordinates communication (status page, customer email, internal Slack)
- Tracks decisions and assigns subtasks
- Decides when to escalate
- Owns the postmortem

**Blameless postmortems:**

The single most important practice. The premise:
- The system enabled the failure; the engineer didn't cause it
- Focus: what changes prevent recurrence (process, code, tooling), not who to punish

**Required postmortem elements:**

1. Timeline (with timestamps)
2. Customer impact (specific: how many users, for how long, what they couldn't do)
3. Root cause (technical AND organizational)
4. Action items (specific, with owners, with due dates)
5. What went well (often skipped — capture the things that worked)

**Anti-pattern:** postmortems that blame the on-call engineer. Drives blame-avoidance culture; real causes go undocumented.

## Pillar 3: Deployment Cadence

**Two valid patterns:**

**Continuous deployment:** every commit that passes CI goes to production. Required if:
- DORA "Deployment Frequency" target is Elite
- Team has > 10 engineers contributing
- Production rollback can happen in < 5 minutes

**Scheduled deploys:** deployments happen at known windows (daily at 10am, weekly Wednesday).
- Acceptable for smaller teams or higher-stakes domains (healthcare, fintech)
- NOT a substitute for poor deploy pipeline; it's a deliberate choice for predictability

**Both work.** Mixing them ("usually continuous but sometimes scheduled") is the broken state. Pick a default and stick with it.

**Progressive delivery (the modern best practice):**

Instead of all-or-nothing deploys, use:
- **Canary:** roll out to 1% → 10% → 50% → 100% with health checks at each step
- **Feature flags:** decouple deploy from release; ramp features independently
- **Blue-green:** deploy to a parallel environment; cut over atomically

Pair with `engineering/feature-flags-architect/`.

**Anti-pattern: scheduled deploys + manual ceremony.**

If your "Tuesday deploy" requires a 30-person sync meeting and rollback is a 2-hour process, the cadence isn't a choice — it's a symptom. Invest in zero-downtime patterns first.

## Pillar 4: SLO Discipline

For every customer-facing service:

- **Service Level Indicator (SLI):** what you measure (e.g., "% of HTTP requests with status < 500")
- **Service Level Objective (SLO):** what you commit to (e.g., "99.9% over 30 days")
- **Error budget:** the inverse of SLO (e.g., 0.1% allowable failures)

**The error budget changes engineering behavior:**

- Budget healthy → ship faster, take risk
- Budget exhausted → freeze risky changes, focus on reliability work

This converts reliability from a feeling into a number.

**Pair with `engineering/slo-architect/`** for the full SLO design framework, error-budget policy, and multi-window burn-rate alerts.

## Maturity Levels

Track production discipline across maturity stages:

| Level | Practices |
|---|---|
| **Level 1: Reactive** | On-call exists but undefined; postmortems sometimes happen; no SLOs |
| **Level 2: Structured** | Defined severity levels; runbooks for top-5 scenarios; quarterly postmortem review |
| **Level 3: Predictive** | SLOs on all customer-facing services; error budgets influence deploy decisions; blameless postmortems are the norm |
| **Level 4: Self-Improving** | Game days / chaos engineering; postmortem action items tracked to closure; production-readiness reviews for new services |
| **Level 5: Elite** | Auto-remediation on common failures; production state directly observable; SLOs are board-level metrics |

**Typical stage targets:**
- Series A: aim for Level 2
- Series B: Level 3
- Growth: Level 4
- Late-stage: Level 4-5

## The Operating Model Cadence

Weekly:
- On-call handoff (Monday morning)
- Incident review (look back at SEV-2+ from prior week)

Monthly:
- DORA metrics review (delivery throughput)
- On-call health check (page volume per person, burnout signals)

Quarterly:
- Maturity-level self-assessment
- SLO review (are SLOs still right? any breaches?)
- Production-readiness review for new services launched this quarter

Annually:
- Game day / chaos engineering exercise
- Disaster recovery drill (full failover test)

## When This Reference Doesn't Help

- **Specific monitoring tooling (Datadog / New Relic / Honeycomb).** Tactical.
- **Specific incident management tooling (PagerDuty / Opsgenie / FireHydrant).** Tactical.
- **Specific chaos engineering implementation.** See `engineering/chaos-engineering/`.
- **SLO design specifics.** See `engineering/slo-architect/`.
- **Feature flag implementation.** See `engineering/feature-flags-architect/`.

This reference is about the operating-model discipline that holds production together, not about specific tools.

---

**Source authorities (non-exhaustive):**

- Beyer, Jones, Petoff, Murphy — "Site Reliability Engineering" (Google, 2016) — origin of modern SRE practice
- Beyer et al. — "The Site Reliability Workbook" (Google, 2018) — practical SLO + error budget guides
- Forsgren, Humble, Kim — "Accelerate" (2018) — DORA correlation with production discipline
- Allspaw, John — "Etsy postmortem process" + extensive writing on blameless postmortems
- PagerDuty Incident Response — public documentation on severity definitions + IC role
- Charity Majors — observability + production engineering writing (Honeycomb founder)
- Nora Jones — chaos engineering / resilience writing (Jeli founder, formerly Slack)
- Mikey Dickerson — "The Hierarchy of Reliability" (2016, Google) — SRE pyramid
