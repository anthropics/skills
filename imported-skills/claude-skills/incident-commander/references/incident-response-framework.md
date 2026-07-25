# Incident Response Framework Reference

Production-grade incident management knowledge base synthesizing PagerDuty, Google SRE, and Atlassian methodologies into a unified, opinionated framework. This document is the source of truth for incident commanders operating under pressure.

---

## 1. Industry Framework Comparison

### PagerDuty Incident Response Model

PagerDuty's open-source incident response process defines four core roles and five process phases. The model prioritizes **speed of mobilization** over process perfection.

**Roles:**
- **Incident Commander (IC):** Owns the incident end-to-end. Does NOT perform technical investigation. Delegates, coordinates, and makes final escalation decisions. The IC is the single point of authority; conflicting opinions are resolved by the IC, not by committee.
- **Scribe:** Captures timestamped decisions, actions, and findings in the incident channel. The scribe never participates in technical work. A good scribe reduces postmortem preparation time by 70%.
- **Subject Matter Expert (SME):** Pulled in on-demand for specific subsystems. SMEs report findings to the IC, not to each other. Parallel SME investigations must be coordinated through the IC to avoid duplicated effort.
- **Customer Liaison:** Owns all outbound customer communication. Drafts status page updates for IC approval. Shields the technical team from inbound customer inquiries during active incidents.

**Process Phases:** Detect, Triage, Mobilize, Mitigate, Resolve, Postmortem.

**Communication Protocol:** PagerDuty mandates a dedicated Slack channel per incident, a bridge call for SEV1/SEV2, and status updates at fixed cadences (every 15 min for SEV1, every 30 min for SEV2). All decisions are announced in the channel, never in DMs or side threads.

### Google SRE: Managing Incidents (Chapter 14)

Google's SRE model, documented in *Site Reliability Engineering* (O'Reilly, 2016), emphasizes **role separation** and **clear handoffs** as the primary mechanisms for preventing incident chaos.

**Key Principles:**
- **Operational vs. Communication Tracks:** Google splits incident work into two parallel tracks. The operational track handles technical mitigation. The communication track handles stakeholder updates, executive briefings, and customer notifications. These tracks run independently with the IC bridging them.
- **Role Separation is Non-Negotiable:** The person debugging the system must never be the person updating stakeholders. Cognitive load from context-switching between technical work and communication degrades both outputs. Google measured a 40% increase in mean-time-to-resolution (MTTR) when a single person attempted both.
- **Clear Handoffs:** When an IC rotates out (recommended every 60-90 minutes for SEV1), the handoff includes: current status summary, active hypotheses, pending actions, and escalation state. Handoffs happen on the bridge call, not asynchronously.
- **Defined Command Post:** All communication flows through a single channel. Google uses the term "command post" -- a virtual or physical location where all incident participants converge.

### Atlassian Incident Management Model

Atlassian's model, published in their *Incident Management Handbook*, is **severity-driven** and **template-heavy**. It favors structured playbooks over improvisation.

**Key Characteristics:**
- **Severity Levels Drive Everything:** The assigned severity determines who gets paged, what communication templates are used, response time SLAs, and postmortem requirements. Severity is assigned at triage and reassessed every 30 minutes.
- **Handbook-Driven Approach:** Atlassian maintains runbooks for every known failure mode. During incidents, responders follow documented playbooks before improvising. This reduces MTTR for known issues by 50-60% but requires significant upfront investment in documentation.
- **Communication Templates:** Pre-written templates for status page updates, customer emails, and executive summaries. Templates include severity-specific language and are reviewed quarterly. This eliminates wordsmithing during active incidents.
- **Values-Based Decisions:** When runbooks do not cover the situation, Atlassian defaults to a decision hierarchy: (1) protect customer data, (2) restore service, (3) preserve evidence for root cause analysis.

### Framework Comparison Table

| Dimension | PagerDuty | Google SRE | Atlassian |
|-----------|-----------|------------|-----------|
| Primary strength | Speed of mobilization | Role separation discipline | Structured playbooks |
| IC authority model | IC has final say | IC coordinates, escalates to VP if blocked | IC follows handbook, escalates if off-script |
| Communication style | Dedicated channel + bridge | Command post with dual tracks | Template-driven status updates |
| Handoff protocol | Informal | Formal on-call handoff script | Rotation policy in handbook |
| Postmortem requirement | All SEV1/SEV2 | All incidents | SEV1/SEV2 mandatory, SEV3 optional |
| Best for | Fast-moving startups | Large-scale distributed systems | Regulated or process-heavy orgs |
| Weakness | Under-documented for edge cases | Heavyweight for small teams | Rigid, slow to adapt to novel failures |

### When to Use Which Framework

- **Teams under 20 engineers:** Start with PagerDuty's model. It is lightweight and prescriptive enough to work without heavy process investment. Add Atlassian-style runbooks as you identify recurring failure modes.
- **Teams running 50+ microservices:** Adopt Google SRE's dual-track model. The operational/communication split becomes critical when incidents span multiple teams and subsystems.
- **Regulated industries (finance, healthcare, government):** Use Atlassian's handbook-driven approach as the foundation. Regulatory auditors expect documented procedures, and templates satisfy compliance requirements for incident communication records.
- **Hybrid (recommended for most teams at scale):** Use PagerDuty's role definitions, Google's track separation, and Atlassian's template library. This is the approach codified in the rest of this document.

---

## 2. Severity Definitions

### Severity Classification Matrix

| Severity | Impact | Response Time | Update Cadence | Escalation Trigger | Example |
|----------|--------|---------------|----------------|---------------------|---------|
| **SEV1** | Total service outage or data breach affecting all users. Revenue loss exceeding $10K/hour. Security incident with active exfiltration. | Page IC + on-call within 5 min. All hands mobilized within 15 min. | Every 15 min to stakeholders. Continuous updates in incident channel. | Immediate executive notification. Board notification for data breaches. | Primary database cluster down. Payment processing system offline. Active ransomware attack. |
| **SEV2** | Major feature degraded for >30% of users. Revenue impact $1K-$10K/hour. Data integrity concerns without confirmed loss. | IC assigned within 15 min. Responders mobilized within 30 min. | Every 30 min to stakeholders. Every 15 min in incident channel. | Executive notification if unresolved after 1 hour. Upgrade to SEV1 if impact expands. | Search functionality returning errors for 40% of queries. Checkout flow failing intermittently. Authentication latency exceeding 10s. |
| **SEV3** | Minor feature degraded or non-critical service impaired. Workaround available. No direct revenue impact. | Acknowledged within 1 hour. Investigation started within 4 hours. | Every 2 hours to stakeholders if actively worked. Daily if deferred. | Escalate to SEV2 if workaround fails or user complaints exceed 50 in 1 hour. | Admin dashboard loading slowly. Email notifications delayed by 30+ minutes. Non-critical API endpoint returning 5xx for <5% of requests. |
| **SEV4** | Cosmetic issue, minor bug, or internal tooling degradation. No user-facing impact or negligible impact. | Acknowledged within 1 business day. Prioritized against backlog. | No scheduled updates. Tracked in issue tracker. | Escalate to SEV3 if internal productivity impact exceeds 2 hours/day across team. | Logging pipeline dropping non-critical debug logs. Internal metrics dashboard showing stale data. Minor UI alignment issue on one browser. |

### Customer-Facing Signals by Severity

**SEV1 Signals:** Support ticket volume spikes >500% of baseline within 15 minutes. Social media mentions of outage trend upward. Revenue dashboards show >95% drop in transaction volume. Multiple monitoring systems alarm simultaneously.

**SEV2 Signals:** Support ticket volume spikes 100-500% of baseline. Specific feature-related complaints cluster in support channels. Partial transaction failures visible in payment dashboards. Single monitoring system shows sustained alerting.

**SEV3 Signals:** Sporadic support tickets with a common pattern (under 20/hour). Users report intermittent issues with workarounds. Monitoring shows degraded but not critical metrics.

**SEV4 Signals:** Internal team notices issue during routine work. Occasional user mention with no pattern or urgency. Monitoring shows minor anomaly within acceptable thresholds.

### Severity Upgrade and Downgrade Criteria

**Upgrade from SEV2 to SEV1:** Impact expands to >80% of users, revenue impact confirmed above $10K/hour, data integrity compromise confirmed, or mitigation attempt fails after 45 minutes.

**Downgrade from SEV1 to SEV2:** Partial mitigation restores service for >70% of users, revenue impact drops below $10K/hour, and no ongoing data integrity concern.

**Downgrade from SEV2 to SEV3:** Workaround deployed and communicated, impact limited to <10% of users, and no revenue impact.

Severity changes must be announced by the IC in the incident channel with justification. The scribe logs the timestamp and rationale.


---

## 3. Role Definitions

### Incident Commander (IC)

The IC is the single decision-maker during an incident. This role exists to eliminate decision-by-committee, which adds 20-40 minutes to MTTR in measured studies.

**Responsibilities:**
- Assign severity level at triage (reassess every 30 minutes)
- Assign all other incident roles
- Approve status page updates before publication
- Make go/no-go decisions on mitigation strategies (rollback, feature flag, scaling)
- Decide when to escalate to executive leadership
- Declare incident resolved and initiate postmortem scheduling

**Decision Authority:** The IC can authorize rollbacks, page any team member regardless of org chart, approve customer communications, and override objections from individual contributors during active mitigation. The IC cannot approve financial expenditures above $50K or public press statements -- those require VP/C-level approval.

**What the IC Must NOT Do:** Debug code, write queries, SSH into production servers, or perform any hands-on technical work. The moment an IC starts debugging, incident coordination degrades. If the IC is the only person with domain expertise, they must hand off IC duties before engaging technically.

### Communications Lead

**Responsibilities:**
- Draft all status page updates using severity-appropriate templates
- Coordinate with Customer Liaison on outbound customer messaging
- Maintain the executive summary document (updated every 30 min for SEV1/SEV2)
- Manage the stakeholder notification list and delivery
- Post scheduled updates even when there is no new information ("We are continuing to investigate" is a valid update)

### Operations Lead

**Responsibilities:**
- Coordinate technical investigation across SMEs
- Maintain the running hypothesis list and assign investigation tasks
- Report technical findings to the IC in plain language
- Execute mitigation actions approved by the IC
- Track parallel workstreams and prevent duplicated effort

### Scribe

**Responsibilities:**
- Maintain a timestamped log of all decisions, actions, and findings
- Document who said what and when in the incident channel
- Capture rollback decisions, hypothesis changes, and escalation triggers
- Produce the initial postmortem timeline (saves 2-4 hours of postmortem prep)

### Subject Matter Experts (SMEs)

SMEs are paged on-demand by the IC for specific subsystems. They report findings to the Operations Lead, not directly to stakeholders. An SME who identifies a potential fix proposes it to the IC for approval before executing. SMEs are released from the incident explicitly by the IC when their subsystem is cleared.

### Customer Liaison

Owns the customer-facing voice during the incident. Monitors support channels for inbound customer reports. Drafts customer notification emails. Updates the public status page (after IC approval). Shields the technical team from direct customer inquiries during active mitigation.

---

## 4. Communication Protocols

### Incident Channel Naming Convention

Format: `#inc-YYYYMMDD-brief-desc`

Examples:
- `#inc-20260216-payment-api-timeout`
- `#inc-20260216-db-primary-failover`
- `#inc-20260216-auth-service-degraded`

Channel topic must include: severity, IC name, bridge call link, status page link.
Example topic: `SEV1 | IC: @jane.smith | Bridge: https://meet.example.com/inc-20260216 | Status: https://status.example.com`

### Internal Status Update Templates

**SEV1/SEV2 Update Template (posted in incident channel and executive Slack channel):**
```
INCIDENT UPDATE - [SEV1/SEV2] - [HH:MM UTC]
Status: [Investigating | Identified | Mitigating | Resolved]
Impact: [Specific user-facing impact in plain language]
Current Action: [What is actively being done right now]
Next Update: [HH:MM UTC]
IC: @[name]
```

**Executive Summary Template (for SEV1, updated every 30 min):**
```
EXECUTIVE SUMMARY - [Incident Title] - [HH:MM UTC]
Severity: SEV1
Duration: [X hours Y minutes]
Customer Impact: [Number of affected users/transactions]
Revenue Impact: [Estimated $ if known, "assessing" if not]
Current Status: [One sentence]
Mitigation ETA: [Estimated time or "unknown"]
Next Escalation Point: [What triggers executive action]
```

### Status Page Update Templates

**SEV1 Initial Post:**
```
Title: [Service Name] - Service Disruption
Body: We are currently experiencing a disruption affecting [service/feature].
Users may encounter [specific symptom: errors, timeouts, inability to access].
Our engineering team has been mobilized and is actively investigating.
We will provide an update within 15 minutes.
```

**SEV1 Update (mitigation in progress):**
```
Title: [Service Name] - Service Disruption (Update)
Body: We have identified the cause of the disruption affecting [service/feature]
and are implementing a fix. Some users may continue to experience [symptom].
We expect to have an update on resolution within [X] minutes.
```

**SEV1 Resolution:**
```
Title: [Service Name] - Resolved
Body: The disruption affecting [service/feature] has been resolved as of [HH:MM UTC].
Service has been restored to normal operation. Users should no longer experience
[symptom]. We will publish a full incident report within 48 hours.
We apologize for the inconvenience.
```

**SEV2 Initial Post:**
```
Title: [Service Name] - Degraded Performance
Body: We are investigating reports of degraded performance affecting [feature].
Some users may experience [specific symptom]. A workaround is [available/not yet available].
Our team is actively investigating and we will provide an update within 30 minutes.
```

### Bridge Call / War Room Etiquette

1. **Mute by default.** Unmute only when speaking to the IC or Operations Lead.
2. **Identify yourself before speaking.** "This is [name] from [team]." Every time.
3. **State findings, then recommendations.** "Database replication lag is 45 seconds and climbing. I recommend we fail over to the secondary cluster."
4. **IC confirms before action.** No unilateral action on production systems during an incident. The IC says "approved" or "hold" before anyone executes.
5. **No side conversations.** If two SMEs need to discuss a hypothesis, they take it to a breakout channel and report back findings to the main bridge.
6. **Time-box debugging.** The IC sets 15-minute timers for investigation threads. If a hypothesis is not confirmed or denied in 15 minutes, pivot to the next hypothesis or escalate.

### Customer Notification Templates

**SEV1 Customer Email (B2B, enterprise accounts):**
```
Subject: [Company Name] Service Incident - [Date]

Dear [Customer Name],

We are writing to inform you of a service incident affecting [product/service]
that began at [HH:MM UTC] on [date].

Impact: [Specific impact to this customer's usage]
Current Status: [Brief status]
Expected Resolution: [ETA if known, or "We are working to resolve this as quickly as possible"]

We will continue to provide updates every [15/30] minutes until resolution.
Your dedicated account team is available at [contact info] for any questions.

Sincerely,
[Name], [Title]
```

---

## 5. Escalation Matrix

### Escalation Tiers

**Tier 1 - Within Team (0-15 minutes):**
On-call engineer investigates. If the issue is within the team's domain and matches a known runbook, resolve without escalation. Page the IC if severity is SEV2 or higher, or if the issue is not resolved within 15 minutes.

**Tier 2 - Cross-Team (15-45 minutes):**
IC pages SMEs from adjacent teams. Common cross-team escalations: database team for replication issues, networking team for connectivity failures, security team for suspicious activity. Cross-team SMEs join the incident channel and bridge call.

**Tier 3 - Executive (45+ minutes or immediate for SEV1):**
VP of Engineering notified for all SEV1 incidents immediately. CTO notified if SEV1 exceeds 1 hour without mitigation progress. CEO notified if SEV1 involves data breach or regulatory implications. Executive involvement is for resource allocation and external communication decisions, not technical direction.

### Time-Based Escalation Triggers

| Elapsed Time | SEV1 Action | SEV2 Action |
|-------------|-------------|-------------|
| 0 min | Page IC + all on-call. Notify VP Eng. | Page IC + primary on-call. |
| 15 min | Confirm all roles staffed. Open bridge call. | IC assesses if additional SMEs needed. |
| 30 min | If no mitigation path identified, page backup on-call for all related services. | First stakeholder update. Reassess severity. |
| 45 min | Escalate to CTO if no progress. Consider customer notification. | If no progress, consider escalating to SEV1. |
| 60 min | CTO briefing. Initiate customer notification if not already done. | Notify VP Eng. Page cross-team SMEs. |
| 90 min | IC rotation (fresh IC takes over). Reassess all hypotheses. | IC rotation if needed. |
| 120 min | CEO briefing if data breach or regulatory risk. External PR team engaged. | Escalate to SEV1 if impact has not decreased. |

### Escalation Path Examples

**Database failover failure:**
On-call DBA (Tier 1, 0-15 min) -> IC + DBA team lead (Tier 2, 15 min) -> Infrastructure VP + cloud provider support (Tier 3, 45 min)

**Payment processing outage:**
On-call payments engineer (Tier 1, 0-5 min) -> IC + payments team lead + payment provider liaison (Tier 2, 5 min, immediate due to revenue impact) -> CFO + VP Eng (Tier 3, 15 min if provider-side issue confirmed)

**Security incident (suspected breach):**
Security on-call (Tier 1, 0-5 min) -> CISO + IC + legal counsel (Tier 2, immediate) -> CEO + external incident response firm (Tier 3, within 1 hour if breach confirmed)

### On-Call Rotation Best Practices

- **Primary + secondary on-call** for every critical service. Secondary is paged automatically if primary does not acknowledge within 5 minutes.
- **On-call shifts are 7 days maximum.** Longer rotations degrade alertness and response quality.
- **Handoff checklist:** Current open issues, recent deploys in the last 48 hours, known risks or maintenance windows, escalation contacts for dependent services.
- **On-call load budget:** No more than 2 pages per night on average, measured weekly. Exceeding this indicates systemic reliability issues that must be addressed with engineering investment, not heroic on-call effort.

---

## 6. Incident Lifecycle Phases

### Phase 1: Detection

Detection comes from three sources, in order of preference:

1. **Automated monitoring (preferred):** Alerting rules on latency (p99 > 2x baseline), error rates (5xx > 1% of requests), saturation (CPU > 85%, memory > 90%, disk > 80%), and business metrics (transaction volume drops > 20% from 15-minute rolling average). Alerts should fire within 60 seconds of threshold breach.
2. **Internal reports:** An engineer notices anomalous behavior during routine work. Internal detection typically adds 5-15 minutes to response time compared to automated monitoring.
3. **Customer reports:** Customers contact support about issues. This is the worst detection source. If customers detect incidents before monitoring, the monitoring coverage has a gap that must be closed in the postmortem.

**Detection SLA:** SEV1 incidents must be detected within 5 minutes of impact onset. If detection latency exceeds this, the postmortem must include a monitoring improvement action item.

### Phase 2: Triage

The first responder performs initial triage within 5 minutes of detection:

1. **Scope assessment:** How many users, services, or regions are affected? Check dashboards, not assumptions.
2. **Severity assignment:** Use the severity matrix in Section 2. When in doubt, assign higher severity. Downgrading is cheap; delayed escalation is expensive.
3. **IC assignment:** For SEV1/SEV2, page the on-call IC immediately. For SEV3, the first responder may self-assign IC duties.
4. **Initial hypothesis:** What changed in the last 2 hours? Check deploy logs, config changes, upstream dependency status, and traffic patterns. 70% of incidents correlate with a change deployed in the prior 2 hours.

### Phase 3: Mobilization

The IC executes mobilization within 10 minutes of assignment:

1. **Create incident channel:** `#inc-YYYYMMDD-brief-desc`. Set topic with severity, IC name, bridge link.
2. **Assign roles:** Communications Lead, Operations Lead, Scribe. For SEV3/SEV4, the IC may cover multiple roles.
3. **Open bridge call (SEV1/SEV2):** Share link in incident channel. All responders join within 5 minutes.
4. **Post initial summary:** Current understanding, affected services, assigned roles, first actions.
5. **Notify stakeholders:** Page dependent teams. Notify customer support leadership. For SEV1, notify executive chain per escalation matrix.

### Phase 4: Investigation

Investigation runs as parallel workstreams coordinated by the Operations Lead:

- **Workstream discipline:** Each SME investigates one hypothesis at a time. The Operations Lead tracks active hypotheses on a shared list. Completed investigations report: confirmed, denied, or inconclusive.
- **Hypothesis testing priority:** (1) Recent changes (deploys, configs, feature flags), (2) Upstream dependency failures, (3) Capacity exhaustion, (4) Data corruption, (5) Security compromise.
- **15-minute rule:** If a hypothesis is not confirmed or denied within 15 minutes, the IC decides whether to continue, pivot, or escalate. Unbounded investigation is the leading cause of extended MTTR.
- **Evidence collection:** Screenshots, log snippets, metric graphs, and query results are posted in the incident channel, not described verbally. The scribe tags evidence with timestamps.

### Phase 5: Mitigation

Mitigation prioritizes restoring service over finding root cause:

- **Rollback first:** If a deploy correlates with the incident, roll it back before investigating further. A 5-minute rollback beats a 45-minute investigation. Rollback authority rests with the IC.
- **Feature flags:** Disable the suspected feature via feature flag if available. This is faster and less risky than a full rollback.
- **Scaling:** If the issue is capacity-related, scale horizontally before investigating the traffic source.
- **Failover:** If a primary system is unrecoverable, fail over to the secondary. Test failover procedures quarterly so this is a routine, not a gamble.
- **Customer workaround:** If mitigation will take time, publish a workaround for customers (e.g., "Use the mobile app while we restore web access").

**Mitigation verification:** After applying mitigation, monitor key metrics for 15 minutes before declaring the issue mitigated. Premature declarations that the issue is mitigated followed by recurrence damage team credibility and customer trust.

### Phase 6: Resolution

Resolution is declared when the root cause is addressed and service is operating normally:

- **Verification checklist:** Error rates returned to baseline, latency returned to baseline, no ongoing customer reports, monitoring confirms stability for 30+ minutes.
- **Incident channel update:** IC posts final status with resolution summary, total duration, and next steps.
- **Status page update:** Post resolution notice within 15 minutes of declaring resolved.
- **Stand down:** IC explicitly releases all responders. SMEs return to normal work. Bridge call is closed.

### Phase 7: Postmortem

Postmortem is mandatory for SEV1 and SEV2. Optional but recommended for SEV3. Never conducted for SEV4.

- **Timeline:** Postmortem document drafted within 24 hours. Postmortem meeting held within 72 hours (3 business days). Action items assigned and tracked in the team's issue tracker.
- **Blameless standard:** The postmortem examines systems, processes, and tools -- not individual performance. "Why did the system allow this?" not "Why did [person] do this?"
- **Required sections:** Timeline (from scribe's log), root cause analysis (using 5 Whys or fault tree), impact summary (users, revenue, duration), what went well, what went poorly, action items with owners and due dates.
- **Action items and recurrence:** Every postmortem produces 3-7 concrete action items. Items without owners and due dates are not action items. Teams should close 80%+ within 30 days. If the same root cause appears in two postmortems within 6 months, escalate to engineering leadership as a systemic reliability investment area.
