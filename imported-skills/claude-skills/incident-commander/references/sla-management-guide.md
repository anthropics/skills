# SLA Management Guide

> Comprehensive reference for Service Level Agreements, Objectives, and Indicators.
> Designed for incident commanders who must understand, protect, and communicate SLA status during and after incidents.

---

## 1. Definitions & Relationships

### Service Level Indicator (SLI)

An SLI is the quantitative measurement of a specific aspect of service quality. SLIs are the raw data that feed everything above them. They must be precisely defined, automatically collected, and unambiguous.

**Common SLI types by service:**

| Service Type | SLI | Measurement Method |
|---|---|---|
| Web Application | Request latency (p50, p95, p99) | Server-side histogram |
| Web Application | Availability (successful responses / total requests) | Load balancer logs |
| REST API | Error rate (5xx responses / total responses) | API gateway metrics |
| REST API | Throughput (requests per second) | Counter metric |
| Database | Query latency (p99) | Slow query log + APM |
| Database | Replication lag (seconds) | Replica monitoring |
| Message Queue | End-to-end delivery latency | Timestamp comparison |
| Message Queue | Message loss rate | Producer vs consumer counts |
| Storage | Durability (objects lost / objects stored) | Integrity checksums |
| CDN | Cache hit ratio | Edge server logs |

**SLI specification formula:**

```
SLI = (good events / total events) x 100
```

For availability: `SLI = (successful requests / total requests) x 100`
For latency: `SLI = (requests faster than threshold / total requests) x 100`

### Service Level Objective (SLO)

An SLO is the target value or range for an SLI. It defines the acceptable level of reliability. SLOs are internal goals that engineering teams commit to.

**Setting meaningful SLOs:**

1. Measure the current baseline over 30 days minimum
2. Subtract a safety margin (typically 0.05%-0.1% below actual performance)
3. Validate against user expectations and business requirements
4. Never set an SLO higher than what the system can sustain without heroics

**Common pitfall:** Setting 99.99% availability when 99.9% meets every user need. The jump from 99.9% to 99.99% is a 10x reduction in allowed downtime and typically requires 3-5x the engineering investment.

**SLO examples:**

- `99.9% of HTTP requests return a non-5xx response within each calendar month`
- `95% of API requests complete in under 200ms (p95 latency)`
- `99.95% of messages are delivered within 30 seconds of production`

### Service Level Agreement (SLA)

An SLA is a formal contract between a service provider and its customers that specifies consequences for failing to meet defined service levels. SLAs must always be looser than SLOs to provide a buffer zone.

**Rule of thumb:** If your SLO is 99.95%, your SLA should be 99.9% or lower. The gap between SLO and SLA is your safety margin.

### The Hierarchy

```
  SLA (99.9%)     ← Contract with customers, financial penalties
    ↑ backs
  SLO (99.95%)    ← Internal target, triggers error budget policy
    ↑ targets
  SLI (measured)  ← Raw metric: actual uptime = 99.97% this month
```

**Standard combinations by tier:**

| Tier | SLI (Metric) | SLO (Target) | SLA (Contract) | Allowed Downtime/Month |
|---|---|---|---|---|
| Critical (payments) | Availability | 99.99% | 99.95% | SLO: 4.38 min / SLA: 21.9 min |
| High (core API) | Availability | 99.95% | 99.9% | SLO: 21.9 min / SLA: 43.8 min |
| Standard (dashboard) | Availability | 99.9% | 99.5% | SLO: 43.8 min / SLA: 3.65 hrs |
| Low (internal tools) | Availability | 99.5% | 99.0% | SLO: 3.65 hrs / SLA: 7.3 hrs |

---

## 2. Error Budget Policy

### What Is an Error Budget

An error budget is the maximum amount of unreliability a service can have within a given period while still meeting its SLO. It is calculated as:

```
Error Budget = 1 - SLO target
```

For a 99.9% SLO over a 30-day month (43,200 minutes):

```
Error Budget = 1 - 0.999 = 0.001 = 0.1%
Allowed Downtime = 43,200 x 0.001 = 43.2 minutes
```

### Downtime Allowances by SLO

| SLO | Error Budget | Monthly Downtime | Quarterly Downtime | Annual Downtime |
|---|---|---|---|---|
| 99.0% | 1.0% | 7 hrs 18 min | 21 hrs 54 min | 3 days 15 hrs |
| 99.5% | 0.5% | 3 hrs 39 min | 10 hrs 57 min | 1 day 19 hrs |
| 99.9% | 0.1% | 43.8 min | 2 hrs 11 min | 8 hrs 46 min |
| 99.95% | 0.05% | 21.9 min | 1 hr 6 min | 4 hrs 23 min |
| 99.99% | 0.01% | 4.38 min | 13.1 min | 52.6 min |
| 99.999% | 0.001% | 26.3 sec | 78.9 sec | 5.26 min |

### Error Budget Consumption Tracking

Track budget consumption as a percentage of the total budget used so far in the current window:

```
Budget Consumed (%) = (actual bad minutes / allowed bad minutes) x 100
```

Example: SLO is 99.9% (43.8 min budget/month). On day 10, you have had 15 minutes of downtime.

```
Budget Consumed = (15 / 43.8) x 100 = 34.2%
Expected consumption at day 10 = (10/30) x 100 = 33.3%
Status: Slightly over pace (34.2% consumed at 33.3% of month elapsed)
```

### Burn Rate

Burn rate measures how fast the error budget is being consumed relative to the steady-state rate:

```
Burn Rate = (error rate observed / error rate allowed by SLO)
```

A burn rate of 1.0 means the budget will be exactly exhausted by the end of the window. A burn rate of 10 means the budget will be exhausted in 1/10th of the window.

**Burn rate to time-to-exhaustion (30-day month):**

| Burn Rate | Budget Exhausted In | Urgency |
|---|---|---|
| 1x | 30 days | On pace, monitoring only |
| 2x | 15 days | Elevated attention |
| 6x | 5 days | Active investigation required |
| 14.4x | 2.08 days (~50 hours) | Immediate page |
| 36x | 20 hours | Critical, all-hands |
| 720x | 1 hour | Total outage scenario |

### Error Budget Exhaustion Policy

When the error budget is consumed, the following actions trigger based on threshold:

**Tier 1 - Budget at 75% consumed (Yellow):**
- Notify service team lead via automated alert
- Freeze non-critical deployments to the affected service
- Conduct pre-emptive review of upcoming changes for risk
- Increase monitoring sensitivity (lower alert thresholds)

**Tier 2 - Budget at 100% consumed (Orange):**
- Hard feature freeze on the affected service
- Mandatory reliability sprint: all engineering effort redirected to reliability
- Daily status updates to engineering leadership
- Postmortem required for the incidents that consumed the budget
- Freeze lasts until budget replenishes to 50% or systemic fixes are verified

**Tier 3 - Budget at 150% consumed / SLA breach imminent (Red):**
- Escalation to VP Engineering and CTO
- Cross-team war room if dependencies are involved
- Customer communication prepared and staged
- Legal and finance teams briefed on potential SLA credit obligations
- Recovery plan with specific milestones required within 24 hours

### Error Budget Policy Template

```
SERVICE: [service-name]
SLO: [target]% availability over [rolling 30-day / calendar month] window
ERROR BUDGET: [calculated] minutes per window

BUDGET THRESHOLDS:
  - 50% consumed: Team notification, increased vigilance
  - 75% consumed: Feature freeze for this service, reliability focus
  - 100% consumed: Full feature freeze, reliability sprint mandatory
  - SLA threshold crossed: Executive escalation, customer communication

REVIEW CADENCE: Monthly budget review on [day], quarterly SLO adjustment

EXCEPTIONS: Planned maintenance windows excluded if communicated 72+ hours in advance
            and within agreed maintenance allowance.

APPROVED BY: [Engineering Lead] / [Product Lead] / [Date]
```

---

## 3. SLA Breach Handling

### Detection Methods

**Automated detection (primary):**
- Real-time monitoring dashboards with SLA burn-rate alerts
- Automated SLA compliance calculations running every 5 minutes
- Threshold-based alerts when cumulative downtime approaches SLA limits
- Synthetic monitoring (external probes) for customer-perspective validation

**Manual review (secondary):**
- Monthly SLA compliance reports generated on the 1st of each month
- Customer-reported incidents cross-referenced with internal metrics
- Quarterly audits comparing measured SLIs against contracted SLAs
- Discrepancy review between internal metrics and customer-perceived availability

### Breach Classification

**Minor Breach:**
- SLA missed by less than 0.05 percentage points (e.g., 99.85% vs 99.9% SLA)
- Fewer than 3 discrete incidents contributed
- No single incident exceeded 30 minutes
- Customer impact was limited or partial degradation only
- Financial credit: typically 5-10% of monthly service fee

**Major Breach:**
- SLA missed by 0.05 to 0.5 percentage points
- Extended outage of 1-4 hours in a single incident, or multiple significant incidents
- Clear customer impact with support tickets generated
- Financial credit: typically 10-25% of monthly service fee

**Critical Breach:**
- SLA missed by more than 0.5 percentage points
- Total outage exceeding 4 hours, or repeated major incidents in same window
- Data loss, security incident, or compliance violation involved
- Financial credit: typically 25-100% of monthly service fee
- May trigger contract termination clauses

### Response Protocol

**For Minor Breach (within 3 business days):**
1. Generate SLA compliance report with exact metrics
2. Document contributing incidents with root causes
3. Send proactive notification to customer success manager
4. Issue service credits if contractually required (do not wait for customer to ask)
5. File internal improvement ticket with 30-day remediation target

**For Major Breach (within 24 hours):**
1. Incident commander confirms SLA impact calculation
2. Draft customer communication (see template below)
3. Executive sponsor reviews and approves communication
4. Issue service credits with detailed breakdown
5. Schedule root cause review with customer within 5 business days
6. Produce remediation plan with committed timelines

**For Critical Breach (immediate):**
1. Activate executive escalation chain
2. Legal team reviews contractual exposure
3. Finance team calculates credit obligations
4. Customer communication from VP or C-level within 4 hours
5. Dedicated remediation task force assigned
6. Weekly status updates to customer until remediation complete
7. Formal postmortem document shared with customer within 10 business days

### Customer Communication Template

```
Subject: Service Level Update - [Service Name] - [Month Year]

Dear [Customer Name],

We are writing to inform you that [Service Name] did not meet the committed
service level of [SLA target]% availability during [time period].

MEASURED PERFORMANCE: [actual]% availability
COMMITTED SLA: [SLA target]% availability
SHORTFALL: [delta] percentage points

CONTRIBUTING FACTORS:
- [Date/Time]: [Brief description of incident] ([duration] impact)
- [Date/Time]: [Brief description of incident] ([duration] impact)

SERVICE CREDIT: In accordance with our agreement, a credit of [amount/percentage]
will be applied to your next invoice.

REMEDIATION ACTIONS:
1. [Specific technical fix with completion date]
2. [Process improvement with implementation date]
3. [Monitoring enhancement with deployment date]

We take our service commitments seriously. [Name], [Title] is personally
overseeing the remediation and is available to discuss further at your convenience.

Sincerely,
[Name, Title]
```

### Legal and Compliance Considerations

- Maintain auditable records of all SLA measurements for the full contract term plus 2 years
- SLA calculations must use the measurement methodology defined in the contract, not internal approximations
- Force majeure clauses typically exclude natural disasters, but verify per contract
- Planned maintenance exclusions must match the exact notification procedures in the contract
- Multi-region SLAs may have separate calculations per region; verify aggregation method

---

## 4. Incident-to-SLA Mapping

### Downtime Calculation Methodologies

**Full outage:** Service completely unavailable. Every minute counts as a full minute of downtime.

```
Downtime = End Time - Start Time (in minutes)
```

**Partial degradation:** Service available but impaired. Apply a degradation factor:

```
Effective Downtime = Actual Duration x Degradation Factor
```

| Degradation Level | Factor | Description |
|---|---|---|
| Complete outage | 1.0 | Service fully unavailable |
| Severe degradation | 0.75 | >50% of requests failing or >10x latency |
| Moderate degradation | 0.5 | 10-50% of requests affected or 3-10x latency |
| Minor degradation | 0.25 | <10% of requests affected or <3x latency increase |
| Cosmetic / non-functional | 0.0 | No impact on core SLI metrics |

**Note:** The exact degradation factors must be agreed upon in the SLA contract. The above are industry-standard starting points.

### Planned vs Unplanned Downtime

Most SLAs exclude pre-announced maintenance windows from availability calculations, subject to conditions:

- Notification provided N hours/days in advance (commonly 72 hours)
- Maintenance occurs within an agreed window (e.g., Sunday 02:00-06:00 UTC)
- Total planned downtime does not exceed the monthly maintenance allowance (e.g., 4 hours/month)
- Any overrun beyond the planned window counts as unplanned downtime

```
SLA Availability = (Total Minutes - Excluded Maintenance - Unplanned Downtime) / (Total Minutes - Excluded Maintenance) x 100
```

### Multi-Service SLA Composition

When a customer-facing product depends on multiple services, composite SLA is calculated as:

**Serial dependency (all must be up):**
```
Composite SLA = SLA_A x SLA_B x SLA_C
Example: 99.9% x 99.95% x 99.99% = 99.84%
```

**Parallel / redundant (any one must be up):**
```
Composite Availability = 1 - ((1 - SLA_A) x (1 - SLA_B))
Example: 1 - ((1 - 0.999) x (1 - 0.999)) = 1 - 0.000001 = 99.9999%
```

This is critical during incidents: an outage in a shared dependency may breach SLAs for multiple customer-facing products simultaneously.

### Worked Examples

**Example 1: Simple outage**
- Service: Core API (SLA: 99.9%)
- Month: 30 days = 43,200 minutes
- Incident: Full outage from 14:23 to 14:38 UTC on the 12th (15 minutes)
- No other incidents this month

```
Availability = (43,200 - 15) / 43,200 x 100 = 99.965%
SLA Status: PASS (99.965% > 99.9%)
Error Budget Consumed: 15 / 43.2 = 34.7%
```

**Example 2: Partial degradation**
- Service: Payment Processing (SLA: 99.95%)
- Month: 30 days = 43,200 minutes
- Incident: 50% of transactions failing for 4 hours (240 minutes)
- Degradation factor: 0.5 (moderate - 50% of requests affected)

```
Effective Downtime = 240 x 0.5 = 120 minutes
Availability = (43,200 - 120) / 43,200 x 100 = 99.722%
SLA Status: FAIL (99.722% < 99.95%)
Shortfall: 0.228 percentage points → Major Breach
```

**Example 3: Multiple incidents**
- Service: Dashboard (SLA: 99.5%)
- Month: 31 days = 44,640 minutes
- Incident A: 45-minute full outage on the 5th
- Incident B: 2-hour severe degradation (factor 0.75) on the 18th
- Incident C: 30-minute full outage on the 25th

```
Total Effective Downtime = 45 + (120 x 0.75) + 30 = 45 + 90 + 30 = 165 minutes
Availability = (44,640 - 165) / 44,640 x 100 = 99.630%
SLA Status: PASS (99.630% > 99.5%)
Error Budget Consumed: 165 / 223.2 = 73.9% → Yellow threshold, feature freeze recommended
```

---

## 5. SLO Best Practices

### Start with User Journeys

Do not set SLOs based on infrastructure metrics. Start from what users experience:

1. Identify critical user journeys (e.g., "User completes checkout")
2. Map each journey to the services and dependencies involved
3. Define what "good" looks like for each journey (fast, error-free, complete)
4. Select the SLIs that most directly measure that user experience
5. Set SLO targets that reflect the minimum acceptable user experience

A database with 99.99% uptime is meaningless if the API in front of it has a bug causing 5% error rates.

### The Four Golden Signals as SLI Sources

From Google SRE, the four golden signals provide comprehensive service health:

| Signal | SLI Example | Typical SLO |
|---|---|---|
| Latency | p99 request duration < 500ms | 99% of requests under threshold |
| Traffic | Requests per second | N/A (capacity planning, not SLO) |
| Errors | 5xx rate as % of total requests | < 0.1% error rate over rolling window |
| Saturation | CPU/memory/queue depth | < 80% utilization (capacity SLI) |

For most services, latency and error rate are the two most important SLIs to back with SLOs.

### Setting SLO Targets

1. Collect 90 days of historical SLI data
2. Calculate the 5th percentile performance (worst 5% of days)
3. Set SLO slightly above that baseline (this ensures the SLO is achievable without heroics)
4. Validate: would a breach at this level actually impact users negatively?
5. Adjust upward only if user impact analysis demands it

**Never set SLOs by aspiration.** A 99.99% SLO on a service that has historically achieved 99.93% is a guaranteed source of perpetual firefighting with no reliability improvement.

### Review Cadence

- **Weekly:** Review current error budget burn rate, flag services approaching thresholds
- **Monthly:** Full SLO compliance review, adjust alert thresholds if needed
- **Quarterly:** Reassess SLO targets based on 90-day data, review SLA contract alignment
- **Annually:** Strategic SLO review tied to product roadmap and infrastructure investments

### Anti-Patterns

| Anti-Pattern | Problem | Fix |
|---|---|---|
| Vanity SLOs | Setting 99.99% to impress, then ignoring breaches | Set achievable targets, enforce budget policy |
| SLO Inflation | Ratcheting SLOs up whenever performance is good | Only increase SLOs when users demonstrably need it |
| Unmeasured SLAs | Committing contractual SLAs without actual SLI measurement | Instrument SLIs before signing SLA contracts |
| Copy-Paste SLOs | Same SLO for every service regardless of criticality | Tier services by business impact, set SLOs accordingly |
| Ignoring Dependencies | Setting aggressive SLOs without accounting for dependency reliability | Calculate composite SLA; your SLO cannot exceed dependency chain |
| Alert-Free SLOs | Having SLOs but no automated alerting on budget consumption | Every SLO must have corresponding burn rate alerts |

---

## 6. Monitoring & Alerting for SLAs

### Multi-Window Burn Rate Alerting

The Google SRE approach uses multiple time windows to balance speed of detection against alert noise. Each alert condition requires both a short window (for speed) and a long window (for confirmation):

**Alert configuration matrix:**

| Severity | Short Window | Short Threshold | Long Window | Long Threshold | Action |
|---|---|---|---|---|---|
| Critical (Page) | 1 hour | > 14.4x burn rate | 5 minutes | > 14.4x burn rate | Wake someone up |
| High (Page) | 6 hours | > 6x burn rate | 30 minutes | > 6x burn rate | Page on-call within 30 min |
| Medium (Ticket) | 3 days | > 1x burn rate | 6 hours | > 1x burn rate | Create ticket, next business day |

**Why these specific numbers:**

- 14.4x burn rate over 1 hour consumes 2% of monthly budget in that hour. At this rate, the entire 30-day budget is gone in ~50 hours. This demands immediate human attention.
- 6x burn rate over 6 hours consumes 5% of monthly budget. The budget will be exhausted in 5 days. Urgent but not wake-up-at-3am urgent.
- 1x burn rate over 3 days means you are on pace to exactly exhaust the budget. This needs investigation but is not an emergency.

### Burn Rate Alert Formulas

For a given time window, calculate the burn rate:

```
burn_rate = (error_count_in_window / request_count_in_window) / (1 - SLO_target)
```

Example for a 99.9% SLO, observing 50 errors out of 10,000 requests in a 1-hour window:

```
observed_error_rate = 50 / 10,000 = 0.005 (0.5%)
allowed_error_rate = 1 - 0.999 = 0.001 (0.1%)
burn_rate = 0.005 / 0.001 = 5.0
```

A burn rate of 5.0 means the error budget is being consumed 5 times faster than the sustainable rate.

### Alert Severity to SLA Risk Mapping

| Burn Rate | Budget Impact | SLA Risk | Response |
|---|---|---|---|
| < 1x | Under budget pace | None | Routine monitoring |
| 1x - 3x | On pace or slightly over | Low | Investigate next business day |
| 3x - 6x | Budget will exhaust in 5-10 days | Moderate | Investigate within 4 hours |
| 6x - 14.4x | Budget will exhaust in 2-5 days | High | Page on-call, respond in 30 min |
| > 14.4x | Budget will exhaust in < 2 days | Critical | Immediate page, incident declared |
| > 100x | Active major outage | SLA breach imminent | All-hands incident response |

### Dashboard Design for SLA Tracking

Every SLA-tracked service should have a dashboard with these panels:

**Row 1 - Current Status:**
- Current availability (real-time, rolling 5-minute window)
- Current error rate (real-time)
- Current p99 latency (real-time)

**Row 2 - Budget Status:**
- Error budget remaining (% of monthly budget, gauge visualization)
- Budget consumption timeline (line chart, actual vs expected burn)
- Budget burn rate (current 1h, 6h, and 3d burn rates)

**Row 3 - Historical Context:**
- 30-day availability trend (daily granularity)
- SLA compliance status for current and previous 3 months
- Incident markers overlaid on availability timeline

**Row 4 - Dependencies:**
- Upstream dependency availability (services this service depends on)
- Downstream impact scope (services that depend on this service)
- Composite SLA calculation for customer-facing products

### Alert Fatigue Prevention

Alert fatigue is the primary reason SLA monitoring fails in practice. Mitigation strategies:

1. **Require dual-window confirmation.** Never page on a single short window. Always require both the short window (for speed) and long window (for persistence) to fire simultaneously.

2. **Separate page-worthy from ticket-worthy.** Only two conditions should wake someone up: >14.4x burn rate sustained, or >6x burn rate sustained. Everything else is a ticket.

3. **Deduplicate aggressively.** If the same service triggers both a latency and error rate alert for the same underlying issue, group them into a single notification.

4. **Auto-resolve.** Alerts must auto-resolve when the burn rate drops below threshold. Never leave stale alerts open.

5. **Review alert quality monthly.** Track the ratio of actionable alerts to total alerts. Target >80% actionable rate. If an alert fires and no human action is needed, tune or remove it.

6. **Escalation, not repetition.** If an alert is not acknowledged within the response window, escalate to the next tier. Do not re-send the same alert every 5 minutes.

### Practical Monitoring Stack

| Layer | Tool Category | Purpose |
|---|---|---|
| Collection | Prometheus, OpenTelemetry, StatsD | Gather SLI metrics from services |
| Storage | Prometheus TSDB, Thanos, Mimir | Retain metrics for SLO window + 90 days |
| Calculation | Prometheus recording rules, Sloth | Pre-compute burn rates and budget consumption |
| Alerting | Alertmanager, PagerDuty, OpsGenie | Route alerts by severity and schedule |
| Visualization | Grafana, Datadog | Dashboards for real-time and historical SLA views |
| Reporting | Custom scripts, SLO generators | Monthly SLA compliance reports for customers |

**Retention requirement:** SLI data must be retained for at least the SLA reporting period (typically monthly or quarterly) plus a 90-day dispute window. Annual SLA reviews require 12 months of data at daily granularity minimum.

---

*Last updated: February 2026*
*For use with: incident-commander skill*
*Maintainer: Engineering Team*
