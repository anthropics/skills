# SLO principles

The Google SRE Workbook canon, distilled to what matters in practice.

## SLI vs SLO vs SLA

| Term | What it is | Audience | Stakes |
|---|---|---|---|
| **SLI** (Service Level Indicator) | A measurable signal of user-perceived health (e.g., HTTP success rate) | Engineering | None directly — it's the input |
| **SLO** (Service Level Objective) | A target value or range for the SLI over a window (e.g., 99.9% over 28 days) | Engineering, internal | Engineering action when burning budget |
| **SLA** (Service Level Agreement) | A customer-facing commitment with consequences (refunds, credits) | Customers, legal, sales | Contractual; costs money to break |

**Cardinal rule:** SLA target < SLO target < SLI baseline.

If SLA = 99.9%, SLO must be tighter (e.g., 99.95%) so engineering action triggers BEFORE customer-impacting violation.

## The error budget

```
error_budget = 100% − SLO_target

For 99.9% SLO over 30 days:
  error_budget = 0.1% × 30d × 24h × 60min = 43.2 minutes/month

That's the maximum unavailability you can spend without violating SLO.
```

The whole point of SLOs: error budget makes reliability a numeric resource you can spend deliberately. Spending it on:
- New feature rollouts (some risk)
- Chaos experiments (intentional learning)
- Migrations (necessary instability)

is GOOD. Wasting it on:
- Avoidable bugs
- Bad deploys
- Unmonitored regressions

is BAD. Error budget reframes "should we ship this?" from gut feel to a budget question.

## Multi-window burn-rate alerts (the canon)

Google SRE Workbook Chapter 5: "Alerting on SLOs." The recommended structure:

| Alert | Long window | Short window | % budget burned | Severity |
|---|---|---|---|---|
| Fast burn | 1h | 5m | 2% | page |
| Slow burn | 6h | 30m | 5% | page |
| Ticket burn | 3d | 6h | 10% | ticket (no page) |

Why two windows per alert?
- **Long window** filters noise (random spikes don't fire)
- **Short window** speeds detection (alert fires the moment burn is sustained)

Single-window burn-rate alerts are either too noisy (5-min only) or too slow (30-day only).

The `error_budget_calculator.py` tool emits these thresholds for any target+window combination.

## Choosing a target

Bad: copy-paste 99.9% on every endpoint.
Good: measure 30 days of historical SLI, then:

```
target = floor(p50 of last 30 days × 100) / 100
```

This guarantees the system has actually sustained the target. Tightening later is fine; loosening after announcing a target is embarrassing.

**Reality-check ranges:**

| User-perceived service | Typical target |
|---|---|
| Internal tool, occasional use | 99% |
| Standard customer-facing app | 99.9% |
| Commerce / payments | 99.95% |
| Critical infrastructure | 99.99% |
| Hyperscale (Google, AWS) | 99.999% (and only for tiny scope) |

99.99%+ requires multi-region, automatic failover, no single points of failure, and a team paid to maintain that. Don't write it on a whim.

## Choosing a window

| Window | Use when | Trade-off |
|---|---|---|
| 7 days | Need fast feedback; system changes weekly | High noise, fast learning |
| 28 days | Default for most services | Balanced |
| 30 days | Calendar-month aligned (board reports) | Slightly more noise than 28 |
| 90 days | Slow-changing systems, contract reporting | Too slow for engineering feedback |

28 days = 4 calendar weeks. Recommended unless you have a specific reason otherwise.

## Error budget policy (the missing half)

An SLO without a policy is a wish. The policy answers:

> When the error budget is burned, what changes?

Standard policy options:

| State | Action |
|---|---|
| Budget healthy (>50% remaining) | Normal operation; ship features, run experiments |
| Budget at 50% | Heightened review on risky changes |
| Budget exhausted (<10%) | Freeze risky deploys; focus on reliability work |
| Budget violated | Postmortem; SLO revision; blameless review |

Without an agreed policy, burning budget is just a number.

## SLO ownership

Every SLO has exactly one owning team. The owner is responsible for:
- Keeping the SLI definition correct as the system evolves
- Making sure burn-rate alerts route to the right team
- Quarterly review and revision
- Writing the postmortem when SLO is violated

Without an owner, SLOs bit-rot (SLI definitions drift, alerts route to wrong teams, reviews never happen).

## When NOT to define an SLO

- For internal tooling that breaks rarely and doesn't gate revenue
- For experimental features that may be removed in 30 days
- For systems where you can't measure user experience (revisit when you can)
- As performance theater — measuring without acting on burn

## Review cadence

- **Quarterly** — minimum for any active SLO
- **Monthly** — recommended for systems under active development
- **Weekly** — only during incident-recovery windows

The point of review: "is this SLO still right?" Tightening, loosening, or removing an SLO is a normal outcome. SLOs are not contracts; they are calibration knobs.

## Reading

- *Google SRE Workbook* (Beyer, Murphy, Rensin et al.) — Chapter 2 (SLO design), Chapter 5 (alerting on SLOs). Free at sre.google/workbook.
- *Implementing Service Level Objectives* (Alex Hidalgo) — covers operationalization beyond Google's frame.
- The SLO Reference Architecture (slo.dev) — community-maintained.
