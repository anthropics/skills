# Experiment design

A well-designed chaos experiment has 7 sections. Skip any of them and the experiment becomes either useless (no learning) or dangerous (no bounds).

## The 7 sections

```
1. Hypothesis
2. Steady-state metric
3. Attack
4. Blast radius
5. Abort criteria
6. Rollback procedure
7. Learning question
```

## 1. Hypothesis

**Format:** *When [fault], [steady-state metric] stays [tolerance].*

Examples:
- *"When the primary Postgres replica fails, checkout p99 latency stays below 500ms."*
- *"When 50% of payment-service requests are throttled to 1 RPS, conversion rate drops by less than 5% within 60 seconds of return-to-normal."*
- *"When us-east-1 is partitioned from us-west-2, Search continues to return results from us-west-2 within 200ms p99."*

A good hypothesis:
- Names a specific fault (not "things break")
- Names a specific metric (not "everything")
- States a specific tolerance (not "good enough")
- Is measurable and falsifiable

## 2. Steady-state metric

The metric you'll measure before, during, and after the experiment.

Required properties:
- **Quantitative** — a number, not a feeling
- **Customer-relevant** — something users feel (latency, error rate, conversion)
- **Measurable in <60s** — slow metrics give you no time to abort
- **Stable in normal operation** — you need a baseline

| Good | Bad |
|---|---|
| p99 checkout latency | "the system is healthy" |
| 4xx + 5xx rate | "errors are low" |
| Successful login rate | CPU usage |
| Items added to cart per minute | replica count |

## 3. Attack

The fault you're injecting. Must specify:

- **Type** — latency, error, resource, partition, dependency, time, infrastructure
- **Magnitude** — *how* much (e.g., "+200ms", "10% errors", "100% timeout to peer X")
- **Duration** — how long the attack runs (typically 5-30 minutes)
- **Target** — which subset of the system gets the attack

See `attack_taxonomy.md` for the 7 attack types.

## 4. Blast radius

The maximum scope of customer impact. Use `blast_radius_calculator.py` to compute:

- **Affected users** — `traffic_share × user_population`
- **Error budget consumed** — `duration × traffic_share × availability_delta`
- **Risk score** — GREEN (<1% budget) / YELLOW (1-10%) / RED (>10%)

Rule of thumb:
- Start at 1% traffic share
- Grow only after 3 successful experiments at the previous level
- Never exceed 10% of monthly error budget in a single experiment

## 5. Abort criteria

The signals that auto-trigger experiment termination. Each must be:

- **Concrete** — specific metric and threshold ("p99 > 1000ms" not "performance degrades")
- **Detectable in <60s** — latency, error rate, throughput
- **Wired to action** — manual abort link in the dashboard, automatic via alert webhook

Standard abort criteria:

| Signal | Threshold | Action |
|---|---|---|
| p99 latency | > 2× baseline | abort |
| 5xx rate | > baseline + 1pp | abort |
| 4xx rate (excl. 401/404) | > baseline + 5pp | abort |
| Conversion rate | < baseline × 0.95 | abort |
| Customer ticket spike | > 3× baseline | escalate |
| On-call paged | any SEV1/SEV2 | abort |

## 6. Rollback procedure

How you'll revert the fault. Required because:
- Sometimes the chaos tool itself fails to revert
- Sometimes the fault has lingering effects (caches, connections)

Standard rollback:
1. Disable fault injection in tool
2. Verify steady-state recovers within 2 minutes
3. If not recovering, escalate as incident; restore from backup if needed

## 7. Learning question

What do you expect NOT to learn? Force yourself to predict the outcome.

Examples:
- *"We expect the cache to absorb the latency. We'll learn whether the timeout configuration on the upstream is correct."*
- *"We expect failover to take 30s. We'll learn whether retry backoff is configured."*

If you predicted the outcome correctly: confidence increased.
If you didn't: there's an unknown — file a follow-up.

## Pre-flight checklist

Before running the experiment, verify:

- [ ] Hypothesis written
- [ ] Steady-state metric measured for ≥5 minutes
- [ ] Blast radius calculated (GREEN or YELLOW)
- [ ] Abort criteria documented with thresholds
- [ ] Rollback procedure tested in staging
- [ ] On-call team notified in the team channel
- [ ] Monitoring dashboards open
- [ ] Owner identified and reachable
- [ ] Time-box agreed (max experiment duration)
- [ ] Communication plan if abort triggers

## Time-boxing

| Experiment type | Typical duration | Max recommended |
|---|---|---|
| First-time chaos | 5 minutes | 10 minutes |
| Familiar attack, new target | 15 minutes | 30 minutes |
| Continuous (automated) | per scheduler | 10 min per attack |
| Game Day (human-led) | 1-2 hours | 4 hours |

## Escalation

If abort criteria are hit:

1. **Stop the experiment immediately** (the obvious step many teams forget to script)
2. Verify steady-state recovery
3. If recovery doesn't happen in 5 min → declare an incident
4. Open a postmortem doc using `experiment_postmortem.py`
5. Notify stakeholders (whoever was promised "this won't impact anything")
6. Capture timeline while memory is fresh

## Anti-patterns

- **Hypothesis written after running** — that's a postmortem, not chaos engineering
- **Steady-state metric chosen during experiment** — pick before
- **Magnitude "small"** — quantify; "small" varies by reader
- **No abort criteria** — never run without them
- **Single owner of all chaos** — culture problem; spread the practice
- **Chaos that always succeeds** — increase magnitude; you're not learning if everything passes
- **Chaos that always fails** — reduce magnitude; you can't learn if everything breaks
- **Chaos with no follow-up actions** — what was the point?
