# Delivery Throughput — The Decision: "Are we shipping at the right speed, and where does work wait?"

This reference answers exactly one decision: **what are our DORA 4 metrics, where is the bottleneck, and what do we fix first?**

Pair with `scripts/delivery_throughput_analyzer.py` for automation.

## The DORA 4 Metrics

From Google's "Accelerate: The Science of Lean Software and DevOps" (Forsgren, Humble, Kim — 2018), refined annually in the "State of DevOps" report.

These are **team-level** metrics, not engineer-level. Misusing them for performance reviews is the fastest way to break them (engineers will game whatever you measure).

### 1. Deployment Frequency

How often code reaches production.

| Performance | Frequency |
|---|---|
| Elite | Multiple times per day |
| High | Once per day to once per week |
| Medium | Once per week to once per month |
| Low | Less than once per month |

**What it actually measures:** the team's ability to small-batch work and the safety of the deploy pipeline.

**Anti-pattern:** chasing deployment frequency by force-merging small no-op PRs. The metric is meaningful only when paired with change failure rate.

### 2. Lead Time for Changes

Time from commit to production.

| Performance | Lead Time |
|---|---|
| Elite | Less than 1 hour |
| High | 1 day to 1 week |
| Medium | 1 week to 1 month |
| Low | More than 1 month |

**What it actually measures:** how much friction exists between an engineer thinking they're done and the customer actually getting the change. Includes review queue, CI flakiness, deploy gates.

**This is the best single metric for overall team health.** If lead time is good, most other things are good.

### 3. Mean Time to Recovery (MTTR)

From incident detection to resolution.

| Performance | MTTR |
|---|---|
| Elite | Less than 1 hour |
| High | Less than 1 day |
| Medium | 1 day to 1 week |
| Low | More than 1 week |

**What it actually measures:** the operational maturity — monitoring, runbooks, on-call discipline, ability to roll back.

**Closely related: SLO discipline.** Pair this metric with `engineering/slo-architect/` for the error-budget framework that turns MTTR into proactive measurement.

### 4. Change Failure Rate

Percentage of deploys that cause an incident.

| Performance | Rate |
|---|---|
| Elite | 0-15% |
| High | 16-30% |
| Medium | 16-45% |
| Low | 46-60% |

**What it actually measures:** balance between speed and quality. Elite teams ship more AND break less; low-performing teams ship less AND break more (more time spent on incident response than feature work).

**Anti-pattern:** narrowly defining "incident" so the metric looks good. Be honest; pick a definition and stick with it.

## Bottleneck Identification

Cycle time = sum of waits between handoffs. The longest wait is the bottleneck.

**Standard breakdown:**

```
[engineer codes] -> PR creation -> first review -> approval -> merge -> deploy
                  └─ wait 1 ─┘   └── wait 2 ──┘  └ wait 3 ┘  └ wait 4 ┘
```

| Bottleneck | Typical Cause | Fix |
|---|---|---|
| PR creation → first review | Reviewers overloaded; no SLA | Reviewer rotation with 24h SLA + CODEOWNERS automation |
| First review → approval | Async ping-pong; review depth high | Cap PR size at 400 lines; pair-review for complex changes |
| Approval → merge | Flaky CI; required-but-redundant checks | Quarantine flaky tests; auto-merge after approval + green CI |
| Merge → deploy | Manual deploy gates; scheduled releases | Continuous deployment OR progressive delivery with feature flags |

**Rule of thumb:** if any single wait is > 50% of total cycle time, fix that one before anything else.

## The 4 Common Anti-Patterns

### Anti-pattern 1: Over-large PRs

PRs > 400 lines get reviewer fatigue. Reviewers approve to clear the queue, not because they reviewed deeply. Quality drops; rework increases.

**Fix:** stage refactors into smaller PRs; use feature flags so partial work can ship safely; review draft PRs early.

### Anti-pattern 2: Flaky CI

A test that fails intermittently is worse than no test. Engineers re-run, lose trust, eventually disable. Real bugs slip.

**Fix:** quarantine flaky tests immediately (move to a separate suite); allocate 10-20% of engineering time to a "flaky test budget" per quarter; track flake rate.

### Anti-pattern 3: Manual Deploy Gates

Every manual approval adds latency, AND humans approving without context don't actually catch bugs. The gate exists for compliance theatre, not safety.

**Fix:** automate gates with policy-as-code; use progressive delivery (canary, blue-green) for safety instead of approval; keep manual gates only for legal/compliance reasons.

### Anti-pattern 4: Scheduled Release Windows

"Production deploys only on Tuesdays" is a smell. It means the team doesn't trust the deploy pipeline, OR doesn't have rollback discipline, OR is using deploys as a coordination mechanism.

**Fix:** invest in zero-downtime deploys; build rollback discipline; deploy on demand.

## What to Fix First

The DORA research shows a clear priority order:

1. **Lead Time for Changes** — fix this first. It surfaces every other operating problem.
2. **Change Failure Rate** — once lead time is reasonable, drive down failure rate (mostly via better testing + progressive delivery).
3. **Deployment Frequency** — improves naturally as lead time and failure rate improve.
4. **MTTR** — improves naturally with deploy frequency (smaller blast radius per change).

If you try to fix MTTR first by adding more monitoring without fixing lead time, you'll just generate alerts faster on a system that's still slow.

## Operating Discipline

Quarterly review:

1. Pull DORA 4 metrics for the last quarter
2. Identify the worst metric (lowest performance level)
3. Identify the bottleneck in cycle time
4. Pick ONE thing to fix in the next quarter
5. Repeat

Resist the urge to fix everything at once. Engineering teams improve fastest when they pick one bottleneck and remove it.

## When This Reference Doesn't Help

- **SLO design and error budgets.** See `engineering/slo-architect/`.
- **Specific CI/CD tooling choices.** Tactical; pick what your team knows.
- **Code review culture / mentoring.** People dynamics; standard engineering management practice.
- **Production incident response.** See `engineering/chaos-engineering/` and standard incident-response playbooks.

This reference is about diagnosing throughput and choosing what to fix, not about implementing the fix.

---

**Source authorities (non-exhaustive):**

- Forsgren, Humble, Kim — "Accelerate: The Science of Lean Software and DevOps" (2018) — origin of DORA 4 metrics
- Google / DORA — "State of DevOps Report" (annual; latest 2024-2025) — benchmark thresholds + correlations
- Kim, Behr, Spafford — "The Phoenix Project" (2013) + "The DevOps Handbook" (2016) — flow theory
- Reinertsen, Donald — "The Principles of Product Development Flow" (2009) — queueing theory applied to dev work
- Newman, Sam — "Building Microservices" (2nd ed., 2021) — deployment patterns for distributed systems
- Humble, Jez — "Continuous Delivery" (2010) — deployment pipeline patterns
- Atlassian / GitHub / GitLab annual surveys — industry baselines for cycle time and review SLAs
