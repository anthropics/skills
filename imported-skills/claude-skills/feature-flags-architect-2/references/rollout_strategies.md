# Rollout strategies

Pick a strategy by risk, not by preference. Higher-risk launches get slower, more granular ramps.

## The 4 strategies

### 1. Ring (canary) — risky launches

`1% → 5% → 25% → 50% → 100%`

| Property | Value |
|---|---|
| Use when | Touches payments, auth, data integrity, performance-sensitive paths |
| Duration | 14-30 days typical |
| Hold time per ring | 24-72 hours minimum (long enough to detect anomalies) |
| Abort cost | Low (only 1-25% affected) |
| Verification | Full metrics suite at each ring |

**Phases:**
1. **0% (deploy)** — code ships dark; verify it deploys without flag turned on
2. **1%** — internal users + low-traffic cohort; full metric verification
3. **5%** — broader smoke test; watch for tail-of-distribution issues
4. **25%** — significant load; performance and infra checks
5. **50%** — half-and-half; perfect for A/B comparison
6. **100%** — fully on; hold 7 days before removing flag

**Abort triggers per ring:**
- Error rate > baseline + 1pp
- p99 latency > baseline × 1.2
- Business metric regression (conversion, retention) > baseline × 0.95

### 2. Linear — medium risk

Constant percent-per-day until target.

| Property | Value |
|---|---|
| Use when | Standard feature launches without high-risk paths |
| Duration | 7-14 days |
| Step size | (target / duration_days) per day |
| Abort cost | Medium |
| Verification | Daily metric check |

Example: 100% over 10 days = 10% per day.

### 3. Log (front-loaded) — low risk

Fast early ramp, slow tail. Reaches majority of population in first 1/3 of duration.

| Property | Value |
|---|---|
| Use when | Low-risk launch with high confidence; UI tweaks; copy changes |
| Duration | 3-7 days |
| Curve | `pct(t) = target × log(1+t) / log(1+T)` |
| Abort cost | Higher (most users on early) |
| Verification | Light — metric check at start and end |

### 4. Cohort — entitlement-aware

Named segments rolled in order: `internal → beta → free → paid → all`

| Property | Value |
|---|---|
| Use when | Feature has different value/risk per cohort; beta access; paying-tier first |
| Duration | Variable (gate by cohort size, not days) |
| Step size | Whole cohort at a time |
| Abort cost | Cohort-bounded |
| Verification | Per-cohort metrics |

**Order rules:**
1. Internal first — your own team finds bugs cheaply
2. Beta opt-in users — they expect rough edges
3. Free tier — broader signal at lower commercial risk
4. Paid plans — most valuable users last (or first for premium features)
5. All — flag fully on; remove flag

## Geo-staged variant

For internationally-distributed products, layer geo on top of any strategy:

```
Phase A: 100% in NZ/AU (low-traffic, English, off-business-hours US)
Phase B: 100% in EU (test data residency / GDPR paths)
Phase C: 100% in US (high traffic; full validation)
```

Useful for catching i18n, timezone, and regional infrastructure issues before peak load.

## Abort criteria

Hard-coded thresholds that auto-flip the flag back to 0% (or trigger paging):

| Signal | Threshold | Severity |
|---|---|---|
| Error rate (5xx) | > baseline + 1 percentage point | SEV1 |
| Error rate (4xx) | > baseline + 5 percentage points | SEV2 |
| p99 latency | > baseline × 1.2 | SEV2 |
| p999 latency | > baseline × 1.5 | SEV1 |
| Conversion rate | < baseline × 0.95 | SEV2 |
| Retention (D1/D7/D30) | < baseline × 0.95 | SEV2 |
| Database CPU | > 80% | SEV1 |
| Saturation alarm | any | SEV1 |

**Automate:** wire each threshold to a webhook that sets the flag to 0% via provider API.

## Verification per phase

At each phase, confirm:

1. **Health metrics** are within abort thresholds
2. **Business metrics** match or exceed control
3. **Logs** show no new error patterns
4. **User reports** (support tickets) show no spike for the affected feature
5. **Ops on-call** acknowledges no anomalies

If any signal is off, hold the phase. Don't advance on schedule alone.

## Hold-time rules

- **Off-hours hold time** doesn't count toward bake-in (e.g., a phase started Friday 6pm in PST is held until Monday 9am)
- **Weekend rollouts** require explicit owner approval and on-call coverage
- **Holiday rollouts** require VP-level approval

## Common mistakes

| Mistake | Fix |
|---|---|
| Skipping rings to "just get it done" | Don't. Aborts cost less than incidents. |
| 100% on Friday afternoon | Wait until Monday morning. |
| Rolling forward when metrics regress slightly | Stop. Investigate. The next ring exposes 5× more users. |
| No verification step defined per ring | Define it before starting. |
| Manual abort only (no automated kill switch) | Wire a threshold-based auto-abort. |
| Holding "for a few hours" then forgetting | Set a calendar event with the next phase + abort criteria. |

## Tools

- `scripts/rollout_planner.py` — generates a markdown plan
- Provider dashboards — for execution and real-time abort
- Metrics dashboard linked from `flag-doc` entry
- On-call runbook with kill-switch trigger words
