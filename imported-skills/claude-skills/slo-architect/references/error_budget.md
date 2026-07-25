# Error budget

The most important number in your SLO.

## Computation

```
error_budget_fraction = 1 − (target_percent / 100)
error_budget_minutes  = error_budget_fraction × window_days × 24 × 60
error_budget_requests = error_budget_fraction × total_requests_in_window
```

## Reference table

| SLO target | 7-day budget (min) | 28-day budget (min) | 30-day budget (min) | 90-day budget (min) |
|---|---|---|---|---|
| 99% | 100.8 | 403.2 | 432 | 1296 |
| 99.5% | 50.4 | 201.6 | 216 | 648 |
| 99.9% | 10.08 | 40.32 | 43.2 | 129.6 |
| 99.95% | 5.04 | 20.16 | 21.6 | 64.8 |
| 99.99% | 1.008 | 4.032 | 4.32 | 12.96 |
| 99.999% | 0.1008 | 0.4032 | 0.432 | 1.296 |

99.999% over 30 days = 26 seconds of allowed downtime. Sustainable only with multi-region, sub-second failover, dedicated SRE team.

## Burn-rate alerts (Google SRE Workbook canon)

The single most useful artifact this skill produces. From Chapter 5: "Alerting on SLOs."

### Why multi-window

Single-window alerts fail in opposite directions:

| Window | Failure mode |
|---|---|
| 5 minutes | Fires on every blip; alert fatigue |
| 30 days | Fires when budget is already exhausted; too late |
| 1 hour alone | Fires too often; misses sustained slow burn |

Multi-window combines:
- **Long window** filters noise
- **Short window** speeds detection

The alert fires only when BOTH windows show high burn. This filters spikes (only short window high) and only fires on sustained burn (both windows high).

### Recommended thresholds

| Alert | Long window | Short window | Burn rate threshold | % budget at fire | Severity |
|---|---|---|---|---|---|
| Fast burn | 1h | 5m | 14.4 | 2% in 1h | page |
| Slow burn | 6h | 30m | 6 | 5% in 6h | page |
| Ticket | 3d | 6h | 1 | 10% in 3d | ticket |

The numbers come from: `burn_rate × bad_event_rate > slo_target_violation_rate`.

`error_budget_calculator.py` computes these for any target+window. Output is PromQL-shaped:

```promql
# fast_burn (page)
# Burn rate threshold: 14.4
(
  sli:rate1h > 14.4 * (1 - 0.999)
  AND
  sli:rate5m > 14.4 * (1 - 0.999)
)
```

Paste into your Prometheus rules; adjust label selectors to match your environment.

## Error budget policy

A policy without consequences is theater. The policy says: **"When budget is in state X, action Y happens automatically."**

### Standard 4-state policy

| State | Trigger | Action |
|---|---|---|
| **Healthy** | >50% budget remaining | Normal operation; ship features, run experiments |
| **Caution** | 25-50% budget remaining | Reduce risk on changes; no chaos experiments |
| **Critical** | <25% remaining | Freeze risky deploys; reliability work prioritized |
| **Violated** | Budget exhausted | Postmortem; SLO revision; blameless review |

### What "freeze" means

Specifically:
- No deploys to production except for SLO-improving fixes
- All releases require explicit owner sign-off
- Chaos experiments paused
- Feature flag rollouts paused

This is real, not aspirational. Engineering teams that don't follow through erode the credibility of the SLO.

### Recovery path

After SLO is violated:
1. Same-day: stop bleeding (rollback, kill switch, scale up)
2. Within 48h: postmortem published
3. Within 14 days: at least one follow-up action shipped
4. At 30 days: review whether SLO is still right

If burns are frequent, the SLO is wrong (too tight) OR the system needs investment.

## Burn-rate vs uptime alerting

Old-school: "Page if any 5xx rate >5%."
New-school: "Page if budget burns 14.4× faster than sustainable."

Why burn-rate is better:
- Stays calibrated as traffic grows (5% of low traffic = noise; of high traffic = real)
- Auto-adjusts for SLO target (99.99% needs sharper alerts than 99%)
- Aligns alerts with the SLO they protect

## When to skip burn-rate alerts

- For SLOs that aren't "always on" (batch jobs, async pipelines) — measure SLI per execution instead
- For SLOs in development (no historical data yet)
- For internal tools where ticket-only is enough — don't page the team for non-paging issues

## The error budget conversation

The SLO + error budget is meant to enable a conversation, not replace it.

> Engineering: "We want to ship the new payment provider this sprint."
> SRE: "We're at 35% budget remaining for the month. If this rolls back twice, we'll exhaust it."
> Eng: "Fine, we'll ship behind a feature flag and ramp 1% → 5% → 50% with a 24-hour bake at each stage."
> SRE: "OK. Set the flag's auto-abort to fire on the burn-rate alert."

That's the conversation the SLO + budget enables. Without numbers, both sides argue from gut feel.
