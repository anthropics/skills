# SLI design

The SLI is the foundation. Get it wrong and the SLO is meaningless — green dashboard, angry users.

## The user-experience test

Before defining ANY SLI, answer:

> When this signal turns red, will a user notice?

If the answer is "maybe" or "depends," it's not an SLI — it's an internal metric.

| Signal | User notices? | Use as SLI? |
|---|---|---|
| HTTP 5xx rate | Yes | YES |
| p99 latency at the user's edge | Yes | YES |
| Successful login rate | Yes | YES |
| CPU usage on backend | No | NO |
| Memory usage on backend | No | NO |
| Pod restart count | No (until it's too late) | NO |
| Database query duration | Indirect | Maybe (if it dominates user latency) |

CPU and memory are LEADING indicators of trouble — useful for capacity planning, useless for SLO.

## The 5 SLI types

### 1. Request-success-rate (most common)

Numerator: "good" requests
Denominator: total requests

```
sli = (total - 5xx - timeouts - protocol_errors) / total
```

Use when:
- Service is request-driven (HTTP, gRPC, queue handler)
- Each request is independent
- Success/failure is well-defined

Edge cases:
- 4xx is usually NOT counted as bad (they're client errors), EXCEPT 429 (rate limiting) and 401/403 if those are operator-caused
- Time out at p99 of expected latency; treat anything beyond as bad
- Cancelled requests are tricky — define explicitly

### 2. Request-latency

Numerator: requests with latency below threshold
Denominator: total requests

```
sli = count(latency_p99 < 500ms) / count(all)
```

Use when:
- Performance is part of user experience (most user-facing services)
- A success that takes 30 seconds is effectively a failure

Pick the threshold from data: measure p50/p95/p99 over 30 days, then set the threshold at p95 of typical good operation.

### 3. Availability-time

Numerator: window minus total downtime
Denominator: window length

```
sli = (window - sum(downtime_seconds)) / window
```

Use when:
- Service is "always-on" (DNS, infrastructure, control plane)
- "Up" or "down" is binary
- No clear request unit

Define "up" precisely: is one health check failure "down"? Three consecutive? Per-region or per-cluster?

### 4. Data-freshness

Numerator: data points younger than threshold
Denominator: total data points

```
sli = count(data_age < 5min) / count(all_data)
```

Use when:
- Service's value depends on recency (analytics dashboards, fraud detection, search index)
- "Stale data" is the user-facing failure mode

### 5. Correctness

Numerator: outputs that are correct
Denominator: total outputs

```
sli = count(correct_predictions) / count(predictions)
```

Use when:
- Output quality matters more than speed (ML models, search ranking, fraud scoring)
- You have ground truth (labels, customer feedback, A/B comparison)

Hardest SLI to maintain because "correct" requires labeled data.

## SLI vs SLO target — concrete examples

### Example 1: Checkout API

- **SLI:** `(2xx + 3xx requests) / total requests`, excluding 4xx (client errors)
- **SLO target:** 99.9% over 28 days
- **Error budget:** 40.32 minutes/window of unavailability

### Example 2: Search latency

- **SLI:** `count(latency < 200ms) / count(all_searches)`
- **SLO target:** 99.5% over 28 days
- **Error budget:** 3.36 hours/window where >0.5% of queries are slow

### Example 3: Internal API uptime

- **SLI:** `(window - downtime) / window`, downtime measured by pingdom-style probes
- **SLO target:** 99% over 28 days
- **Error budget:** 6.72 hours/window of allowed outage

## Common SLI mistakes

### "We just count errors"

Errors are useful but incomplete. A request that returns 200 OK in 30 seconds is a failure even though it's not an error. Use latency SLI for performance-sensitive services.

### Conflating SLIs across user journeys

If checkout and browsing are different user experiences, they get different SLIs. A 99.9% on "the API" averages over journeys with very different criticality.

### Counting bot traffic

Bots can dominate request volume. Filter them out (or have a separate SLI for them) — your error budget shouldn't be spent on synthetic traffic.

### Counting internal traffic

If your service is hit by other internal services, those requests have different reliability requirements than user requests. Separate SLIs.

### Using ratios that go backward

```
WRONG:  sli = errors / total
        (lower is better — confusing)

RIGHT:  sli = (total - errors) / total
        (higher is better, matches SLO target convention)
```

## Defining the numerator/denominator precisely

Every SLI must specify:

1. **What's being counted** (requests? events? checks?)
2. **What "good" means** (the numerator filter)
3. **What's excluded** (filters: bot traffic, internal traffic, health checks, etc.)
4. **Where it's measured** (LB? service edge? client side?)

Bad: "request success rate"
Good: `count(http_requests_total{job="checkout-api", status_code=~"2..|3.."}) / count(http_requests_total{job="checkout-api", source!="bot"})`

The second one is testable, debuggable, and unambiguous.

## Review the SLI as the system evolves

System change → SLI change. When:

- A new failure mode appears (e.g., circuit breaker that returns 5xx) → update what's "bad"
- A dependency moves (e.g., from synchronous to async) → re-examine what users feel
- A new endpoint is added → does it belong in this SLO or its own?

Stale SLIs are worse than no SLIs — they create false confidence.
