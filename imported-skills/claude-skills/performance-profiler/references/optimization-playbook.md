# Optimization Playbook — Template, Checklist, Pitfalls, Best Practices

The advisory layer behind the performance-profiler workflow: use this when
writing up an optimization, scanning for quick wins, or reviewing a
performance PR.

## Before/After Measurement Template

```markdown
## Performance Optimization: [What You Fixed]

**Date:** 2026-03-01  
**Engineer:** @username  
**Ticket:** PROJ-123  

### Problem
[1-2 sentences: what was slow, how was it observed]

### Root Cause
[What the profiler revealed]

### Baseline (Before)
| Metric | Value |
|--------|-------|
| P50 latency | 480ms |
| P95 latency | 1,240ms |
| P99 latency | 3,100ms |
| RPS @ 50 VUs | 42 |
| Error rate | 0.8% |
| DB queries/req | 23 (N+1) |

Profiler evidence: [link to flamegraph or screenshot]

### Fix Applied
[What changed — code diff or description]

### After
| Metric | Before | After | Delta |
|--------|--------|-------|-------|
| P50 latency | 480ms | 48ms | -90% |
| P95 latency | 1,240ms | 120ms | -90% |
| P99 latency | 3,100ms | 280ms | -91% |
| RPS @ 50 VUs | 42 | 380 | +804% |
| Error rate | 0.8% | 0% | -100% |
| DB queries/req | 23 | 1 | -96% |

### Verification
Load test run: [link to k6 output]
```

## Optimization Checklist

### Quick wins (check these first)

```
Database
□ Missing indexes on WHERE/ORDER BY columns
□ N+1 queries (check query count per request)
□ Loading all columns when only 2-3 needed (SELECT *)
□ No LIMIT on unbounded queries
□ Missing connection pool (creating new connection per request)

Node.js
□ Sync I/O (fs.readFileSync) in hot path
□ JSON.parse/stringify of large objects in hot loop
□ Missing caching for expensive computations
□ No compression (gzip/brotli) on responses
□ Dependencies loaded in request handler (move to module level)

Bundle
□ Moment.js → dayjs/date-fns
□ Lodash (full) → lodash/function imports
□ Static imports of heavy components → dynamic imports
□ Images not optimized / not using next/image
□ No code splitting on routes

API
□ No pagination on list endpoints
□ No response caching (Cache-Control headers)
□ Serial awaits that could be parallel (Promise.all)
□ Fetching related data in a loop instead of JOIN
```

## Common Pitfalls

- **Optimizing without measuring** — you'll optimize the wrong thing
- **Testing in development** — profile against production-like data volumes
- **Ignoring P99** — P50 can look fine while P99 is catastrophic
- **Premature optimization** — fix correctness first, then performance
- **Not re-measuring** — always verify the fix actually improved things
- **Load testing production** — use staging with production-size data

## Best Practices

1. **Baseline first, always** — record metrics before touching anything
2. **One change at a time** — isolate the variable to confirm causation
3. **Profile with realistic data** — 10 rows in dev, millions in prod — different bottlenecks
4. **Set performance budgets** — `p(95) < 200ms` in CI thresholds with k6
5. **Monitor continuously** — add Datadog/Prometheus metrics for key paths
6. **Cache invalidation strategy** — cache aggressively, invalidate precisely
7. **Document the win** — before/after in the PR description motivates the team
