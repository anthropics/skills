# Parallel Execution Discipline — Why 1 q/sec, Why Parallel-Across-Sources

This reference answers exactly one decision: **how does pulse balance speed (parallel execution) against politeness (1 q/sec rate limits), and when does the skill degrade vs continue?**

## The Two Rules That Govern Execution

1. **Parallel across independent sources.** Reddit, HN, Web, X are independent — they don't share rate-limit state. Run them concurrently. This roughly halves wall-clock time for a 4-platform run.

2. **Sequential within a single source.** Reddit's 3 queries (top, new, top-comments) fire one at a time, 1 q/sec. Same for HN's stories+comments queries. Same for Web's 2-3 query rotation. This stays under the per-source rate ceiling.

## Why 1 q/sec Specifically

The choice of 1 q/sec is the **defensible conservative lower bound** across the public APIs the skill uses. Higher rates work *sometimes* but break unpredictably. Lower rates are wasteful.

**Per-source justification:**

| Source | Documented ceiling (approx) | Pulse setting | Margin |
|---|---|---|---|
| Reddit public JSON | ~1 q/sec per IP (varies; OAuth allows 60/min) | 1 q/sec | At-ceiling |
| HN Algolia | No hard limit (community-shared infra) | 1 q/sec | Polite |
| Web search APIs | varies (Bing 3 qps, Google CSE 100/day, Brave 1 qps free tier) | 1 q/sec | At-ceiling (Brave) |
| X/Twitter (Grok / API) | Varies wildly by tier | 1 q/sec | Conservative |

The 1 q/sec floor handles all these cleanly. A skill that pushes 3 qps will succeed on some sources, get rate-limited on others, and produce inconsistent runs.

## Concurrency Patterns

### Parallel Phases (Phases 1, 2, 3)

```
Time →
0s    1s    2s    3s    4s    5s    6s    7s
Reddit:  Q1 ──→ ●     Q2 ──→ ●     Q3 ──→ ●
HN:      Q1 ──→ ●     Q2 ──→ ●     (done)
Web:     Q1 ──→ ●     Q2 ──→ ●     Q3 ──→ ●
```

All three platforms start at `t=0`. Within each platform, queries fire 1 second apart. Total wall-clock time = max(time-per-platform), not sum.

For a 4-2-3 query budget across Reddit-HN-Web: sequential would take 9 seconds. Parallel takes 3-4 seconds.

### Sequential Phase 4 (X/Twitter)

Phase 4 runs last and sequentially because:
1. **High failure rate** — X is the most likely to fail (browser automation flakiness, Grok unavailability, API auth issues). Running it last means its failure doesn't block Phases 1–3.
2. **Lower marginal signal** — X content overlaps significantly with Reddit/HN, so it adds delta not foundation.
3. **Different tool surface** — Phases 1–3 use HTTP fetch; Phase 4 uses Grok / browser / API. Mixing them concurrently complicates the harness.

## Plan-Tier Detection (Rate-Limit Header Signals)

For sources that return rate-limit metadata, honor it:

| Header | Meaning | Action |
|---|---|---|
| `X-Ratelimit-Limit: N` | Total quota | Track against `Remaining` |
| `X-Ratelimit-Remaining: 0` | Quota exhausted | Stop hitting this source; mark as "rate-limited, partial" in output |
| `X-Ratelimit-Reset: <ts>` | When quota refills | If exhausted mid-run, wait until reset only if `<ts>` is within 5s; otherwise skip rest |
| `Retry-After: <seconds>` | Server-specified backoff | Honor exactly; if > 10s, mark source partial and continue |

For sources without these headers (Reddit public JSON, HN Algolia free tier), default to 1 q/sec and trust the conservative limit.

## Failure Modes and Recovery

### Single failed request

```
Reddit Q1 → 429
  Wait 3s.
  Reddit Q1 retry → 200
  Continue.
```

Log: "Reddit Q1 retried after 429."

### Repeated source failure

```
Reddit Q1 → 429
  Wait 3s.
  Reddit Q1 retry → 429
  Mark Reddit "partial — Q1 failed after retry."
  Continue Reddit Q2.
Reddit Q2 → 429
  Wait 3s.
  Reddit Q2 retry → 429
  Mark Reddit "rate-limited, dropping remaining queries."
  Continue with HN and Web only.
```

The skill does NOT block the whole run on one source failing.

### 3 consecutive failures across all sources

```
Reddit Q1 → 429 (retry → 429): consecutive=1
HN Q1 → 503 (retry → 503): consecutive=2
Web Q1 → timeout (retry → timeout): consecutive=3
STOP.
```

When 3 consecutive failures fire across *any* sources, halt. Likely root cause: network sandbox issue, harness misconfiguration, or simultaneous-outage event. Report what was collected and tell the user.

Note: a successful source resets the consecutive counter. Reddit-fail then HN-success then Web-fail then Web-fail-again is consecutive=2 (not 3) on Web alone.

## Why Not More Aggressive (3 qps, exponential backoff, 5 retries)?

For production services with SLAs and dedicated quotas, aggressive retry patterns make sense. For research workflows, they don't:

- **Users want fast feedback on failure.** If a source is broken, the user wants to know in 5 seconds, not 30.
- **Backoff math is wasteful at low scale.** Exponential backoff (1s, 2s, 4s, 8s, 16s) makes sense for thousands of QPS. For 1-10 queries per source, it just adds latency.
- **Idempotency isn't a concern.** A search query isn't a payment or state-changing op. The cost of failing fast is low.

3s + retry-once + stop-after-3 is the minimal viable retry for ad-hoc research workflows.

## Concurrent Execution in Practice

The skill calls phases concurrently via the harness's native parallelism (Claude's tool-call batching). The mechanical pattern:

```
1. Build the query list for each platform after intake.
2. Issue all "first queries" in one tool-call batch:
     [Reddit Q1, HN Q1, Web Q1]
3. After Q1 batch returns, issue Q2 batch:
     [Reddit Q2, HN Q2, Web Q2]
4. After Q2, issue Q3 batch (Reddit-only at this point since HN has 2 queries, Web has 2-3):
     [Reddit Q3]
5. Phase 4 (X/Twitter) sequential, last.
```

This achieves parallel across platforms while staying sequential within each.

## Operational Checklist

- [ ] Phases 1, 2, 3 fire in parallel (first query of each in the same tool-call batch)
- [ ] Within each platform, sequential queries 1 q/sec
- [ ] Phase 4 runs last, sequentially
- [ ] On 429 / rate-limit header signaling exhaustion: stop that source, continue others
- [ ] On any failure: 3s + retry-once before marking source-failed
- [ ] On 3 consecutive failures across all sources: stop entire run
- [ ] Log every retry + every source-failed to the audit log via `citation_tracker.py`

## Citations (7 sources)

1. **Google SRE Workbook — Chapter 5 ("Alerting on SLOs"), Chapter 17 ("Non-Abstract Large System Design"), Chapter 22 ("Addressing Cascading Failures").** Source for the "graceful degradation on partial failure" pattern. The SRE Workbook's framing of "don't take down the whole system when one component fails" applies directly to pulse: one source failing doesn't fail the briefing. https://sre.google/workbook/

2. **IETF RFC 6585 — *Additional HTTP Status Codes* (2012).** Source for the 429 ("Too Many Requests") + `Retry-After` header semantics. The RFC formalizes the server-side rate-limit signaling that Rule 5 (plan-tier detection) honors. https://datatracker.ietf.org/doc/html/rfc6585

3. **Mike Cohen, "Exponential Backoff and Jitter" — AWS Architecture Blog, 2015.** Argues for exponential-backoff-with-jitter at production scale. Source for the inverse argument: at research-workflow scale (10s of queries, not millions), exponential backoff is overkill — fail fast is better UX. https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/

4. **Reddit's API documentation + community findings (e.g., `praw` library source code).** Source for the 1 q/sec unauthenticated rate-limit empirical ceiling. The `praw` library's hardcoded conservative throttling is the de-facto community standard.

5. **Algolia documentation — algolia.com/doc.** Source for the HN Algolia endpoint's documented behavior (no hard rate limit on the public HN index, but politeness expected for shared infrastructure).

6. **Concurrent execution patterns in Python — `concurrent.futures` and `asyncio` standard-library documentation.** Source for the "batch concurrent then synchronize" pattern that the skill uses via the harness's tool-call batching. Even though the skill itself doesn't invoke concurrent.futures directly, the conceptual model is the same.

7. **Marc Brooker, "Timeouts, retries, and backoff with jitter" — AWS Builders' Library, 2019.** Source for the consecutive-failure counter pattern. Brooker's argument that "consecutive failures across sources indicate systemic issues, not transient ones" is the rationale for stop-after-3-consecutive.
