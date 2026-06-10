# Reporting Reference

Use this file when writing `report.md` or `compare` route output.

## Report structure

Write to `.perf/runs/<run-folder>/report.md` using this shape:

```markdown
# Performance Report — {package}

**Date:** {timestamp}
**Scenario:** {startup|ui|freeze}
**Device:** {model} — Android {version}
**Score: {total}/{max}**

## Capture Quality
{USB powered, thermal state, missing data sources, or other caveats}

## Score Breakdown
| Category | Score | Rating | Confidence |
|----------|-------|--------|------------|

## Cold Start Timeline (startup scenario)
| Event | Duration (ms) | Notes |
|-------|--------------|-------|

## Frame Performance
{adjusted jank rate or gfxinfo-backed frame health, worst frames, jank type breakdown}

## Memory
{RSS growth pattern, classification, meminfo breakdown if available}

## GC Pressure
{event count, total duration, correlation with jank}

## CPU & Threading
| Root Cause | Events | Total Blocked (ms) | Max (ms) | Waiters | Affected Threads |
|-----------|--------|-------------------|---------|---------|-----------------|

## Binder IPC
{slow calls, which threads, which servers}

## Additional Findings
{anything discovered beyond the default checklist}

## Recommendations
{ranked by likely impact, tied to evidence, explicit about confidence}
```

## Startup timeline guidance

- Lead with `am start -W` `TotalTime`.
- Present startup in chronological order with nesting.
- Separate **build-level** costs (DEX, JIT, class verification) from **code-level** costs (SDK init, DI, view inflation).
- Call out `bindApplication`, `performCreate`, major sub-costs, and whether `reportFullyDrawn` is absent.
- Do not double-count nested slices.

Example rows:

| Event | Duration (ms) | Notes |
|-------|--------------|-------|
| **am start -W TotalTime** | **1352** | **COLD** |
| `bindApplication` | **331.1** | Application startup |
| — DEX loading | 33.9 | Build-level |
| — SDK init | 130.8 | Defer if non-critical |
| `performCreate:SingleActivity` | **515.9** | Activity creation |
| First `Choreographer#doFrame` | — | TTFF marker |

## Score breakdown guidance

Use this rubric for `Score Breakdown`:

| Category | Max | EXCELLENT | GOOD | ACCEPTABLE | POOR |
|----------|-----|-----------|------|------------|------|
| Frame Performance | 30 | <1% adjusted jank = 30 | 1-5% = 24 | 5-10% = 15 | >10% = 5 |
| ANR Stability | 25 | 0 ANRs = 25 | - | 1 ANR = 10 | 2+ = 5 |
| Memory Health | 20 | Stabilized <400MB = 20 | Stabilized 400-700MB = 14 | >700MB or unclear = 8 | Likely leak = 0 |
| CPU/Threading | 15 | No contention >50ms = 15 | Minor = 10 | Main blocked >200ms = 3 | - |
| Binder IPC | 10 | No main-thread >100ms = 10 | Minor = 7 | ANR-risk calls = 2 | - |

If a category cannot be scored because data is missing, note it and reduce the denominator instead of guessing.

Startup-specific scoring caveats:

- If fewer than 30 frame rows are present, do not score `Frame Performance`.
- Do not use startup jank percentage as the headline comparison metric across devices.
- Prefer startup timeline phases, `am start -W`, DEX state, JIT pressure, and memory context.

## CPU and threading guidance

- Present top threads by CPU time.
- Group `monitor_contention` events by lock owner `class.method`.
- Rank contention by total blocked time, not max single event.
- Note `waiters=N` when useful.
- Classify each root cause as app, SDK, or system/framework when possible.

Example contention rows:

| Root Cause | Events | Total Blocked (ms) | Max (ms) | Waiters | Affected Threads |
|-----------|--------|-------------------|---------|---------|-----------------|
| **SdkHeartbeat.register()** | 7 | **471.9** | 151.0 | up to 3 | SDK background threads |
| NetworkClient.newStream() | 3 | 80.5 | 32.4 | 1 | Networking threads |
| DaggerSingletonC.get() | 1 | 29.4 | 29.4 | 0 | DefaultDispatcher |

## Confidence states

Use one of these for every finding:

- **Issue found** — evidence is clear
- **Likely issue, low confidence** — evidence suggests a problem but is not conclusive
- **No issue found** — checked and looks fine
- **Insufficient data** — trace too short, scenario not captured, or data source missing

## History append

Append one JSON line to `.perf/history.jsonl`:

```json
{"timestamp":"...","scenario":"...","score":76,"frames":24,"anr":25,"memory":14,"cpu":8,"binder":7,"adjusted_jank_pct":4.54,"raw_jank_pct":12.16,"rss_peak_mb":571,"gc_events":14,"gc_total_ms":906}
```

## Compare guidance

For the `compare` route:

1. List what changed: device, app version, scenario, thermal state, DEX state.
2. Compare key metrics side by side: startup time, adjusted jank or gfxinfo frame health, RSS peak, GC count, top contention.
3. Flag regressions and improvements with magnitude.
4. Say when a difference is likely noise rather than a real change.

Important caveats:

- If DEX extraction/verification differs between runs, startup timing is not directly comparable. Compare only the non-DEX portions.
- If either startup run has fewer than 30 frame rows, do not compare startup jank percentages.
- Cross-device comparisons should focus more on relative proportions than absolute timings.

## Report view guidance

- If a report exists, summarize the latest score, scenario, top findings, and top recommendations first.
- If history has two or more entries, show the recent trend and delta before drilling into the latest run.
- If no report exists yet, say that no analyzed run is available and point the user to `analyze` or the default route.
