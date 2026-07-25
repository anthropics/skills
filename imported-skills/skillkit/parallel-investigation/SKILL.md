---
name: parallel-investigation
description: Coordinates parallel investigation threads to simultaneously explore multiple hypotheses or root causes across different system areas. Use when debugging production incidents, slow API performance, multi-system integration failures, or complex bugs where the root cause is unclear and multiple plausible theories exist; when serial troubleshooting is too slow; or when multiple investigators can divide root-cause analysis work. Provides structured phases for problem decomposition, thread assignment, sync points with Continue/Pivot/Converge decisions, and final report synthesis.
version: 1.0.0
triggers:
  - investigate in parallel
  - multiple approaches
  - divide investigation
  - complex problem
  - explore options
tags:
  - collaboration
  - investigation
  - parallel
  - problem-solving
difficulty: advanced
estimatedTime: 15
relatedSkills:
  - debugging/root-cause-analysis
  - collaboration/handoff-protocols
---

# Parallel Investigation

Coordinate parallel investigation threads to explore multiple hypotheses simultaneously. Most effective for production incidents, performance regressions, or integration failures where the root cause is unclear.

## Core Principle

**When uncertain, explore multiple paths in parallel. Converge when evidence points to an answer.**

Parallel investigation reduces time-to-solution by eliminating serial bottlenecks.

## Investigation Structure

### Phase 1: Problem Decomposition

Break the problem into independent investigation threads:

```
Problem: API responses are slow

Investigation Threads:
├── Thread A: Database performance
│   └── Check slow queries, indexes, connection pool
├── Thread B: Application code
│   └── Profile endpoint handlers, check for N+1
├── Thread C: Infrastructure
│   └── Check CPU, memory, network latency
└── Thread D: External services
    └── Check third-party API response times
```

Each thread should be independent (no blocking dependencies), focused (clear scope), and time-boxed.

### Phase 2: Thread Assignment

Assign threads with clear ownership:

```markdown
## Thread A: Database Performance
**Investigator:** [Name/Agent A]
**Duration:** 30 minutes
**Scope:**
- Query execution times
- Index utilization
- Connection pool metrics
**Report Format:** Summary + evidence
```

### Phase 3: Parallel Execution

Each thread follows this pattern:

1. Gather evidence specific to thread scope
2. Document findings as you go
3. Identify if thread is a lead or dead end
4. Prepare summary for sync point

**Thread Log Template:**
```markdown
## Thread: [Name]
**Start:** [Time]

### Findings
- [Timestamp] [Finding]

### Evidence
- [Log/Metric/Screenshot]

### Preliminary Conclusion
[What this thread suggests about the problem]
```

### Phase 4: Sync Points

Regular convergence to share findings:

```
Sync Point Agenda:
1. Each thread report (2 min each)
2. Discussion & correlation (5 min)
3. Decision: Continue, Pivot, or Converge (3 min)
```

**Sync Point Decisions:**
- **Continue**: Threads are progressing, maintain parallel execution
- **Pivot**: Redirect threads based on new evidence
- **Converge**: One thread found the answer, others join to validate

### Phase 5: Convergence

When a thread identifies the likely cause:

1. **Validate** — Other threads verify the finding
2. **Deep dive** — Focused investigation on identified cause
3. **Document** — Compile findings from all threads

## Coordination Patterns

**Hub and Spoke**: One coordinator assigns threads, tracks progress, calls sync points, and makes convergence decisions. Best when one person has the most context.

**Peer Network**: Equal investigators post findings to a shared channel and self-organize convergence when a pattern emerges. Best when investigators have similar expertise.

## Communication Protocol

### During Investigation

```
[Thread A] [Status] Starting query analysis
[Thread B] [Finding] No N+1 patterns in user endpoint
[Thread A] [Finding] Slow query: SELECT * FROM orders WHERE...
[Thread C] [Dead End] CPU and memory within normal
[Thread A] [Hot Lead] Missing index on orders.user_id
```

### At Sync Point

```markdown
## Thread A Summary

**Status:** Hot Lead
**Key Finding:** Missing index on orders.user_id
**Evidence:** Query taking 3.2s, explain shows full table scan
**Recommendation:** Likely root cause — suggest converge
```

## Decision Framework

| Thread Status | Action |
|---------------|--------|
| All exploring | Continue parallel |
| One hot lead | Validate lead, others support |
| Multiple leads | Prioritize by evidence strength |
| All dead ends | Reframe problem, new threads |
| Confirmed cause | Converge, begin fix |

## Time Management

A typical two-hour investigation:

```
0:00  Problem decomposition & thread assignment
0:15  Parallel investigation begins
0:45  Sync point #1 → Continue/Pivot/Converge decision
1:30  Sync point #2 (if continuing)
1:35  Final convergence & documentation
```

Adjust sync point cadence based on incident severity — every 20 minutes for critical outages, every 45 minutes for lower-urgency investigations.

## Documentation

### Final Report Structure

```markdown
# Investigation: [Problem]

## Summary
[Brief description and resolution]

## Threads Explored

### Thread A: [Area]
- Investigator: [Name]
- Findings: [Summary]
- Outcome: [Lead / Dead End / Root Cause]

## Root Cause
[Detailed explanation of what was found]

## Evidence
- [Evidence 1]
- [Evidence 2]

## Resolution
[What was done to fix]

## Lessons Learned
- [Learning 1]
```

## Integration with Other Skills

- **debugging/root-cause-analysis**: Each thread follows RCA principles
- **debugging/hypothesis-testing**: Threads test specific hypotheses
- **handoff-protocols**: When passing a thread to another person
