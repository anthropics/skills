# Multi-Agent Coordination Strategies

## Patterns

### Fan-Out / Fan-In

The simplest and most common pattern. One coordinator dispatches the same task to N agents, waits for all to complete, then evaluates.

```
         ┌─ Agent 1 ─┐
Task ──> ├─ Agent 2 ─┤ ──> Evaluate ──> Merge Winner
         └─ Agent 3 ─┘
```

**When to use**: Optimization tasks, competitive solutions, exploring diverse approaches, competing content drafts, vendor evaluation.

**Agent count**: 2-5 (diminishing returns beyond 5 for most tasks).

**Eval**: Metric-based preferred. LLM judge for subjective quality.

### Tournament

Multiple rounds of fan-out/fan-in. Losers are eliminated, winners advance. Each round can refine the task or increase difficulty.

```
Round 1:  A1, A2, A3, A4  →  Eval  →  A2, A4 advance
Round 2:  A2, A4           →  Eval  →  A2 wins
```

**When to use**: Complex optimization where iterative refinement helps. Each round builds on the previous winner.

**Implementation**:
1. Run `/hub:init` + `/hub:spawn` for round 1
2. Eval, merge winner into a new base branch
3. Run `/hub:init` again with the merged branch as base
4. Repeat until convergence or budget exhausted

### Ensemble

All agents' work is combined rather than selecting a winner. Useful when agents solve different parts of a problem.

```
Agent 1: solves auth module
Agent 2: solves API routes       ──> Cherry-pick all ──> Combined result
Agent 3: solves database layer
```

**When to use**: Large tasks that decompose into independent subtasks. Each agent gets a different piece.

**Implementation**:
1. In `/hub:init`, give each agent a DIFFERENT task (subtask of the whole)
2. Spawn with unique dispatch posts per agent
3. Instead of `/hub:eval` ranking, manually cherry-pick from each
4. Or merge sequentially: merge agent-1, then merge agent-2 on top

### Pipeline

Agents work sequentially — each builds on the previous agent's output. Like a relay race.

```
Agent 1 (design) → Agent 2 (implement) → Agent 3 (test) → Agent 4 (optimize)
```

**When to use**: Tasks with natural phases (design → implement → test). Each phase needs different expertise.

**Implementation**:
1. Spawn agent-1 alone, wait for completion
2. Merge agent-1's work, spawn agent-2 from that base
3. Repeat for each pipeline stage
4. Each agent reads the previous agent's result post for context

## Agent Configuration

### Task Decomposition

For fan-out, all agents get the same task. But you can add variation:

| Strategy | Dispatch Difference | Use Case |
|----------|-------------------|----------|
| **Identical** | Same prompt to all | Pure competition |
| **Constrained** | Same goal, different constraints | "Use caching" vs "Use indexing" |
| **Seeded** | Same goal, different starting hints | Explore different parts of solution space |
| **Role-varied** | Same goal, different personas | "As a performance engineer" vs "As a DBA" |

### Agent Count Guidelines

| Task Complexity | Agents | Rationale |
|----------------|--------|-----------|
| Simple optimization | 2 | Two approaches is usually enough |
| Medium complexity | 3 | Three diverse approaches, manageable eval |
| Complex / creative | 4-5 | More exploration, but eval cost increases |
| Subtask decomposition | N = subtasks | One agent per subtask (ensemble pattern) |

## Evaluation Strategies

### Metric-Based (Objective)

Best when a clear numeric metric exists:

| Metric Type | Example | Direction |
|-------------|---------|-----------|
| Latency | p50_ms, p99_ms | lower |
| Throughput | rps, qps | higher |
| Size | bundle_kb, image_bytes | lower |
| Score | test_pass_rate, accuracy | higher |
| Count | error_count, warnings | lower |
| Word count | word_count | higher |
| Readability | flesch_score | higher |
| Conversion | cta_click_rate | higher |

### LLM Judge (Subjective)

Best when quality is subjective or multi-dimensional:

Judging criteria (in order of importance):
1. **Correctness** — Does it solve the stated task?
2. **Completeness** — Does it handle edge cases?
3. **Simplicity** — Fewer lines changed = less risk
4. **Quality** — Clean execution, good structure, no anti-patterns
5. **Performance** — Efficient algorithms and data structures

### Hybrid

1. Run metric eval to get objective ranking
2. If top-2 agents are within 10% of each other, use LLM judge
3. Weight: 70% metric, 30% qualitative

## Failure Handling

### All Agents Fail

```
Signal: All agents return errors or no improvement
Action:
  1. Post failure summary to board
  2. Archive session (state → archived)
  3. Suggest: "Try with different constraints, more agents, or simplified task"
  4. Do NOT auto-retry without user approval
```

### Partial Failure

```
Signal: Some agents fail, others succeed
Action:
  1. Evaluate only successful agents
  2. Note failures in eval summary
  3. Proceed with merge if any agent succeeded
```

### No Improvement

```
Signal: All agents complete but none improve on baseline
Action:
  1. Show results with negative deltas
  2. Suggest: "Current implementation may already be near-optimal"
  3. Archive session
```

## Communication Protocol

### Board Usage by Phase

| Phase | Channel | Content |
|-------|---------|---------|
| Dispatch | `dispatch/` | Task assignment per agent |
| Working | `progress/` | Agent status updates (optional) |
| Complete | `results/` | Final result summary per agent |
| Merge | `results/` | Merge summary from coordinator |

### Result Post Template

Agents should write results in this format:

```markdown
## Result Summary

- **Approach**: {one-line description of strategy}
- **Files changed**: {count}
- **Key changes**: {bullet list of main modifications}
- **Metric**: {value} (baseline: {baseline}, delta: {delta})
- **Tests**: {pass/fail status}
- **Confidence**: {High/Medium/Low} — {reason}
- **Limitations**: {known issues or edge cases}
```
