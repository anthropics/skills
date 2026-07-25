# Workflow API Reference

Complete surface for Claude Code's Workflow tool: every global, option, cap, and constant a workflow `.js` file can rely on. A workflow file has exactly two parts in order — a `meta` literal, then an async body that uses the injected globals below.

## 1. `meta` declaration

`meta` must be the **first statement** and a **pure object literal** — no variables, spreads, template strings, or function calls inside it. Reserved keys (`__proto__`, `constructor`, `prototype`) are rejected by the parser.

```js
export const meta = {
  name: 'workflow-name',            // required, non-empty string
  description: 'One-line summary',  // required
  whenToUse: 'When to run this',    // optional
  phases: [                         // optional, one entry per phase() call
    { title: 'Phase Name', detail: 'Description', model: 'haiku' }
  ]
}
```

## 2. Injected globals

| Global | Signature | Returns |
|--------|-----------|---------|
| `agent()` | `agent(prompt, opts?) → Promise<string\|object>` | Text, or a validated object when `schema` is set |
| `pipeline()` | `pipeline(items, ...stages) → Promise<any[]>` | Streamed per-item results (no barrier between stages) |
| `parallel()` | `parallel(thunks) → Promise<any[]>` | Concurrent results (barrier — waits for all) |
| `phase()` | `phase(title) → void` | Groups subsequent agents under a heading |
| `log()` | `log(message) → void` | Narrator output to the workflow log |
| `console` | `.log()`, `.error()`, … | Routed into the workflow log |
| `workflow()` | `workflow(nameOrRef, args?) → Promise<any>` | Result of a nested workflow (one level deep max) |
| `args` | any | The input passed to the workflow, unchanged |
| `budget` | `{ total, spent(), remaining() }` | Token tracking |

## 3. `agent()` options

```js
agent(prompt, {
  label: 'string',           // display name (~60 char default)
  phase: 'phase-name',       // progress-group assignment
  schema: { type: 'object' },// JSON Schema — validates + structures the return
  model: 'haiku',            // 'haiku' | 'sonnet' | 'opus' | 'inherit' | full-model-id
  isolation: 'worktree',     // run in a fresh git worktree (~200-500 ms + disk)
  agentType: 'agent-type',   // custom sub-agent type
  stallMs: 180000            // per-agent stall timeout override (ms)
})
```

**Model resolution:** `haiku`/`sonnet`/`opus` resolve to the current default of that family; `inherit` (the default) uses the session main-loop model; a full model ID passes through unchanged. Pick lighter models (Haiku) for classification/extraction and heavier ones (Opus) for synthesis or hard reasoning.

**Resume cache key** includes `schema`, `model`, `isolation`, and `agentType` — changing any of these re-runs the agent on resume. `label` and `phase` do **not** invalidate the cache.

## 4. `pipeline()` vs `parallel()`

**`pipeline(items, stage1, stage2, …)`** — each item flows through every stage independently; there is no barrier between stages, so stage 2 starts for an item the moment stage 1 finishes for *that* item. Stage callbacks receive `(prevResult, originalItem, index)`. Wall-clock time ≈ the slowest single item's full chain, not the sum of slowest-per-stage. **Default choice for multi-stage work.**

**`parallel(thunks)`** — runs an array of `() => Promise` thunks concurrently and waits for all (a barrier). Use only when the next step genuinely needs the entire prior result set — dedup, merge, or a count-based exit. Requires thunks, not bare promises: `parallel([() => agent(a), () => agent(b)])`.

## 5. `budget` object

```js
budget.total        // user-set target, or null if none
budget.spent()      // output tokens spent this turn
budget.remaining()  // max(0, total - spent()), or Infinity when total is null
```

Throws `WorkflowBudgetExceededError` once `spent()` reaches `total`. Use `budget.remaining()` as a loop guard for depth-scaling workflows.

## 6. Caps & limits

| Limit | Value | Behavior on breach |
|-------|-------|--------------------|
| Agent calls per run | 1000 | throws `WorkflowAgentCapError` |
| Concurrent agents | `min(16, max(2, cores − 2))` | excess calls queue |
| Script size | 524,288 bytes | rejected before parsing |
| Per-agent stall | 180,000 ms (3 min) | aborted, retried up to 5× |
| Sync timeout | 30,000 ms | catches infinite synchronous loops |

## 7. Sandbox restrictions

**Banned (non-reproducible — break resume):**
- `Math.random()` → vary the agent prompt by index instead.
- `Date.now()` → pass timestamps in via `args`.
- argless `new Date()` → use `new Date(specificValue)`.

**No access** to filesystem, Node APIs (`require`, `fs`, `process`), or network from the orchestrator. Any work needing those must happen *inside* an `agent()` call (the sub-agent has full tool access).

## 8. Execution & resume

1. The script is persisted to the session directory.
2. A background task launches and returns a run ID (`wf_…`).
3. A journal records each `agent()` call keyed by a hash of `(prompt, opts)`.
4. Resume via `Workflow({ scriptPath, resumeFromRunId })` — cached calls return instantly; only changed or new calls re-run. Resume works **same-session only**; edit the saved file and re-invoke with `scriptPath`.

## 9. Enabling the feature

The Workflow tool is gated behind an environment variable and off by default:

```bash
export CLAUDE_CODE_WORKFLOWS=1
```

Save workflow files under `.claude/workflows/` in the project, then browse, launch, and monitor them with the `/workflows` slash command. **P** pauses/resumes a run; **X** skips a sub-agent.

---

## Sources

1. Anthropic — Claude Code documentation, Workflow tool & `/workflows` (code.claude.com/docs).
2. Ray Amjad — `claude-code-workflow-creator`, `references/api-reference.md` (github.com/ray-amjad/claude-code-workflow-creator).
3. Anthropic — Claude Code changelog, v2.1.147 release notes (Workflow tool introduction).
4. Anthropic — sub-agents & the Agent tool documentation (fresh-context isolation model).
5. Anthropic — Claude Agent SDK: orchestration and background-task execution patterns.
6. JSON Schema specification (json-schema.org) — the `schema` option's validation contract.
7. Node.js / ECMAScript — async/await and `Promise.all` semantics underlying `parallel()`.
8. Google SRE Workbook — error-budget discipline, analogous to the `budget` guard pattern.
