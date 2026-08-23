---
name: hivemind
description: Orchestrate free opencode worker agents from Claude Code to cut token costs. Spawn single workers or parallel swarms (scout/coder/tester) that run headless on $0 models, with worktree isolation and compact JSON results. Use when the user wants to delegate grunt work, save Claude quota/tokens, run benchmarks vs opencode, or says "spawn a worker", "swarm", "delegate to opencode", or "/oc".
---

# Hivemind: Claude Code as Orchestrator, opencode as Free Worker Swarm

Claude Code = brain (plans, reviews, merges). opencode = disposable workers on free models
(`opencode/mimo-v2.5-free` default; verified $0.00 per run).

## Prerequisites (external dependency)

This skill is a thin orchestration layer over **[opencode](https://opencode.ai)**, a
third-party CLI. It is not bundled — install and authenticate it yourself first:

| Requirement | Notes |
|---|---|
| Node.js >= 18 | The scripts use `fetch` and `node:timers/promises`. |
| `opencode` CLI on `PATH` | `npm i -g opencode-ai` (or the installer opencode documents). |
| An authenticated opencode account | `opencode auth login`. Workers run as your account. |
| Default model `opencode/mimo-v2.5-free` | A free tier offered by opencode, not by Anthropic. Availability, rate limits, and pricing are opencode's to change — override with `--model` at any time. |
| Windows only: `OPENCODE_GIT_BASH_PATH` | Point at `C:\Program Files\Git\bin\bash.exe`, set persistently. |

Nothing here calls the Anthropic API on the worker side; worker traffic goes to
opencode's endpoints. Do not delegate secrets or private code you would not send there.

## Setup

1. Put this skill folder wherever your agent loads skills from (e.g. `~/.claude/skills/hivemind`).
2. Export `HIVEMIND_HOME` pointing at that folder — the bundled slash commands use it:
   ```
   export HIVEMIND_HOME="$HOME/.claude/skills/hivemind"
   ```
3. Copy the bundled assets into place:
   - `assets/commands/*.md` -> `~/.claude/commands/` (the `/hive`, `/oc`, `/swarm`, ... entry points)
   - `assets/agents/*.md` -> `~/.config/opencode/agent/` (the scout / coder / tester worker personas)

Both copies are optional: everything the commands do can be driven by invoking
`scripts/oc-worker.mjs` directly, and any opencode agent name works with `--agent`.

Runtime state (`.runs/*.jsonl`) is written inside this folder and is gitignored.

## Components

| Path (relative to this skill dir) | Purpose |
|---|---|
| `scripts/oc-worker.mjs` | ONLY sanctioned way to invoke a worker. Hardened join point. |
| `scripts/oc-status.mjs` | Fleet progress from run logs (`oc-status.mjs <run-id>`) |
| `scripts/oc-aggregate.mjs` | Dedupe/synthesize N worker outputs; consensus findings first |
| `scripts/bench/run-bench.mjs` | Benchmark configs A (claude solo), B (opencode solo), C (orchestrated swarm) |
| `scripts/bench/grader-prompt.md` | Blind grading rubric (max 12 pts + PASS/FAIL gate) |
| `assets/commands/` | Slash-command entry points to copy into `~/.claude/commands/` |
| `assets/agents/` | scout / coder / tester agent definitions for opencode |

Slash commands (ship in `assets/commands/`, copy to `~/.claude/commands/`):
- `/hive <task>` - AUTO-ROUTER. Classifies task -> single worker, generic swarm, or template. Default entry point; prefer this over manual routing.
- `/oc <task>` - single worker delegation
- `/swarm <task>` - generic parallel swarm
- `/review-panel <diff>` - 4-lens parallel review (correctness/security/performance/style) + consensus aggregation
- `/research-sweep <question>` - 3-5 parallel research angles, synthesized
- `/migration <task>` - batched per-worktree migration workers + sequenced merge
- `/test-fleet <target>` - partitioned parallel test runs with safety checks

Worker agents (ship in `assets/agents/`, copy to `~/.config/opencode/agent/`):
- **scout** - read-only research (no write/edit/bash)
- **coder** - implements one subtask in its worktree
- **tester** - runs tests only, never edits source

## Invocation contract

```
node "<skill-dir>\scripts\oc-worker.mjs" [--agent scout|coder|tester] [--dir <path>] [--model <p/m>] [--timeout 900] [--run <id> --label <name>] "TASK TEXT"
```

Returns exactly ONE compact JSON line:
`{ ok, result, tokens:{total,input,output,cache}, cost_usd, duration_ms, label, agent, model }`

On failure: `{ ok:false, stage:"args"|"exec"|"api"|"parse"|"empty", error }` with stderr capped at 300 chars.

`--run <id>` + `--label <name>` append lifecycle events (start/done/fail) to `.runs/<id>.jsonl`
inside this skill dir. Use them for EVERY swarm worker so progress is recoverable via
`oc-status.mjs` even after orchestrator context loss.

The script auto-manages the shared server: health-checks `127.0.0.1:4096`, spawns `opencode serve` if dead, waits 5s, falls back to cold start. Workers are idempotent against their `--dir`; re-run once on `ok:false` before giving up.

## Golden Rule (non-negotiable)

Raw opencode NDJSON streams must NEVER enter your context. All output arrives via the
script's single JSON line. Never pipe `opencode run --format json` directly into this
conversation; never re-implement what the script does.

## Single worker flow (/oc)

For one read-only question or small delegation: run oc-worker.mjs without worktrees.
Read-only tasks may omit `--agent`/`--dir`. Summarize `result` for the user.
If files were written: show `git diff` before letting the user commit.

## Swarm flow (multi-worker)

1. Decompose task into 2-5 INDEPENDENT subtasks (no shared files).
2. Writing workers get isolated worktrees FIRST: `git worktree add ../<repo>-wt-N -b swarm/N`.
3. Issue ALL worker invocations as PARALLEL Bash tool calls in ONE message.
4. Review every diff yourself (`git diff main...swarm/N`). YOU are the only merger.
5. Merge approved branches, remove worktrees, run tests.
6. Report table: subtask | agent | tokens | outcome + total worker tokens.

HARD RULES: workers never share directories; never delegate merging/reviewing;
escalate to your own Sonnet only when a free-model worker demonstrably fails twice.

## Benchmarking

```
node scripts\bench\run-bench.mjs --repo <project> [--configs a,b,c] [--task 1-5]
```
Appends JSONL records (ts, config, tokens, cost, duration) to `bench-results.jsonl`.
Grade artifacts blind with `grader-prompt.md` (grader sees only task spec + output).
Configs: A=claude solo baseline, B=opencode solo, C=claude orchestrating 2 workers.

## Fallback ladder (all flows)

1. Worker `ok:false` -> re-invoke once against the same dir.
2. Still failing -> orchestrator performs that subtask inline, marks it `[orchestrator-sourced]`.
3. opencode entirely down (`exec`/`api` twice) -> announce, abandon workers, do the task directly.
Never let a swarm fail a task that Claude could have done itself.

## Fleet patterns

Four reusable topologies ship as slash commands (see table above). Shared invariants:
parallel spawns in one message; `--run/--label` on every worker; aggregation via
`oc-aggregate.mjs` when 3+ workers produce findings; consensus beats single-lens claims;
worktree isolation whenever any worker writes.

## Windows notes (hard-won)

- Requires `OPENCODE_GIT_BASH_PATH=C:\Program Files\Git\bin\bash.exe` (set persistently).
- The script resolves the REAL `opencode.exe` by parsing the npm `.cmd` shim — Node's
  EINVAL policy blocks spawning `.cmd` directly. Do not "simplify" resolver back to
  `where.exe` first-line.
- Free models: `opencode/mimo-v2.5-free`, `opencode/nemotron-3.5-lightning-free`,
  `opencode/hy3-free`. NOTE: `opencode-go/*` models require workspace billing — avoid.

## Known limits

- Free-tier rate limits can 429 under heavy swarms; space out retries.
- Worker quality varies; always review diffs. Scout answers are evidence-cited.
- Bench config C consumes real Claude tokens for orchestration (~1-2k/task).
