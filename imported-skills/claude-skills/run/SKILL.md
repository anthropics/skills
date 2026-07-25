---
name: "run"
description: "One-shot lifecycle command that chains init → baseline → spawn → eval → merge in a single invocation. Use when the user runs /hub:run or asks to execute a full AgentHub competition end-to-end."
command: /hub:run
---

# /hub:run — One-Shot Lifecycle

Run the full AgentHub lifecycle in one command: initialize, capture baseline, spawn agents, evaluate results, and merge the winner.

## Usage

```
/hub:run --task "Reduce p50 latency" --agents 3 \
  --eval "pytest bench.py --json" --metric p50_ms --direction lower \
  --template optimizer

/hub:run --task "Refactor auth module" --agents 2 --template refactorer

/hub:run --task "Cover untested utils" --agents 3 \
  --eval "pytest --cov=utils --cov-report=json" --metric coverage_pct --direction higher \
  --template test-writer

/hub:run --task "Write 3 email subject lines for spring sale campaign" --agents 3 --judge
```

## Parameters

| Parameter | Required | Description |
|-----------|----------|-------------|
| `--task` | Yes | Task description for agents |
| `--agents` | No | Number of parallel agents (default: 3) |
| `--eval` | No | Eval command to measure results (skip for LLM judge mode) |
| `--metric` | No | Metric name to extract from eval output (required if `--eval` given) |
| `--direction` | No | `lower` or `higher` — which direction is better (required if `--metric` given) |
| `--template` | No | Agent template: `optimizer`, `refactorer`, `test-writer`, `bug-fixer` |

## What It Does

Execute these steps sequentially:

### Step 1: Initialize

Run `/hub:init` with the provided arguments:

```bash
python {skill_path}/scripts/hub_init.py \
  --task "{task}" --agents {N} \
  [--eval "{eval_cmd}"] [--metric {metric}] [--direction {direction}]
```

Display the session ID to the user.

### Step 2: Capture Baseline

If `--eval` was provided:

1. Run the eval command in the current working directory
2. Extract the metric value from stdout
3. Display: `Baseline captured: {metric} = {value}`
4. Append `baseline: {value}` to `.agenthub/sessions/{session-id}/config.yaml`

If no `--eval` was provided, skip this step.

### Step 3: Spawn Agents

Run `/hub:spawn` with the session ID.

If `--template` was provided, use the template dispatch prompt from `../agenthub/references/agent-templates.md` instead of the default dispatch prompt. Pass the eval command, metric, and baseline to the template variables.

Launch all agents in a single message with multiple Agent tool calls (true parallelism).

### Step 4: Wait and Monitor

After spawning, inform the user that agents are running. When all agents complete (Agent tool returns results):

1. Display a brief summary of each agent's work
2. Proceed to evaluation

### Step 5: Evaluate

Run `/hub:eval` with the session ID:

- If `--eval` was provided: metric-based ranking with `result_ranker.py`
- If no `--eval`: LLM judge mode (coordinator reads diffs and ranks)

If baseline was captured, pass `--baseline {value}` to `result_ranker.py` so deltas are shown.

Display the ranked results table.

### Step 6: Confirm and Merge

Present the results to the user and ask for confirmation:

```
Agent-2 is the winner (128ms, -52ms from baseline).
Merge agent-2's branch? [Y/n]
```

If confirmed, run `/hub:merge`. If declined, inform the user they can:
- `/hub:merge --agent agent-{N}` to pick a different winner
- `/hub:eval --judge` to re-evaluate with LLM judge
- Inspect branches manually

## Critical Rules

- **Sequential execution** — each step depends on the previous
- **Stop on failure** — if any step fails, report the error and stop
- **User confirms merge** — never auto-merge without asking
- **Template is optional** — without `--template`, agents use the default dispatch prompt from `/hub:spawn`
