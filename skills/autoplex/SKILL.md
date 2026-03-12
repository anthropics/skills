---
name: autoplex
description: >
  Autonomously execute multi-phase task plans via shell scripts that invoke
  Claude Code in headless mode (claude -p). Each task runs in a fresh session
  with full methodology: context loading, parallel research subagents,
  implementation, verification, cross-verification, commit, and progress update.
  Phase-end cross-review audits gate quality. Failure-type-aware retry
  (context overflow, rate limit, budget exceeded) ensures robustness. Runs in
  tmux for background execution.
  Use when: (1) user has a task_plan.md with phased tasks and wants to execute
  them autonomously, (2) user says "run the plan", "execute tasks", "automate
  the phases", "run overnight", or similar, (3) user wants to batch-execute
  tasks from a planning-with-files session without babysitting, (4) user
  references autonomous execution, headless loops, or unattended agent runs,
  (5) user wants to continue executing remaining tasks from a prior run,
  (6) user asks how to run Claude Code tasks in a loop or batch mode.
  Do NOT use for: single-task execution, interactive coding, plan creation
  (use the plan skill instead), or tasks without an existing task_plan.md.
---

# Autoplex

Execute a multi-phase `task_plan.md` unattended via `claude -p` headless sessions, with per-task retry, phase-end cross-review audits, and tmux-based monitoring.

Full documentation and executor script template: https://github.com/ZenAlexa/autoplex

## When to Use

- A `task_plan.md` exists (created via the planning-with-files pattern)
- The plan has multiple tasks organized into phases
- The user wants autonomous, unattended execution
- Tasks are independent enough to run in separate Claude sessions

## Prerequisites

- `claude` CLI installed and authenticated
- Project is a git repository
- Plan directory contains: `task_plan.md`, `progress.md` (and optionally `findings.md`)

## How It Works

The executor generates a bash script that loops through tasks sequentially. Each task invocation is a fresh `claude -p` session (automatic context clearing):

```
For each task in phase order:
  1. Check progress.md — skip if already DONE
  2. Generate a structured prompt with full 6-step methodology
  3. Invoke: claude -p < prompt_file --model opus --effort max
  4. On failure: detect failure type, adapt prompt, retry (up to 2x)
  5. On success: log result, notify, continue

After all tasks in a phase:
  6. Run phase-level cross-review audit (separate claude -p session)
  7. Review fixes critical/warning issues, commits fix
  8. Continue to next phase
```

## Per-Task 6-Step Methodology

Each task runs with this structure:

1. **Context Loading** — Read task_plan.md, findings.md, progress.md
2. **Research** — Launch parallel Explore subagents to scan codebase
3. **Implementation** — Follow plan with anti-pattern awareness
4. **Verification** — Run project's test/build suite
5. **Cross-Verification** — Optional MCP-based parallel audit
6. **Commit** — Stage specific files, commit, update progress ledger

## Failure-Aware Retry

| Failure Type     | Detection Pattern    | Retry Adaptation                    |
| ---------------- | -------------------- | ----------------------------------- |
| Context overflow | `Prompt is too long` | Strip findings.md, fewer subagents  |
| Rate limited     | `429`, `overloaded`  | Wait and retry normally             |
| Budget exceeded  | `budget.*exceeded`   | Reduce cross-verification, +$5      |
| API error        | `500`, `503`         | Retry normally (transient)          |
| Generic          | Any non-zero exit    | Check git diff, continue from there |

## Configuration Defaults

| Setting        | Default       | Notes                                 |
| -------------- | ------------- | ------------------------------------- |
| Model          | opus          | Use sonnet for simple tasks           |
| Effort         | max           | High quality for autonomous execution |
| Task timeout   | 2400s (40min) | Increase for very large tasks         |
| Review timeout | 2400s (40min) | Reviews run long due to subagents     |
| Max retries    | 2             | 3 total attempts (1 + 2 retries)      |
| Budget         | $6-18/task    | Scaled by complexity                  |

## Quick Start

Install the full skill with executor template and production learnings:

```bash
cp -r autoplex ~/.claude/skills/
```

Or from GitHub: https://github.com/ZenAlexa/autoplex

Then say: _"I have a task plan. Run it autonomously."_
