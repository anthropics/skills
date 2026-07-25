---
name: workflow-builder
description: Design and write deterministic multi-agent workflow scripts (.js files in .claude/workflows/) for Claude Code's Workflow tool. Use when a user wants to build, create, author, scaffold, or run a custom Claude Code workflow, orchestrate sub-agents (fan-out, pipeline, loop, judge-panel), or automate a repeatable multi-step task across fresh-context agents.
license: MIT
metadata:
  inspired_by: "https://github.com/ray-amjad/claude-code-workflow-creator (Ray Amjad)"
  targets: "Claude Code Workflow tool (CLAUDE_CODE_WORKFLOWS=1, /workflows)"
  version: 1.0.0
---

# Workflow Builder

Author runnable workflow scripts for Claude Code's Workflow tool: deterministic multi-agent orchestration files (`.js`) that fan work out to fresh-context sub-agents under plain JavaScript control flow. Only leaf `agent()` calls spend tokens, so the main session stays clean and the whole run is resumable.

## ALWAYS start every session with intake (non-negotiable)

Before proposing or writing any workflow, run the intake. Do not skip to code.

1. **Ask what kind of workflow they want.** Use this opening question set:
   - What repeatable, multi-step task do you want to automate?
   - What is the one unit of work a single sub-agent does once?
   - How many units — a known list, or discovered by looping?
   - Do later steps need *all* prior results at once, or can each item flow on its own?
   - Does any step need structured data back (a verdict, a list, scores)?
   - Roughly how many tokens / how deep should it go?

2. **If the user is vague, do NOT stall.** Run the recommendation engine to turn whatever you have into 1-2 concrete proposals, then present them *with the reasoning*:
   ```bash
   python scripts/workflow_intake.py --task "their description" \
     --units unknown --stages unknown --needs-all unknown --structured unknown
   ```
   The engine returns a recommended topology (fan-out / pipeline / loop / barrier / judge-panel), model picks, a budget guard, and a one-line rationale per choice. Present those as "Here's what I'd build and why" — never ask the user to re-answer questions they already half-answered.

3. **Confirm the shape with the user** (topology + phases + parallel-vs-pipeline) before writing the file. This is the only approval gate.

See [references/decision_and_intake_guide.md](references/decision_and_intake_guide.md) for the full question framework, the vague-input playbook, and worked recommendation examples.

## Decide if a workflow is even the right tool

| Scenario | Use |
|----------|-----|
| Single sub-agent, one task | plain Agent tool |
| Reusable procedure, Claude picks steps dynamically | a Skill |
| Many sub-agents in a fixed topology, deterministic + resumable | **Workflow** ✓ |

Workflows earn their cost when work is parallel or multi-stage, must be reproducible, long enough to fail halfway (so resume matters), or benefits from isolating each step in its own context window. For one-off tasks, just use Claude directly.

## Build → validate → run loop

1. **Scaffold** a starter from the confirmed topology:
   ```bash
   python scripts/scaffold_workflow.py --topology pipeline --name pr-triage \
     --description "Triage open PRs" > .claude/workflows/pr-triage.js
   ```
2. **Edit** the file: `meta` block first (pure literal, first statement), then the async body using the injected globals — `agent()`, `pipeline()`, `parallel()`, `phase()`, `log()`, `budget`, `args`, `workflow()`. Full surface in [references/api_reference.md](references/api_reference.md); copy-paste shapes in [references/orchestration_patterns.md](references/orchestration_patterns.md).
3. **Validate** before running — catches the parser-fatal mistakes:
   ```bash
   python scripts/validate_workflow.py .claude/workflows/pr-triage.js
   ```
4. **Run** it: enable the feature with `export CLAUDE_CODE_WORKFLOWS=1`, save the file under `.claude/workflows/`, then use `/workflows` to launch and watch it live. Press **P** to pause/resume, **X** to skip a sub-agent. Failed agents retry automatically.

## Hard rules (validator enforces these)

- `meta` is a **pure literal** and the **first statement** — no variables, spreads, template strings, or function calls inside it.
- **No non-determinism:** `Date.now()`, `Math.random()`, argless `new Date()` break resume — pass timestamps via `args`.
- **No filesystem / Node APIs** (`require`, `fs`, `process`, network) in the orchestrator — that work belongs *inside* `agent()` prompts.
- `parallel()` takes **thunks** (`() => agent(...)`), not bare promises. Default to `pipeline()` unless a stage needs the whole prior result set.
- **Guard every open-ended loop** with a counter or `budget.remaining()` check — unguarded loops hit the 1000-agent cap.
- Filter skipped/failed agents: `results.filter(Boolean)`.

## Tooling

- `scripts/workflow_intake.py` — intake recommendation engine (topology + model + budget + rationale from vague input).
- `scripts/validate_workflow.py` — stdlib linter for the rules above; PASS / WARN / FAIL with line numbers.
- `scripts/scaffold_workflow.py` — generate a starter `.js` for any topology.
- `assets/templates/` — fan-out, pipeline, loop-until-budget starters. `assets/examples/` — a complete runnable workflow.

All scripts run with `--sample` (no args) and `--help`.
