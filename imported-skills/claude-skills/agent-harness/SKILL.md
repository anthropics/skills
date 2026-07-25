---
name: agent-harness
description: "Turn any domain folder of skills into a bounded agentic loop: compile a goal into a verifiable task plan, execute tasks with the domain's own tools, verify every task with machine-run checks, retry with caps, escalate to a human when budgets exhaust, and refuse to close until everything is verified or explicitly waived. Use when you want an agent or subagent to pick up a goal and drive it to a verified close across one of this repo's 18 domains ('run this goal through the engineering harness', 'set up an agentic loop for marketing work', 'make the finance domain self-verifying'). NOT for authoring Claude Code Workflow-tool .js scripts (workflow-builder), N-agent tournaments on one task (agenthub), single-file metric optimization (autoresearch-agent), or discovering published loop recipes (loop-library)."
---

# Agent Harness

You are a harness operator, not a hero. The loop — not your optimism — decides when work
is done. Your job: compile the goal into tasks with checks, execute one task at a time,
let the controller adjudicate verification, and stop when the state machine says stop.

## The contract

```
GOAL → goal_compiler → PLAN → loop_controller: [execute → verify]* → CLOSE
                                     ↑______retry (≤ max_attempts, changed approach)
                                     └── ESCALATE on exhausted budgets — never fake success
```

Three layers, all JSON: a committed per-domain **manifest** (what skills/tools/checks
exist), a per-goal **plan** (which tasks, which verifications, what "done" means), and a
per-run **state file** (the single source of truth; a fresh session resumes from it alone).

## Quick start

```bash
# 0. Pick the domain manifest (18 committed under assets/harnesses/, e.g. engineering-team.json)
ls assets/harnesses/

# 1. Compile the goal (refuses vague goals with exit 3 + forcing questions)
python3 scripts/goal_compiler.py \
  --goal "audit the payments service and design an SLO with an error budget" \
  --manifest assets/harnesses/engineering.json --out plan.json

# 2. Initialize the loop state
python3 scripts/loop_controller.py init --plan plan.json --state .agent-harness/state.json

# 3. Drive the loop — repeat until directive is "close" or "escalate"
python3 scripts/loop_controller.py next --state .agent-harness/state.json
#    → {"action": "execute", "task": "T1", ...}: open the task's skill (SKILL.md at
#      skill_path), do the work with its tools, then:
python3 scripts/loop_controller.py record --state .agent-harness/state.json \
  --task T1 --phase execute --exit-code 0
#    → the controller runs the task's checks ITSELF (subprocess, timeout, evidence log):
python3 scripts/loop_controller.py verify --state .agent-harness/state.json --task T1 --cwd <repo-root>

# 4. Close — refused (exit 4) while any task is unverified and unwaived
python3 scripts/loop_controller.py close --state .agent-harness/state.json
```

Regenerate a manifest after skills change (diff-stable, CI-checkable):

```bash
python3 scripts/harness_manifest_builder.py --domain engineering-team \
  --repo-root <repo-root> --out-dir assets/harnesses --no-timestamp
```

## Hard rules

1. **Never adjudicate your own verification.** `verify` runs the checks via subprocess;
   a passing `record --phase verify` without `--evidence` is rejected (exit 6). You do not
   get to declare a task verified.
2. **Never modify a gate you are judged by.** Check commands come from the manifest/plan.
   Editing a check to make it pass is the reward-hacking failure mode
   (see [references/verification_discipline.md](references/verification_discipline.md)) — same
   invariant as autoresearch-agent's locked evaluator.
3. **One task at a time, writes serialized.** Parallelize reading and judging, never two
   tasks writing the same artifact ([references/agentic_loop_canon.md](references/agentic_loop_canon.md)).
4. **Retry means a changed approach.** Same command + same input = same failure. The retry
   directive says so; honor it.
5. **Budgets are terminal states, not suggestions.** `max_attempts_per_task` → escalated
   (exit 2); `max_loop_iterations` → escalate (exit 5). Exhausted budgets are never
   reported as success — a human waives (`close --waive T3 --reason "..."`), you don't.
6. **Fresh context beats long context.** Every `next` directive is executable by a new
   session reading only the plan + state files. Long-running goals: run each iteration as
   its own session against the durable state.
7. **State lives in `.agent-harness/`** — never in `.agenthub/`, `.autoresearch/`, or
   `docs/TC/` (those belong to sibling skills).
8. **Plan and state files are a trust boundary.** `verify` shell-executes each task's
   check command; only run the harness on plan/state files you or `goal_compiler.py`
   produced, never on files from untrusted input (see
   [references/verification_discipline.md](references/verification_discipline.md)).

## Forcing questions (ask before compiling; one per turn, with a recommended answer)

| # | Question | Recommended answer | Why (canon) |
|---|---|---|---|
| 1 | What single observable outcome means DONE? | A named artifact + a command that exits 0 against it | Verifier's law: invest in verifiability first |
| 2 | Which domain harness applies? | The domain whose skills name the deliverable; if two, run two sequential loops | Orchestrator-workers: scoped objectives beat mega-goals |
| 3 | What must NOT change? | List no-touch paths; put them in the goal text so the compiler's plan inherits them | Boundaries are part of a subagent spec |
| 4 | Who reviews escalations, and how fast? | A named human; escalations block the loop by design | Approval-required is a terminal state, not a nuisance |
| 5 | What is the iteration budget? | Default 12 loop iterations / 3 attempts per task; raise only with a reason | Caps are runtime errors, not advice (OpenAI SDK `max_turns`) |

## Exit codes (branch on these mechanically)

| Code | Tool | Meaning |
|---|---|---|
| 0 | all | OK / directive emitted |
| 2 | loop_controller | Escalation required — a human must review the evidence log |
| 3 | goal_compiler | Goal too vague — answer the forcing questions, recompile |
| 4 | goal_compiler / loop_controller | No skill matched / close refused (unverified tasks) |
| 5 | loop_controller | Global iteration cap reached |
| 6 | loop_controller | Invalid transition (recording on verified task, evidence missing, unknown task) |

## Verifiable success

- `python3 scripts/harness_manifest_builder.py --sample`, `scripts/goal_compiler.py --sample`,
  and `scripts/loop_controller.py --sample` all exit 0.
- A vague goal (`--goal "make it better"`) exits 3 and prints forcing questions.
- `loop_controller.py close` on a state with an unverified task exits 4.
- The demo loop in `loop_controller.py --sample` shows a verify failure consuming an attempt
  and the loop still closing only after a passing verify with evidence.

## Related skills

- **workflow-builder**: authoring deterministic `.js` scripts for Claude Code's Workflow
  tool. NOT for goal-to-close loop state (this skill).
- **agenthub**: N parallel agents competing on ONE task in git worktrees. Use it *inside* a
  harness task that wants competing attempts.
- **autoresearch-agent**: metric optimization of a single file against a locked evaluator.
  Use it when a task's done_when is "metric improves".
- **tc-tracker**: per-code-change lifecycle records. Use for change bookkeeping; the harness
  state file is per-goal, not per-change.
- **loop-library**: discover/audit published loop recipes conversationally. This skill is the
  executable enforcement of that vocabulary.
- **ship-gate / self-eval / spec-driven-workflow**: plug in as close-time checks inside a
  task's `verification[]`.

See [references/domain_harness_design.md](references/domain_harness_design.md) for the
three-layer architecture, the reuse map, and how to raise a domain's harness quality.
