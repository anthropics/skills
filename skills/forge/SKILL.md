---
name: forge
description: "Use this skill whenever the user has a complex task that needs to be done right — not just executed once, but iteratively hammered into shape until it passes quality checks. This includes writing production code, drafting technical documents, designing system architectures, building configuration files, creating test suites, or any deliverable where 'good enough on first try' is unlikely. Trigger when the user says 'forge this', 'do this properly', 'iterate until done', 'use forge', or presents a task that clearly benefits from multiple revision passes. The skill works by dynamically generating two sub-skills: an executor (step-by-step action plan informed by best practices) and an evaluator (measurable pass/fail quality checklist), then running an execute-evaluate-fix loop until every criterion passes. Do NOT use for trivial one-line fixes, simple lookups, or real-time pair programming."
---

# Forge — Execute, Evaluate, Repeat Until Done

Break any complex task into an **executor** (action plan) and an **evaluator** (quality gate), then loop until every check passes.

## Quick Reference

| Phase | What happens |
|-------|-------------|
| Init | Create working directory and task ID |
| Executor | Analyze intent, research best practices, write action plan |
| Evaluator | Derive quality dimensions, write pass/fail checklist |
| Loop | Execute -> evaluate -> fix failures -> repeat |
| Report | Output structured completion summary |

---

## Phase 0: Initialize

1. Set `WORKDIR`: user-specified path, or current working directory.
2. Generate `TASK_ID` from task description (kebab-case, `a-z0-9` and `-` only, max 30 chars).
   - Example: `"Rewrite auth middleware"` -> `rewrite-auth-middleware`
3. **Conflict check**: if `{WORKDIR}/.tmp/{TASK_ID}/` exists, ask the user: **overwrite** / **append number** (`task-id-2`) / **cancel**.
4. Create:

```
{WORKDIR}/.tmp/{TASK_ID}/
  ├── executor/SKILL.md
  └── evaluator/SKILL.md
```

## Phase 1: Generate Executor

1. **Analyze user intent**: break down goals, constraints, expected outputs.
2. **Research best practices**: run 2-3 web queries if search is available. Otherwise generate from knowledge and mark `[offline]`.
3. **Write** `executor/SKILL.md` (target 100 lines):

```markdown
---
name: executor-{TASK_ID}
description: Auto-generated action plan for {task}.
---
# Action Plan: {Task Title}

## Goal
{One sentence}

## References
{Best practice sources, or [offline]}

## Steps
1. {Action} -> Output: {deliverable}
2. ...

## Constraints
- ...
```

## Phase 2: Generate Evaluator

1. **Derive quality dimensions** from the task goal (correctness, completeness, performance, style, etc.).
2. **Research evaluation criteria**: look for review checklists or quality gates in the domain. Mark `[offline]` if unavailable.
3. **Write** `evaluator/SKILL.md` (target 100 lines):

```markdown
---
name: evaluator-{TASK_ID}
description: Auto-generated quality gate for {task}.
---
# Quality Gate: {Task Title}

## Criteria
| Dimension | Weight | Pass When |
|-----------|--------|-----------|
| ... | ... | {Specific, measurable condition} |

## Process
1. Check each row above
2. Record PASS / FAIL + reason per item
3. All PASS -> done; any FAIL -> list required fixes

## Output Format
- Status: PASS / FAIL
- Details: [per-item results]
- Fixes needed: [if any]
```

## Phase 3: Execute-Evaluate Loop

**Max iterations**: 5 (default, user can override).

Each iteration:

1. **Execute**: read latest `executor/SKILL.md`, carry out each step, record what changed.
2. **Evaluate**: read latest `evaluator/SKILL.md`, check every criterion, output PASS / FAIL with per-item details.
3. **Decide**:
   - All PASS -> proceed to Phase 4.
   - Any FAIL -> analyze root cause, update executor and/or evaluator, summarize this iteration (what improved, what to tackle next), return to step 1.
4. **Max iterations reached with open FAILs** -> output best result so far + list of unresolved issues. Ask user: **continue** / **accept current** / **stop**.

**IMPORTANT**: Re-read both skill files at the start of every iteration. They may have been updated in the previous cycle.

## Phase 4: Completion Report

```markdown
## Forge Complete
### Summary
{What was accomplished}
### Final Evaluation
{Last evaluator output}
### Iterations
- Total: {N}
- Key improvements: {Per-round summary}
### Output Files
{File paths}
### Lessons Learned
{Reusable patterns or insights}
```

---

## Error Handling

| Scenario | Strategy |
|----------|----------|
| Web search unavailable | Fall back to offline, mark `[offline]` |
| Skill file missing | Regenerate from template, notify user |
| User interruption | Save progress, output partial summary |
| Step failure | Log error, try alternative, flag in evaluation |
| Max iterations reached | Output best result + open issues, ask user |

## Notes

- Multiple tasks coexist under the same `WORKDIR` (separate `TASK_ID` directories).
- Skill content evolves during iteration — line limits apply only to initial generation.
- `.tmp/` is scratch space. Clean up after completion.
- Executor steps can invoke other skills as needed.
