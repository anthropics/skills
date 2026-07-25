# Claude Code Prompt Design Patterns

Patterns for designing the prompts that drive Claude Code work — initial prompts that kick off a session, session prompts that govern multi-turn work, autonomous prompts that run with less supervision, and subagent delegation prompts that hand work to specialist agents.

This reference is for DESIGN mode when the deliverable includes a CC prompt of any kind, and for EVOLVE mode when the friction is "the prompt isn't producing what we want." For environment design (CLAUDE.md, hooks, settings), see `cc-environment-design-patterns.md`. For Skills authoring, see `cc-skills-and-hooks-composition.md`.

---

## Table of contents

1. The four prompt classes — when each applies
2. Universal prompt principles (apply to all classes)
3. The Explore → Plan → Implement → Verify workflow
4. Initial prompt patterns
5. Session prompt patterns
6. Autonomous prompt patterns
7. Subagent delegation prompt patterns
8. Files-as-context: the spec-file pattern
9. The verification iron law
10. Output discipline for CC prompts

---

## 1. The four prompt classes — when each applies

| Class | Purpose | Typical length | Where it lives |
|---|---|---|---|
| **Initial prompt** | Kicks off a fresh session against a defined work scope | 50-300 words | Pasted into a fresh `claude` invocation; or stored at `prompts/{task-name}.md` and read in |
| **Session prompt** | Continues or refines work within an active session; includes context the session needs | 20-200 words | Typed in the active session |
| **Autonomous prompt** | Drives long-running, less-supervised work (overnight runs, multi-stage builds) | 100-500 words | Stored at `prompts/{run-name}.md`; invoked via headless mode or from an orchestrator |
| **Subagent delegation prompt** | Routes a specific subtask to a specialist agent | 30-150 words | Constructed by the parent session when it spawns a subagent |

The deployment plan in DESIGN mode should specify which prompt classes are needed and where they live. Most projects need at least an initial prompt template; many also need session and subagent prompt templates.

---

## 2. Universal prompt principles (apply to all classes)

These five principles appear across every authoritative source on CC prompt design (Anthropic primary docs, rosmur/claudecode-best-practices, obra/superpowers, alexop.dev, Shrivu Shankar). They apply to every prompt class.

**P1. Specific and actionable beats vague and aspirational.** "Run `npm test` before declaring done" beats "test your changes." "Use 2-space indentation" beats "format code properly." Vague prompts consume context tokens without changing behavior. **[Anthropic docs + practitioner consensus]**

**P2. Imperative form.** Direct instructions, not suggestions. "Edit X. Run Y. Verify Z." beats "You might want to consider editing X." The prompt is a directive, not a discussion. **[Anthropic docs]**

**P3. Critical instructions at the top.** Put the most important rules and behaviors first. Use `## Important` or `## Critical` headers. CC processes prompts top-to-bottom; buried critical instructions get less weight. **[Anthropic docs + Shrivu Shankar]**

**P4. Files-as-context, not transcript-dumps.** Reference files the agent should read (`@PLAN.md`, `@spec/api.md`) rather than pasting their content into the prompt. CC's tool calls fetch file contents on demand; pasting them duplicates context. **[12 convergence patterns; named anti-pattern across all 3 external research reports]**

**P5. Verification gates baked into the prompt.** Every prompt that produces output specifies how the output will be verified. "Edit X. Run `pytest tests/` and verify all tests pass before declaring done." Without verification gates, CC drifts toward implementation-first behavior and the "trust-then-verify gap" emerges. **[obra/superpowers verification-before-completion iron law]**

---

## 3. The Explore → Plan → Implement → Verify workflow

The canonical CC workflow named identically across Anthropic primary docs and every major practitioner source. Four phases:

**Phase 1 — Explore.** The agent surveys the codebase or context relevant to the task. In CC, this typically uses the Explore subagent (Haiku, read-only, cheap). The output is a context-grounded understanding, not a plan.

**Phase 2 — Plan.** The agent produces a written plan — what files will change, what's the approach, what's the verification strategy. CC supports a "plan mode" (Shift+Tab) that disables edit tools while planning. In plan mode, the user can edit the plan (Ctrl+G) before approving. The plan is an artifact (PLAN.md, SPEC.md), not a paragraph in chat.

**Phase 3 — Implement.** The agent executes the plan. The implementation should match the plan; deviation should surface as a plan revision, not a silent change.

**Phase 4 — Verify.** The agent runs the verification gates specified in the plan. Tests, lints, smoke checks, manual review hooks. The agent does not declare "done" until verification passes.

**The anti-pattern this prevents:** "vibe coding" — agent reads a vague request, jumps into edits, produces something that compiles but solves the wrong problem or breaks adjacent functionality. Plan-before-code is the single highest-leverage discipline in CC work. **[Anthropic primary docs + obra/superpowers + rosmur + coleam00 + shinpr — full convergence]**

**When to skip the plan:** Anthropic's own framing — "if you could describe the diff in one sentence, skip the plan." Trivial typo fixes, single-line config changes, or one-file refactors that have a clear shape don't warrant planning overhead. **[Anthropic docs — explicitly named exception]**

**Initial prompt template (workflow-aware):**

```markdown
Task: <one-sentence task description>

Workflow:
1. Explore the relevant code surface. Read @docs/architecture.md and any files in `src/<area>/` that might be affected.
2. Produce a plan in `PLAN.md` covering: files to change, approach, verification strategy, rollback plan.
3. Wait for plan approval before implementing.
4. Implement per the approved plan.
5. Run `<verification commands>` and confirm pass before declaring done.

Authority bounds: <reference to CLAUDE.md authority matrix or specific rules>

Halt and escalate if: <reference to halt-and-escalate triggers>
```

---

## 4. Initial prompt patterns

The initial prompt sets the work scope, references the relevant context files, and specifies the workflow. It does NOT re-state CLAUDE.md rules — those are loaded by CC automatically. The initial prompt's job is to scope the specific task within the standing rules.

**Pattern: Scope-and-workflow.** The most common initial prompt shape.

```markdown
Task: <task in one sentence>

Read first: @PLAN.md, @docs/<relevant>.md, @CHANGELOG.md (last 5 entries).

Approach: <Explore → Plan → Implement → Verify, or "skip plan" if trivial>

Verification: <specific commands the agent must run before declaring done>

Out-of-scope for this task: <anything the agent might reasonably do but shouldn't this time>
```

**Pattern: Scoped-iteration.** For a known iteration on a previously-shipped artifact.

```markdown
Task: <iteration on artifact X>

Reference state:
- Current artifact: @<path>
- Spec: @<path-to-spec>
- Last change: see @CHANGELOG.md entry "<id>"

Goal: <specific outcome of this iteration>

Constraints:
- <constraint 1>
- <constraint 2>

Verify: <specific verification commands>
```

**Pattern: Bug-fix.** Tightly scoped fix with a defined regression test.

```markdown
Task: Fix <bug>.

Reproduce first: run `<command>`. Expected behavior: <X>. Actual behavior: <Y>.

Workflow:
1. Reproduce the bug.
2. Add a failing test that captures the bug.
3. Implement the fix.
4. Confirm the test passes and the full suite still passes.
5. Add a CHANGELOG entry per the project's change_log discipline.

Authority: bug fix only. Do not refactor adjacent code. Do not add features.
```

**Anti-patterns to avoid in initial prompts:**
- Pasting CLAUDE.md content into the prompt (CC reads CLAUDE.md automatically; duplication wastes tokens)
- Pasting prior chat transcripts ("transcript dump")
- Listing every conceivable thing the agent might do (creates "kitchen sink" sessions)
- Vague success criteria ("make it better")
- No verification gate (the agent will declare done without checking)

---

## 5. Session prompt patterns

Session prompts continue or refine work within an active CC session. They're shorter than initial prompts because the session already has loaded context.

**Pattern: Iteration.** "The first cut isn't quite right; here's the refinement."

```markdown
The function in @<path> handles the happy path but fails on <case>. Add handling for <case> following the same pattern as <reference function>. Run the tests after.
```

**Pattern: Course-correction.** The agent went off-track; redirect.

```markdown
Stop. The change you just made breaks the contract specified in @<spec>. Revert and try again. The rule is: <specific rule>.
```

**Pattern: Scope-narrowing.** The agent is doing too much; narrow.

```markdown
Focus only on <specific subset>. Do not touch <other area> in this session. We'll handle that separately.
```

**Pattern: Verification-on-demand.** Make the agent prove the current state.

```markdown
Run `<verification command>` and show me the output. Don't make any changes until I respond.
```

**Anti-patterns to avoid in session prompts:**
- Re-explaining context that's already in the session (waste)
- Asking open-ended questions when a directive is needed ("what do you think we should do?" — usually the user knows)
- Letting the session sprawl across unrelated tasks (use `/clear` to start a clean session for unrelated work)

---

## 6. Autonomous prompt patterns

Autonomous prompts drive long-running, less-supervised CC work. They require more explicit framing than interactive prompts because the agent can't ask clarifying questions in real-time.

**Required elements for any autonomous prompt:**

1. **Mission statement** — what success looks like, in one paragraph
2. **Scope authorization** — what's in-scope, in-scope-with-notification, out-of-scope (mirror the CLAUDE.md scope rules)
3. **Halt-and-escalate triggers** — explicit conditions under which the agent must stop and surface
4. **Verification gates** — specific commands that must pass before any "done" declaration
5. **Progress reporting cadence** — how often the agent should write to a status file (every N changes, every M minutes)
6. **Error handling protocol** — what to do on test failure, build failure, ambiguous input
7. **Context bounds** — what files to read, what to ignore, what to write to

**Pattern: Autonomous-build template.**

```markdown
# Autonomous run: <run name>

## Mission
<one paragraph: what success looks like>

## Scope
- In-scope: <list>
- In-scope with notification: <list>; log to STATUS.md
- Out-of-scope (HALT and escalate): <list>

## Workflow per work item
1. Read the next item from @WORK_QUEUE.md
2. Apply the standard Explore → Plan → Implement → Verify cycle
3. Update CHANGELOG.md with the entry per the change_log discipline
4. Run the full verification suite: `<commands>`
5. If verification passes: mark item complete in @STATUS.md, move to next item
6. If verification fails: HALT, write diagnosis to @HALT.md, exit

## Halt-and-escalate triggers (any of these → HALT)
- <trigger 1>
- <trigger 2>
- <trigger 3>

## Progress reporting
- After every work item: append to @STATUS.md
- Every 30 minutes (heartbeat): touch @HEARTBEAT.md

## Error handling
- Test failure → HALT, write diagnosis
- Ambiguous input from a work item → HALT, do not guess
- Tool unavailable → HALT, write diagnosis

## Context bounds
- READ: @<paths>
- WRITE: @<paths>
- IGNORE: @<paths>
```

**The pump primer pattern.** Autonomous runs typically benefit from a "pump primer" — the first work item is done manually (or in an interactive session) to validate the workflow, then the autonomous run picks up from item 2. This catches misconfiguration before the agent runs unsupervised. **[generalizable]**

**See also:** The pre-execution readiness check for autonomous work is the `rootnode-handoff-trigger-check` Skill if available — recommended before launching any autonomous run that will execute more than ~5 work items.

---

## 7. Subagent delegation prompt patterns

Subagents are spawned with their own context window. The delegation prompt is the only context the subagent has — there is no "shared session" to draw from. Design the prompt accordingly.

**Required elements for any subagent prompt:**

1. **Specific task** — one verifiable outcome, not "explore X" without a defined output
2. **Return format** — what the parent session expects back (summary, finding list with priority, diff with rationale, JSON object with named fields)
3. **Tool restrictions** — what the subagent is allowed to use; restrict to read-only for review roles
4. **Context bounds** — what files are in-scope to read; everything outside is out-of-scope
5. **Anti-pollution rule** — "do not echo file contents back; summarize with file path + line range references"

**Pattern: Read-only investigator.**

```markdown
Investigate <specific question>.

Read: @<path1>, @<path2>, anything in `src/<area>/` matching `<pattern>`.

Tools: read-only. Do not edit any files.

Return:
- A 3-5 sentence summary of findings.
- A list of file:line references that support the findings.
- One sentence on confidence ("High — direct evidence in <file>" or "Low — inferred from <indirect evidence>").

Do not echo file contents back. Reference by path + line range.
```

**Pattern: Spec-driven implementer.**

```markdown
Implement <specific change> per the spec at @<spec-path>.

Workflow: read the spec, implement, run `<verification>`, return the diff.

Return:
- The diff (paths and changes).
- Verification output (pass/fail per gate).
- One sentence: "complete" or "incomplete because <reason>".

Halt and return early if: the spec is ambiguous; verification fails; the change requires touching files not in scope.

Scope: only files in `src/<specific-area>/`.
```

**Pattern: Cross-verifier (the S/B/C/X X-role from production CC deployment 2026-05-04).**

```markdown
Cross-verify the audits in @<audit-path-1>, @<audit-path-2>, @<audit-path-3>.

For each disagreement between the three audits:
1. Identify the disagreement (which agent says what).
2. Investigate the underlying source to determine which is correct.
3. Return a single reconciled verdict per disagreement.

Return:
- A summary table: <issue> | <agent-A verdict> | <agent-B verdict> | <agent-C verdict> | <reconciled verdict> | <evidence>
- Overall ship verdict: PASS / PASS_WITH_NOTES / FAIL.

Read-only access. Do not modify any audit files.
```

**Anti-patterns to avoid in subagent prompts:**
- Open-ended exploration ("look around and tell me what you find" — produces unbounded output)
- No return format ("investigate X" — parent session has to parse arbitrary prose)
- Tool overprovisioning (giving an investigator full edit tools — invites scope creep)
- "Brainstorm creatively" / "consider all angles" — produces unfocused output that doesn't compose with parent session work
- Cross-subagent coordination ("ask the other agent if..." — subagents don't share context; use agent teams instead)

---

## 8. Files-as-context: the spec-file pattern

Project decisions belong in version-controlled files, not in chat history. The spec file is the canonical source of truth for what the agent should do; the prompt references the spec, not vice versa.

**The spec-file shapes:**

| File | Purpose | When to use |
|---|---|---|
| `PLAN.md` | A plan for a specific change or feature, produced in plan mode | After Explore phase; before Implement phase |
| `SPEC.md` | A long-lived specification for an artifact (an API, a data model, a feature) | When the artifact has multiple iterations and the spec is the canonical reference |
| `INITIAL.md` | The kickoff context for a new feature (mission, scope, constraints) | At project start; for major new features |
| `PRP.md` (Product Requirements Prompt) | A structured prompt template for executing a feature, per coleam00/context-engineering-intro | When the team uses the PRP pattern for feature delivery |
| `HANDOFF.md` | Continuation context between sessions when work spans multiple sessions | At session close; read at next session open |
| `AGENTS.md` | Agent role specs for the project's custom subagents | When the project has 2+ custom subagents |
| `CHANGELOG.md` | Per-change log entries per the change_log discipline | After every change |

**The pattern:** the prompt is a few sentences; the spec file is the substantial content. This keeps prompts short, makes specs reviewable, and keeps the agent's behavior auditable (the agent can read the spec; the human can read the spec; the diff between intended and actual behavior is visible).

**Reference syntax in CC:** use `@<path>` to reference a file. CC reads the file when it processes the prompt. `@PLAN.md` is shorter and more reliable than pasting PLAN.md content into the prompt.

---

## 9. The verification iron law

From obra/superpowers' verification-before-completion Skill, named identically across multiple practitioner sources: **never declare work complete without evidence that verification passed.** No "should work," no "probably fine," no "looks good." Evidence: test output, diff, lint clean, smoke check passing.

**Apply in every prompt** by:
1. Specifying the verification commands explicitly.
2. Banning speculative completion language in the prompt itself ("Do not declare done with phrases like 'should work' or 'probably fine'. Show the verification output.").
3. Where the project warrants enforcement (not just preference), back the iron law with a Stop hook that blocks completion without test evidence. See `cc-skills-and-hooks-composition.md` §"The verification iron law as hook."

**Working pattern from obra/superpowers:**

```markdown
Before declaring done:
1. Run `<test command>`. Show the output.
2. Run `<lint command>`. Show the output.
3. If both pass: declare done with evidence. Format: "Verified: tests N passed in Xs; lint clean. Done."
4. If either fails: do not declare done. Diagnose and re-attempt, or HALT and surface the failure.

Banned phrases at completion: "should work," "probably fine," "looks good," "I believe this is correct."
```

This pattern alone catches the most common CC failure mode (silent partial completion) and is worth specifying in every prompt where verification is possible. **[obra/superpowers iron law + Anthropic's "trust-then-verify gap" framing]**

---

## 10. Output discipline for CC prompts

CC prompts authored in DESIGN mode carry empirically-tested output standards that don't fully surface in environment-design references. The four below emerged from production CC prompt execution (Phase 31d merge, Phase 32a/b v3.0 builds, 2026-05-06 to 2026-05-08) — each gap produced a named friction during execution. Apply them when the deliverable is an initial prompt, session prompt, or autonomous prompt that an agent will run.

**Shell environment in CC prompts.** When producing CC prompts that include shell command blocks, default to bash. The CC harness shell is bash on Windows (Git Bash) and sh/bash on Linux/macOS, even when the operator's interactive environment is PowerShell. Prompts authored against the operator's local shell land in CC and trigger live translation by the agent (`Get-Content` → `cat`, `Test-Path` → `[ -f <file> ]`, `Measure-Object -Line` → `wc -l`, backtick line-continuation → backslash). Translation usually works but relies on agent judgment, creates inconsistent execution logs, and can fail silently for less-obvious divergences. Pattern: bash as the primary command block, with PowerShell variants labeled and adjacent for the divergent set. Universal commands — all `git` and `gh` invocations, `pwd`, `ls` — work in both shells and need no variants. `[generalizable: Phase 31d merge prompt execution 2026-05-06]`

**Pre-flight Skill enumeration in CC prompts.** When producing a multi-step CC prompt — any session prompt with phases, halts, or non-trivial scope — include a pre-flight stage that enumerates available Skills before any other file reads. Skill availability is determined at session-launch time, not at design-time, and the agent's methodology grounding depends on what's actually loaded. Prompts that proceed straight into file reads risk two failure modes: agents make decisions assuming Skills they don't have (requiring rework when discovery happens mid-execution), or agents skip Skill activation entirely and miss methodology that should have applied. The pre-flight stage takes one paragraph — enumerate available Skills, name the relevant ones the prompt expects to compose with, and explicitly note any expected Skill that's missing. See CC_ENVIRONMENT_GUIDE — pre-flight checklist (R5) for the broader pre-flight discipline this extends to runtime tooling discovery. `[generalizable: Phase 31d/32 execution learnings 2026-05-07/08]`

**Continuation-phrase ambiguity gate in multi-halt CC prompts.** When producing a CC prompt with operator halts and continuation phrases, include explicit halt-on-ambiguity discipline at each resume point. Continuation phrases that look unambiguous in design can be ambiguous in execution: an operator's reply may match the literal phrase, admit a clear semantic equivalent, or admit two reasonable interpretations. A prompt that doesn't direct the agent to halt on ambiguity produces silent inference — the agent picks one interpretation and proceeds, and is wrong some non-trivial fraction of the time. Pattern at every resume point: "If the operator's continuation message is ambiguous between two or more reasonable interpretations, halt and ask one targeted clarifying question. Do not infer." This is a specific application of the broader halt-and-escalate discipline (see root_AGENT_ENVIRONMENT_ARCHITECTURE — halt-and-escalate as a first-class discipline) to the resume case. `[generalizable: Phase 31d merge prompt execution 2026-05-06]`

**Forward-state-aware artifact authoring in CC prompts.** When a CC prompt instructs the agent to author downstream artifacts — PR descriptions, commit messages, audit summaries, halt reports — direct the agent to be explicit about whether forward references describe state at authoring or expected state post-commit/post-merge/post-release. Artifacts read mid-flow should not assume completed state that hasn't yet happened. Pattern: prefix forward references with explicit temporal markers ("post-merge:", "this PR will:", "after the v3.0 release will…") rather than declarative present tense ("is on main", "ships in v3.0"). The discipline is most load-bearing in PR bodies (read between PR open and PR merge, when the described state hasn't yet landed) and in audit reports authored mid-build (where the build is in progress at authoring). `[generalizable: Phase 32a/b artifact authoring 2026-05-07/08]`

---

## End of CC prompt design patterns reference
