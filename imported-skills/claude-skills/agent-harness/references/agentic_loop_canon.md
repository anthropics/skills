# The Agentic Loop Canon

What the 2024–2026 practitioner literature agrees an agent loop is, and the design
decisions this skill inherits from it. Every rule in `SKILL.md` traces to one of
these sources.

## Sources

1. **Erik Schluntz & Barry Zhang (Anthropic), "Building Effective Agents", Dec 2024** —
   https://www.anthropic.com/research/building-effective-agents. The reference taxonomy:
   *workflows* (LLM steps orchestrated through predefined code paths) vs *agents* (the LLM
   directs its own process). Patterns: prompt chaining with programmatic gates, routing,
   parallelization, orchestrator-workers, evaluator-optimizer. Rule inherited: **compile the
   goal into a workflow — explicit ordered tasks with checks — and let the model be dynamic
   only inside a task**, because evaluator-optimizer loops only pay off "when clear evaluation
   criteria exist."
2. **Anthropic, "Building agents with the Claude Agent SDK", Sep 2025** —
   https://claude.com/blog/building-agents-with-the-claude-agent-sdk. Canonizes the loop as
   **gather context → take action → verify work → repeat**, with the filesystem as the context
   store and a verification-reliability ladder: rules-based checks > visual inspection >
   LLM-as-judge. Rule inherited: every task record in the plan carries a `verification` array;
   deterministic checks outrank judgment.
3. **Anthropic, "How we built our multi-agent research system", Jun 2025** —
   https://www.anthropic.com/engineering/multi-agent-research-system. Production
   orchestrator-workers: subagent specs need **objective, output format, tool guidance, and
   task boundaries** or workers duplicate and wander; effort must be scaled by rule (simple
   query = 1 agent, 3–10 calls). Rule inherited: `goal_compiler.py` emits per-task objective +
   suggested tools + done_when, and caps tasks with `--max-tasks`.
4. **Anthropic, "Effective harnesses for long-running agents", Nov 2025** —
   https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents. The
   flagship harness: an initializer expands the goal into a structured `feature-list.json`;
   a worker is woken repeatedly, each fresh-context session doing ONE item: read progress →
   implement → run tests → write progress → commit. **All state lives on disk/git; sessions
   are stateless shifts.** Rule inherited: the plan file + state file ARE the loop; never
   assume conversational carryover between iterations.
5. **Geoffrey Huntley, "Ralph Wiggum as a 'software engineer'", Jul 2025** —
   https://ghuntley.com/ralph/ (now an official Claude Code plugin). A `while true` loop
   feeding the same prompt to a fresh-context agent, with the filesystem + TODO file + git as
   memory. Load-bearing insight: **fresh context each iteration is the point** — quality
   degrades as the window fills, so restart against durable state instead of continuing.
   Community practice adds iteration caps and completion criteria. Rule inherited:
   `max_loop_iterations` is mandatory and enforced by the controller, not the agent.
6. **Walden Yan (Cognition), "Don't Build Multi-Agents", Jun 2025** —
   https://cognition.com/blog/dont-build-multi-agents. The counterweight to fan-out
   enthusiasm: parallel actors making conflicting decisions on partial context is the dominant
   multi-agent failure. Synthesis with source 3: **fan out readers and judges; serialize
   writers.** Rule inherited: the default loop order is `sequential`; parallel execution is an
   explicit opt-in and only for non-writing tasks.
7. **Anthropic, "Equipping agents for the real world with Agent Skills", Oct 2025** —
   https://www.anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills.
   Skills load by **progressive disclosure** (metadata → SKILL.md → referenced files on
   demand); ship deterministic scripts for anything reliably automatable. Rule inherited: the
   manifest carries one-paragraph skill descriptors only; the agent opens a skill's SKILL.md
   when — and only when — its task starts.

## The loop this skill implements

```
GOAL ──goal_compiler──▶ PLAN (tasks × verification × caps)
                            │
              ┌─────────────▼──────────────┐
              │  loop_controller next       │◀────────────┐
              │  → execute ONE task         │             │
              │  → record --phase execute   │             │
              │  → loop_controller verify   │  retry ≤ max_attempts,
              │    (controller runs checks) │  changed approach only
              └──────┬──────────────┬───────┘             │
                verified        failed ───────────────────┘
                     │              │ (attempts exhausted)
                     ▼              ▼
                  close         ESCALATE to a human
              (refuses while any task unverified)
```

This is the six-step Observe→Choose→Act→Verify→Record→Repeat-or-stop cycle from the
vendored `loop-library/SKILL.md` (Forward Future, MIT), with the terminal-state taxonomy it
defines — success · clean no-op · blocked · approval-required · exhausted · stagnated —
mapped onto controller states: `closed` (success/no-op), `escalated`
(approval-required/exhausted), and the global iteration cap (stagnated).

## What the canon says NOT to do

- **Don't run the loop inside one ever-growing context.** (Sources 4, 5.) Each `next`
  directive is designed to be executable by a fresh session reading only the state file.
- **Don't let two tasks write the same artifact in parallel.** (Source 6.)
- **Don't hand the model an open-ended goal without acceptance criteria.** (Sources 1, 3.)
  `goal_compiler.py` refuses vague goals (exit 3) with forcing questions instead.
- **Don't treat subagent enthusiasm as progress.** (Source 3: early agents "spawned 50
  subagents for simple queries.") Task count is capped; effort is budgeted up front.
