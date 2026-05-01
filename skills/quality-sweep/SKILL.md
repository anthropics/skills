---
name: quality-sweep
description: >-
  Multi-agent code quality sweep that runs five specialist passes — bug hunting,
  TODO resolution, style/layout consistency, dead code removal, and deduplication
  refactoring — each delegated to a focused sub-agent via the Task tool. Use this
  skill when the user asks for a "quality sweep", "code quality pass", wants to
  "find bugs", "remove dead code", "deduplicate code", "fix TODOs", check
  "layout consistency", or prepare code "before a pull request". Also triggers on
  requests like "clean up the codebase", "audit code quality", or "pre-merge
  review".
license: Complete terms in LICENSE.txt
---

# Quality Sweep

A multi-agent quality sweep that runs five specialist passes on a codebase. Each pass is delegated to a focused sub-agent via the `Task` tool, and each pass runs iteratively (typically 3–5 invocations) because a fresh context catches different issues each time.

You — the agent running this skill — act as the **Quality Lead**. You do not fix code yourself. You orchestrate, review, and decide.

## Specialist agents

Each agent is defined in its own file under `agents/`. Read the relevant file before dispatching a sub-agent so you can paraphrase its key instructions in the task prompt.

| # | Agent | File | Role |
|---|-------|------|------|
| 1 | Bug Hunter | [`agents/bug-hunter.md`](agents/bug-hunter.md) | Finds and fixes one bug per invocation, progressing from obvious crashes to subtle edge cases. |
| 2 | TODO Resolver | [`agents/todo-resolver.md`](agents/todo-resolver.md) | Resolves one `TODO`/`FIXME`/`XXX`/`HACK` comment by implementing, removing, or converting it to a tracked issue. |
| 3 | Style Auditor | [`agents/style-auditor.md`](agents/style-auditor.md) | Unifies one cluster of frontend layout/spacing/typography inconsistencies against the project's design system. |
| 4 | Dead Code Remover | [`agents/dead-code-remover.md`](agents/dead-code-remover.md) | Removes one piece of dead code — unused imports, unreachable branches, unreferenced exports — after verifying via static analysis. |
| 5 | Dedup Refactorer | [`agents/dedup-refactorer.md`](agents/dedup-refactorer.md) | Extracts one duplication cluster into a shared abstraction and updates all callers. |

## Orchestration pattern

1. **Read the agent file** for the current pass (e.g., `agents/bug-hunter.md`).
2. **Dispatch a sub-agent** using the `Task` tool. Include in the task prompt:
   - The agent's role and process (paraphrase key instructions from the agent file).
   - The repo path and scope constraint (see "Scoping the sweep" below).
   - The iteration number and a summary of prior-iteration findings to avoid duplicating work.
   - An instruction to find and fix **one** issue, commit-ready, then stop.
3. **Review the result** when the sub-agent returns. Check the file list and summary. Accept, request a revision, or move on.
4. **Iterate** by dispatching a fresh sub-agent for the same role. Do not carry the previous sub-agent's context — a fresh context is the whole point, since it catches different things each time.
5. **Stop** when the stopping conditions are met (see below), then move to the next pass.

## Default sweep order

```
1. Bug Hunting
2. TODO Resolution
3. Style Consistency  (skip if backend-only)
4. Dead Code Removal
5. Deduplication
```

### Detecting project type

Before starting, determine whether the codebase is frontend-only, backend-only, or mixed:

- **Frontend signals**: presence of `src/components/`, JSX/TSX files, CSS/SCSS/Tailwind config, `package.json` with React/Vue/Angular/Svelte dependencies, a `public/` or `static/` directory.
- **Backend signals**: server entry points (`server.ts`, `app.py`, `main.go`), API route definitions, database migrations, Dockerfiles for services, no UI framework dependencies.
- **Mixed**: both signals present.

Skip the Style Auditor pass for backend-only projects. For frontend-only projects, all five passes apply. For mixed projects, scope the Style Auditor to frontend directories only.

## Partial sweeps

When the user asks for a single pass rather than the full sweep, run only the requested agent:

- "just hunt for bugs" → run Bug Hunter iterations only.
- "just dedupe" → run Dedup Refactorer iterations only.
- "clean up dead code" → run Dead Code Remover iterations only.
- "fix the TODOs" → run TODO Resolver iterations only.
- "check style consistency" → run Style Auditor iterations only.

All the same orchestration rules apply — iterate with fresh contexts until stopping conditions are met.

## Scoping the sweep

When the user provides a scope hint ("focus on the auth module", "stick to data validation", "only look at `src/api/`"):

1. Pass the scope constraint to every sub-agent in the task prompt.
2. The sub-agent restricts its search to the specified files/directories.
3. If a fix requires touching a file outside the scope (e.g., updating an import in a caller), that's acceptable — but the *finding* must originate within scope.

If no scope hint is given, sweep the entire project.

## Stopping conditions

For each iterative pass, stop running more iterations when any of these hold:

- **No findings**: the sub-agent reports "no findings" — there is nothing left to fix in this category.
- **Diminishing returns**: two consecutive iterations produce only trivial or borderline findings.
- **Iteration cap**: 5 iterations have been completed for this pass (default cap; the user can override).
- **User-set limit**: the user specifies a maximum number of iterations or a time budget.

When in doubt, err on the side of stopping early. More passes at diminishing quality create noise.

## Commit hygiene

Each accepted fix gets its own commit with a Conventional Commits message:

- Bug fix → `fix: <description>`
- TODO resolution → `chore: resolve TODO — <description>` or `feat:` / `fix:` if the resolution adds a feature or fixes a bug
- Style consistency → `style: <description>`
- Dead code removal → `chore: remove dead code — <description>`
- Deduplication → `refactor: extract <abstraction> from <callers>`

The skill itself does **not** push or open a PR. Leave that to the caller.

## Parallel execution of independent passes

When two passes target non-overlapping file scopes, you can run them in parallel. For example:

- Bug Hunter on `src/auth/` + Style Auditor on `src/components/` → safe to parallelize.
- Dead Code Remover on `src/` + Dedup Refactorer on `src/` → **not** safe (both may touch the same files).

Use your judgment. When in doubt, run sequentially.

## Anti-patterns

- **Don't run all five sub-agents in parallel on the same files.** This causes merge conflicts and duplicated work.
- **Don't let a sub-agent spiral into a giant refactor.** Each invocation handles one finding. If a sub-agent tries to fix multiple things at once, reject the result and re-dispatch with a clearer scope.
- **Don't skip the lead's review step.** Every sub-agent result should be reviewed before committing. Blindly accepting changes defeats the purpose of having a lead.
- **Don't carry context between iterations.** The iterative restart pattern works because a fresh context notices different things. Passing the full prior transcript to the next iteration undermines this.
- **Don't commit multiple findings in one commit.** One finding, one commit.
