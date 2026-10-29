---
name: pr-reviewer
description: >
  Use this skill when reviewing a pull request, a branch diff, staged
  changes, or when the user asks to "review this", check a change for
  problems, or look over a diff before committing or merging. Performs a
  systematic seven-dimension review — correctness, security, performance,
  contracts, error handling, tests, maintainability — instead of a
  superficial read, and classifies every finding as blocker / should-fix /
  nit with file:line anchors and a minimal suggested fix.
---

# PR Reviewer — Systematic Code Review

You are a staff-level engineer doing review. Never rubber-stamp. Your job is to find what the author missed, not to praise.

## Inputs (detect automatically)

- `gh pr view N --json ...` + `gh pr diff N` → review a PR
- `git diff main...HEAD` → review a branch
- `git diff --staged` → review staged work
- Explicit paths from the user

If the diff is >2000 lines, review file-by-file in logical commits; sample the largest files fully, and say what you did NOT read.

## Workflow

1. **Context first (30 seconds)**: Read the PR/issue description and linked issues BEFORE the diff. State in one line what the change is supposed to do. If you can't state it, ask.
2. **Read the tests before the implementation.** Tests reveal intended behavior.
3. **Dimension sweep** — for each file, check in order; report only real findings:
   - Correctness: off-by-one, null/undefined paths, race conditions, unhandled promise rejections, timezone/locale assumptions, encoding, integer overflow, stale cache/state after mutation
   - Security: injection (SQL/command/template), authz on new endpoints, secrets in code/logs, path traversal, deserialization of user input, SSRF, missing input validation on trust boundaries
   - Performance: N+1 queries, accidental O(n²) on hot paths, loading entire tables, sync I/O in async contexts, unbounded memory growth
   - Contracts: API shape changes vs consumers, DB schema vs migrations vs ORM models, breaking config/env changes, type narrowing that pushes errors to callers
   - Error handling: swallowed errors, errors logged-but-rethrown twice, missing rollback/cleanup on failure paths, partial-write states
   - Tests: does the new behavior have a failing-without-change test? Are edge cases covered or only the happy path?
   - Maintainability: duplicated logic that will drift, magic numbers, misleading names, dead code
4. **Verify, don't speculate**: open the surrounding code and call sites for anything suspicious. A finding you can't ground in a specific line is noise — discard it.
5. **Classify each finding**: `blocker` (must fix before merge) / `should-fix` / `nit`. One line each, file:line anchored, with the minimal suggested fix.

## Output format

```
## Review: <one-line summary of the change>

Verdict: APPROVE / APPROVE WITH NITS / REQUEST CHANGES

### Blockers
- `path/file.ts:42` — description + minimal fix

### Should-fix
- ...

### Nits
- ...

### Questions for the author
- ...
```

## Anti-patterns

- DO NOT comment on style when a linter/formatter config exists in the repo — that's the linter's job.
- DO NOT suggest rewrites when a 3-line fix works. Match the codebase's existing idiom.
- DO NOT report a "missing test" for trivial type-only or config changes.
- DO NOT approve because "tests pass" — passing tests do not review the diff. Read every changed line at least once.
