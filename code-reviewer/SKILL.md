---
name: code-reviewer
description: Systematic code review that runs automated checks first, then does manual analysis. Use when the user asks to review, audit, or check code for issues.
license: Apache-2.0
---

# Code Review Process

## Step 1: Run automated checks

Before reading the code yourself, run the project's existing tooling to catch mechanical issues. Identify the language and run the appropriate commands:

```bash
# Python
python -m py_compile <file>        # syntax check
ruff check <file> 2>/dev/null || python -m flake8 <file> 2>/dev/null
python -m mypy <file> 2>/dev/null  # if mypy is installed

# JavaScript/TypeScript
npx tsc --noEmit 2>/dev/null       # type check
npx eslint <file> 2>/dev/null

# Go
go vet ./...

# Rust
cargo check 2>&1 | head -50
```

Also check if the project has its own lint/check commands (in `package.json` scripts, `Makefile`, `pyproject.toml`, etc.) and prefer those.

If any tool isn't installed, skip it and note that in your review. Don't ask the user to install tooling mid-review.

## Step 2: Check git context

```bash
git log --oneline -5 -- <file>     # recent change history
git diff HEAD~1 -- <file>          # what changed most recently
```

Understanding *what changed* focuses the review on new/modified code rather than relitigating existing code.

## Step 3: Manual review

Read the code. Focus your attention on things automated tools **cannot** catch:

1. **Logic correctness** - Does the code actually do what it claims? Trace through a concrete example mentally.
2. **Missing error paths** - What happens when the network is down, the file doesn't exist, the input is empty?
3. **Concurrency issues** - Shared mutable state, missing locks, race conditions between check-and-act.
4. **Security at boundaries** - User input flows, SQL construction, HTML rendering, shell command building, file path construction.
5. **Resource lifecycle** - Are connections, file handles, and subscriptions cleaned up on all paths (including error paths)?
6. **API contract mismatches** - Does the caller's assumptions match the callee's behavior? Check types at module boundaries.

Skip things the linter already covers (formatting, naming conventions, import order).

## Step 4: Run tests

```bash
# Find and run the project's test suite
# Check package.json, Makefile, pyproject.toml, Cargo.toml for test commands
```

If tests fail, note which ones and whether the failures are related to the code under review.

## Step 5: Structure your output

Use this format for each finding:

```
### [SEVERITY] Brief title

**Location:** `file.py:42`

**Problem:** One sentence explaining what's wrong.

**Fix:**
\`\`\`python
# suggested fix
\`\`\`
```

Severity levels:
- **CRITICAL** - Security vulnerability, data loss, crash in production
- **BUG** - Incorrect behavior that will manifest under normal use
- **ISSUE** - Will cause problems under edge cases or at scale
- **NIT** - Style or minor improvement, fix if convenient

End with a summary: total findings by severity, whether the code is safe to ship, and the 1-2 most important things to address.

## Gotchas

- Don't flag code that's intentionally simple (e.g., a script meant to be throwaway) with enterprise-grade concerns. Match your review depth to the code's purpose.
- If reviewing a diff, don't comment on unchanged surrounding code unless it's directly affected by the change.
- "This could be refactored" is not a useful finding unless you explain the concrete problem the current structure causes.
- Check for hardcoded secrets (API keys, passwords, tokens) in every review. This is the single most common critical finding.
- When you see a `TODO` or `FIXME`, flag it only if it's in new code. Existing TODOs are the author's known debt.
