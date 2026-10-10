---
name: git-commit-writer
description: Write clear, conventional git commit messages from staged changes, unstaged diffs, or a described set of edits. Use whenever the user asks to "write a commit message", "commit these changes", "help me commit", generate a Conventional Commits message, split a large diff into logical commits, or draft a PR title/body from recent commits — even if they don't explicitly mention Conventional Commits or a style guide.
---

# Git Commit Writer

Turn a diff into a well-structured git commit message. The default style is [Conventional Commits](https://www.conventionalcommits.org/) because it plays well with automated changelogs and semantic-release, but the skill adapts to whatever convention the target repository already uses.

## When to use this skill

Trigger for any of these signals:

- User says "write a commit message", "commit this", "help me commit", "generate a commit", or "what should I put as the commit message".
- User pastes a diff, describes code changes, or asks for a PR title/description.
- User has staged files and wants a summary of them.
- User asks to split a large change into multiple logical commits.

## Workflow

Follow these steps in order. Skip steps only when the user has already provided the information (e.g., they pasted the diff directly).

### 1. Detect repository conventions

Before writing anything, quickly check the repo for an existing convention so the new message blends in:

```bash
# Look at the last ~20 commits for prevailing style
git log -20 --pretty=format:'%s'
# Check for a commit lint config or contributor guide
ls CONTRIBUTING.md commitlint.config.* .commitlintrc* .gitmessage 2>/dev/null
```

Rules of thumb:
- If most subject lines look like `feat(scope): ...` / `fix: ...` → use **Conventional Commits**.
- If they look like `[JIRA-123] Do the thing` → mirror the ticket-prefix style.
- If they're free-form imperative sentences → match that.
- If in doubt, default to Conventional Commits.

### 2. Read the actual changes

Never guess from filenames alone. Read the diff:

```bash
git diff --staged           # what's about to be committed
git diff                    # unstaged changes
git diff HEAD~1             # last commit's changes (for rewording)
```

For large diffs, focus on:
- Which files changed and their roles (source, test, config, docs).
- The public API surface (added/removed/renamed exports, function signatures).
- Behavior changes vs. pure refactors.
- Anything that looks like a breaking change.

### 3. Classify the change

Pick exactly one Conventional Commit type per commit:

| Type       | Use when                                                              |
|------------|-----------------------------------------------------------------------|
| `feat`     | A user-visible feature or capability is added.                        |
| `fix`      | A bug is fixed.                                                       |
| `docs`     | Docs-only change (README, comments, guides).                          |
| `refactor` | Internal restructure with no behavior change.                         |
| `perf`     | Performance improvement without changing behavior.                    |
| `test`     | Adding or fixing tests only.                                          |
| `build`    | Build system, package manager, or dependency changes.                 |
| `ci`       | CI configuration (GitHub Actions, CircleCI, etc.).                    |
| `chore`    | Housekeeping that doesn't fit above (formatting, renames, cleanup).   |
| `revert`   | Reverts a previous commit.                                            |

Optional scope in parentheses (`feat(auth): ...`) — use the top-level module, package, or directory name that changed.

### 4. Write the message

Format:

```
<type>(<optional scope>): <imperative subject, ≤ 72 chars, no trailing period>

<optional body: what changed and why, wrapped at ~72 chars, blank line after subject>

<optional footers>
```

**Subject line rules:**
- Imperative mood: "add", "fix", "remove" — not "added", "fixes", "removing".
- Lowercase first word after the colon (unless it's a proper noun).
- No trailing period.
- ≤ 72 characters. Aim for 50 if you can.

**Body rules (include when the change isn't self-explanatory):**
- Explain **what** and **why**, not **how** — the diff shows how.
- Wrap at ~72 chars.
- Reference issues/tickets in footers, not the subject.

**Footers:**
- `BREAKING CHANGE: <description>` — for breaking API changes. Also allowed as `!` after the type: `feat(api)!: drop v1 endpoints`.
- `Refs: #123`, `Closes: #456`, `Co-authored-by: Name <email>`.

### 5. Splitting a large diff into multiple commits

If the staged diff mixes unrelated concerns, propose a split before writing messages. Group hunks by:
1. Bug fixes vs. features vs. refactors — never combine.
2. Public API changes vs. internal.
3. Source vs. test vs. docs vs. build config (small doc/test bumps that accompany a code change can stay together).

Present the proposed split as a numbered list and let the user confirm, then produce one message per group. Suggest the `git add -p` workflow to stage each group.

### 6. Present the result

Always show the final message in a fenced code block so the user can copy it verbatim:

````
```
feat(auth): support passkey login

Add WebAuthn registration and assertion endpoints behind the
`AUTH_PASSKEYS` feature flag. Falls back to password login when
the flag is off.

Refs: #4821
```
````

If you produced multiple commits, show each in its own code block with a one-line description above it.

## Examples

### Example 1 — small fix

**Diff:** one-line change in `src/utils/date.ts` fixing an off-by-one in `daysBetween`.

```
fix(utils): correct off-by-one in daysBetween

The end date was excluded from the range, causing all durations
to be reported one day short. Include it and update the tests.

Closes: #312
```

### Example 2 — feature with breaking change

**Diff:** removes the old `/v1/users` endpoint and adds `/v2/users`.

```
feat(api)!: replace /v1/users with /v2/users

The v2 endpoint returns paginated results and uses cursor-based
navigation. Clients pinned to v1 must migrate before deploy.

BREAKING CHANGE: /v1/users has been removed. Use /v2/users with
the `cursor` query parameter.
```

### Example 3 — pure refactor

**Diff:** extracts `formatCurrency` into its own module; no behavior change.

```
refactor(billing): extract formatCurrency into shared module

No behavior change. Prepares for reuse in the upcoming invoice
export feature.
```

### Example 4 — docs-only

```
docs(readme): clarify local setup for Windows users
```

## Anti-patterns to avoid

- `update` / `fix stuff` / `wip` — meaningless subjects.
- Ending the subject with a period.
- Past tense (`added feature X`).
- Mentioning file names in the subject when a scope would do (`fix(auth)` beats `fix login.ts`).
- Combining unrelated changes in one commit.
- Restating the diff in the body — say **why**, not **what line changed**.

## Handoff

If the user wants you to actually create the commit, run:

```bash
git commit -m "<subject>" -m "<body>"
```

Otherwise just output the message and let them run it themselves. For messages with complex bodies, suggest:

```bash
git commit -F- <<'MSG'
<paste the full message here>
MSG
```

## Further reading

- [`references/conventional-commits.md`](references/conventional-commits.md) — quick reference for the Conventional Commits spec.
