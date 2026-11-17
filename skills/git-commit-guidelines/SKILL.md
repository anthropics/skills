---
name: git-commit-guidelines
description: Provides guidelines for writing clear and effective Git commit messages.
---

When writing a commit message:

1. Run `git diff --staged` (or `git diff`) to review exactly what changed before writing the message.
2. Follow this structure:

## Subject line
- Use the imperative mood ("Add", "Fix", "Update" — not "Added" or "Adds")
- Keep it to 50 characters or fewer
- Don't end it with a period
- Capitalize the first word
- Summarize *what* changed, not how

## Body (optional, separated by a blank line)
- Wrap lines at ~72 characters
- Explain *why* the change was made and what problem it solves, not a restatement of the diff
- Note any non-obvious side effects, trade-offs, or follow-up work
- Use bullet points for multiple distinct changes

## General best practices
- Keep commits atomic: one logical change per commit
- Write each commit so it stands on its own and could be reverted cleanly
- Reference related issues/tickets when relevant (e.g. `Fixes #123`)
- Avoid vague messages like "fix stuff", "wip", or "update"
- Don't mix unrelated changes (e.g. a refactor and a bug fix) in one commit
