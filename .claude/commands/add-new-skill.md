---
name: add-new-skill
description: Workflow command scaffold for add-new-skill in skills_claude.
allowed_tools: ["Bash", "Read", "Write", "Grep", "Glob"]
---

# /add-new-skill

Use this workflow when working on **add-new-skill** in `skills_claude`.

## Goal

Adds a new skill to the repository, including its SKILL.md and any supporting files.

## Common Files

- `skills/*/SKILL.md`
- `skills/*/LICENSE.txt`
- `skills/*/scripts/*`
- `skills/*/templates/*`
- `skills/*/examples/*`
- `skills/*/reference/*`

## Suggested Sequence

1. Understand the current state and failure mode before editing.
2. Make the smallest coherent change that satisfies the workflow goal.
3. Run the most relevant verification for touched files.
4. Summarize what changed and what still needs review.

## Typical Commit Signals

- Create a new folder under skills/ (or previously examples/, document-skills/, office-examples/).
- Add SKILL.md to the new skill folder.
- Optionally add LICENSE.txt, scripts/, templates/, examples/, or reference/ subfolders and files as needed.
- Update skills/README.md or .claude-plugin/marketplace.json if necessary.

## Notes

- Treat this as a scaffold, not a hard-coded script.
- Update the command if the workflow evolves materially.