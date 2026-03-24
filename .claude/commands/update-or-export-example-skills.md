---
name: update-or-export-example-skills
description: Workflow command scaffold for update-or-export-example-skills in skills_claude.
allowed_tools: ["Bash", "Read", "Write", "Grep", "Glob"]
---

# /update-or-export-example-skills

Use this workflow when working on **update-or-export-example-skills** in `skills_claude`.

## Goal

Bulk updates or exports of example skills, often including renaming, reorganizing, or synchronizing multiple skill folders and their contents.

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

- Modify, move, or rename multiple skill folders (e.g., from examples/ to skills/, or document-skills/).
- Update SKILL.md and supporting files for each skill.
- Update marketplace.json or skills/README.md as needed.

## Notes

- Treat this as a scaffold, not a hard-coded script.
- Update the command if the workflow evolves materially.