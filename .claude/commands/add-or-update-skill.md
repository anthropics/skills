---
name: add-or-update-skill
description: Workflow command scaffold for add-or-update-skill in skills_claude.
allowed_tools: ["Bash", "Read", "Write", "Grep", "Glob"]
---

# /add-or-update-skill

Use this workflow when working on **add-or-update-skill** in `skills_claude`.

## Goal

Adds a new skill or updates an existing skill, including its SKILL.md and related scripts/assets.

## Common Files

- `skills/*/SKILL.md`
- `skills/*/scripts/*.py`
- `skills/*/templates/*`
- `skills/*/reference/*`
- `.claude-plugin/marketplace.json`

## Suggested Sequence

1. Understand the current state and failure mode before editing.
2. Make the smallest coherent change that satisfies the workflow goal.
3. Run the most relevant verification for touched files.
4. Summarize what changed and what still needs review.

## Typical Commit Signals

- Create or update SKILL.md in skills/<skill-name>/
- Add or update supporting scripts, templates, or assets in the skill's folder
- If applicable, update marketplace or index files (e.g., .claude-plugin/marketplace.json)
- Optionally, add language-specific guides or reference files

## Notes

- Treat this as a scaffold, not a hard-coded script.
- Update the command if the workflow evolves materially.