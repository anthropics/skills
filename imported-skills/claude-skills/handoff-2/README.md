# handoff (skill)

Productivity-shaped handoff skill. Compact the current conversation into a handoff document for another agent to pick up.

See [SKILL.md](SKILL.md) for the workflow and [../../README.md](../../README.md) for the plugin-level overview.

## Quick start

```bash
# First-run setup (asks where to save handoffs)
python3 scripts/setup.py

# Generate a handoff scaffold for the next session
python3 scripts/handoff_template_generator.py --goal "your next-session goal"

# Lint the draft for secrets and PII before saving
python3 scripts/redaction_linter.py /path/to/draft.md
```

## What's in this folder

- `SKILL.md` — the skill prompt + invocation triggers + 5-section template.
- `scripts/` — 6 stdlib Python tools (setup, template generator, linter, recommender, cleanup, config loader).
- `references/` — 5 reference docs: mandatory checklist, structure, dedup discipline, redaction checklist, config reference.
- `assets/` — example handoff output.

## Inspired by

[Matt Pocock's handoff skill](https://github.com/mattpocock/skills/tree/main/skills/productivity/handoff) (MIT). The seven-sentence body of `SKILL.md` is Matt's, preserved verbatim. The wrapper is this repo's.
