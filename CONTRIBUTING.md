# Contributing

## Adding a new skill

1. Read the [Agent Skills specification](https://agentskills.io/specification) and [best practices](https://agentskills.io/skill-creation/best-practices)
2. Create a directory named after your skill (lowercase, hyphens only)
3. Add a `SKILL.md` with valid frontmatter (`name`, `description` required)
4. Keep `SKILL.md` under 500 lines. Move detailed content to `references/`, `scripts/`, or `assets/`
5. Open a PR

## Quality checklist

Before submitting, verify:

- [ ] `name` field matches the directory name
- [ ] `description` explains both *what* the skill does and *when* to use it
- [ ] Instructions focus on what an agent *wouldn't already know* — specific procedures, gotchas, and tooling rather than general knowledge
- [ ] Bundled scripts (if any) are self-contained with clear error messages
- [ ] No binary files, secrets, or generated artifacts (add them to `.gitignore`)
- [ ] You've tested the skill with at least one agent to verify it works

## Improving existing skills

Bug fixes, gotcha additions, and script improvements to existing skills are welcome. If you've used a skill and found a case where it gave bad guidance, adding a correction to the gotchas section is one of the highest-value contributions.

## License

Contributions are licensed under Apache-2.0 unless otherwise noted in the skill's `license` field.
