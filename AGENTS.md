# Repository Guidelines

Each skill lives in `skills/<skill-name>/` and must include a `SKILL.md`. That's the minimum.

Optional folders inside a skill: `scripts/` for automation, `references/` for long-form guidance, `assets/` for templates and media. Use kebab-case for skill directories (`webapp-testing`, not `webapp_testing`).

- `template/SKILL.md` — starting point for new skills
- `spec/agent-skills-spec.md` — points to the current Agent Skills spec
- `.claude-plugin/marketplace.json` — plugin bundle definitions

## Commands

No repo-wide build pipeline. Validate what you changed.

```bash
# Validate a skill
python3 skills/skill-creator/scripts/quick_validate.py skills/<skill-name>

# Scaffold a new skill
python3 skills/skill-creator/scripts/init_skill.py my-new-skill --path skills

# Package for distribution
python3 skills/skill-creator/scripts/package_skill.py skills/<skill-name> ./dist
```

Some skills have their own dependencies:

```bash
python3 -m pip install -r skills/mcp-builder/scripts/requirements.txt
python3 -m pip install -r skills/slack-gif-creator/requirements.txt
```

## Style

`SKILL.md` files start with YAML frontmatter. Required keys: `name` and `description`. Keep `name` lowercase kebab-case, max 64 characters, matching the folder name. Write concise, task-oriented sections with real examples. Python scripts follow PEP 8: 4-space indentation, clear function names.

## Testing

Run `quick_validate.py` on every skill you touch. If you change a script, run a basic smoke test (`python3 <script> --help` or a sample input). For packaging changes, generate a `.skill` artifact and confirm the expected files are present.

## Commits and PRs

Short imperative subject lines with a type prefix (`feat: ...`). Keep commits focused to one skill or one logical change.

PRs need:
- What changed and why
- Affected paths (e.g. `skills/pdf/`, `skills/skill-creator/scripts/`)
- Validation commands run and results
- Screenshots or artifacts when output is visual

## Security

No secrets, tokens, or private keys in commits. When adding third-party content or dependencies, update `THIRD_PARTY_NOTICES.md`.
