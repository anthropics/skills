# refactor-code (plugin)

The `refactor-code` Agent Skill, packaged for Claude Code plugin installation.

For Claude Code:

```
/plugin install refactor-code@refactor-code
```

The **portable skill itself** lives in `skills/refactor-code/` and conforms to the [Agent Skills open standard](https://agentskills.io/). That folder is what you copy into any other agent's skills directory — ChatGPT, Codex CLI, Gemini CLI, Cursor, etc. See the [top-level README](../../README.md#install) for platform-by-platform install commands.

## Layout

- `.claude-plugin/plugin.json` — Claude Code plugin manifest
- `skills/refactor-code/SKILL.md` — the skill definition (this is the portable bit)
- `skills/refactor-code/references/` — catalogs of code smells, refactoring techniques, design patterns, and linting rules by language
- `evals/` — test prompts and inputs used to verify the skill
