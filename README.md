# skills_claude

Hub for my Claude Code project skills.

## Layout

```
CLAUDE.md                 # always-on ponytail (lazy senior dev) ruleset
.claude/skills/           # project skills, loaded on demand
  ponytail/               # lazy mode itself
  ponytail-review/        # over-engineering review of a diff
  ponytail-audit/         # over-engineering audit of the whole repo
  ponytail-debt/          # harvest `ponytail:` shortcut comments into a ledger
  ponytail-gain/          # measured-impact scoreboard
  ponytail-help/          # quick-reference card
.claude-plugin/           # marketplace.json, so the skills install as a plugin
```

## Skills

| Skill | Trigger | What it does |
|-------|---------|--------------|
| ponytail | `/ponytail` | Lazy senior dev mode: simplest solution that works. |
| ponytail-review | `/ponytail-review` | Reviews a diff only for over-engineering. |
| ponytail-audit | `/ponytail-audit` | Audits the whole repo for what to delete. |
| ponytail-debt | `/ponytail-debt` | Collects `ponytail:` shortcut comments into a ledger. |
| ponytail-gain | `/ponytail-gain` | Shows ponytail's measured impact. |
| ponytail-help | `/ponytail-help` | Reference card for all ponytail modes. |

`CLAUDE.md` is loaded automatically for every session in this repo; the
`.claude/skills/` skills load when invoked.

## Install as a plugin

```
/plugin marketplace add SpiritAnima1/skills_claude
/plugin install ponytail@ponytail-skills
```

## Credits

The ponytail ruleset and companion skills are adapted from
[DietrichGebert/ponytail](https://github.com/DietrichGebert/ponytail).
