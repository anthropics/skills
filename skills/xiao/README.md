# xiao — Xiaomi Robot Vacuum skill

Demo skill contributed from the upstream repo
[dacrypt/xiao](https://github.com/dacrypt/xiao) — a CLI that controls a
Xiaomi Robot Vacuum X20+ (`xiaomi.vacuum.c102gl`) via the Xiaomi Cloud API.

This SKILL.md is the same one that ships in the upstream repo at
`.claude/skills/xiao/SKILL.md`. For the full agent guide, machine-readable
contract (`--json`, exit codes, error-recovery protocol), and setup
instructions, see:

- Upstream repo: https://github.com/dacrypt/xiao
- Canonical agent reference: https://github.com/dacrypt/xiao/blob/main/AGENTS.md
- llms.txt: https://raw.githubusercontent.com/dacrypt/xiao/main/llms.txt

## Quick install

```bash
pip install xiao
playwright install chromium
xiao setup cloud
xiao --help
```

Then paste this skill into `~/.claude/skills/xiao/SKILL.md` (or fork the
upstream repo for the latest copy) and Claude Code will pick it up
automatically.

## License

MIT (same as upstream).
