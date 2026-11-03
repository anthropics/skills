# /review — Daily Usage Review for Claude Code

**You spend $50-150/day on Claude Code but have no idea where the money goes.**

This skill fixes that. Run `/review` at the end of your day and get:

- How much you spent, how many sessions, what you actually did
- Which habits are costing you money (too many short sessions, wrong model, etc.)
- Commands and skills you should be using but aren't

## The Problem

Claude Code users face three blind spots:

1. **Cost opacity** — No built-in way to see daily/weekly spend breakdown
2. **Habit unawareness** — Starting 10+ sessions/day when `/compact` would save 80% of cache creation costs
3. **Feature discovery** — Claude Code ships new commands constantly, but users stick to the 3-4 they know

## What It Does

```
/review              # review today
/review 2026-03-19   # review a specific date
/review --save       # save to ./review-2026-03-20.md
```

Output (~20 lines):

```
# Daily Review · 2026-03-20

**Overview**: 7 sessions · 90 commands · est. $26.27
**7-day avg**: $65.88/day · week total $461.15

**What you worked on**
- Server debugging via SSH (22 calls)
- Blog development with Hugo
- Claude Code cost optimization — migrated MCP config, redesigned skills

**Suggestions**
- Today $26 vs weekly avg $66 — session discipline is working, keep it up
- 31 `ls` + 20 `find` calls — use Glob/Grep tools instead, faster and cheaper

**Skill usage**
- Used today: /review, /cost, /model
- Not used in 3 days: /publish, /decide → still need these?

**Recommendations**
- 🆕 New: `/fast` (v2.1.80) — same Opus model, faster output. Perfect for iterative work
- 💡 Try: `/compact` — you opened 7 sessions, could've been 3 with compact
- 💡 Try: `/resume` — pick up where you left off instead of new session
- 📦 Skills: `frontend-design` — you touched Hugo templates today
- 📦 Skills: `claude-api` — useful if you're building with Claude's API

**One thing for tomorrow**: use `/compact` before opening a new session
```

## Key Design Decisions

### Mandatory recommendations
Every review **must** include:
- 1-2 latest commands from the CHANGELOG
- 2 built-in commands you didn't use but should have
- 2 official skills relevant to your work

This isn't optional. The whole point is surfacing things you don't know about.

### Suggestions over data
Users don't need token breakdowns — they need "you're wasting money because X, do Y instead." The skill shows just enough numbers to be credible, then focuses on actionable advice.

### Zero config
Works out of the box. Reads `~/.claude/projects/` for session data. Optionally reads bash-history hook logs for richer command analysis. Supports `ccusage` if installed.

## Data Sources

| Source | Required? | What it provides |
|--------|-----------|------------------|
| `~/.claude/projects/*/*.jsonl` | Yes (always exists) | Session count, token usage, cost estimate |
| `~/.claude/hooks/logs/bash-history.log` | Optional (hook) | Command count, tool breakdown, active projects |
| `ccusage` CLI | Optional (npm install) | Faster, more accurate cost data |
| Claude Code CHANGELOG | Fetched live | Latest feature/command recommendations |

## Install

Copy `SKILL.md` to your Claude Code skills directory:

```bash
mkdir -p ~/.claude/skills/review
curl -o ~/.claude/skills/review/SKILL.md \
  https://raw.githubusercontent.com/anthropics/skills/main/skills/review/SKILL.md
```

Then just type `/review` in Claude Code.

## Languages

- **English**: this skill (`/review`)
- **中文版**: see [review-zh/SKILL.md](../review-zh/SKILL.md) — 同样的功能，中文输出

## License

Apache 2.0
