---
name: review
description: "Generate a daily Claude Code usage review — token costs, session habits, and actionable suggestions including command/skill recommendations. Use when: user says 'review', 'daily review', 'usage report', 'what did I do today'. Do NOT use for: code review or PR review."
---

# Daily Usage Review

Generate a concise daily review of Claude Code usage with cost analysis, habit insights, and personalized command/skill recommendations.

## Arguments

- Optional date: `YYYY-MM-DD` (defaults to today)
- `--save`: write output to `./review-{DATE}.md`

## Step 1 — Date & Environment

Determine review date. Detect available data sources:

```bash
command -v ccusage &>/dev/null && echo "has_ccusage" || echo "no_ccusage"
[ -f ~/.claude/hooks/logs/bash-history.log ] && echo "has_bash_hook" || echo "no_bash_hook"
```

## Step 2 — Token Cost Analysis

**With ccusage:**
```bash
ccusage session && ccusage daily --days 7
```

**Without ccusage (JSONL fallback):**

Parse `~/.claude/projects/*/*.jsonl` (skip `*/subagents/*`). For each file modified on the target date, sum `usage` fields from assistant messages: `input_tokens`, `output_tokens`, `cache_creation_input_tokens`, `cache_read_input_tokens`.

Cost estimate (Sonnet 4.6): input $3/M, output $15/M, cache_creation $3.75/M, cache_read $0.30/M.

Track: session count, short sessions (≤5 messages), and 7-day daily totals.

Distill **1-2 cost suggestions** from the data (e.g., too many short sessions → use `/compact`).

## Step 3 — Bash Commands (if hook available)

```bash
grep "^\[{DATE}" ~/.claude/hooks/logs/bash-history.log
```

Summarize: total count, top tool types (git/python/ssh/curl), active directories.

## Step 4 — Skill Usage

List installed skills:
```bash
ls ~/.claude/skills/ 2>/dev/null | grep -v INDEX
```

Detect which skills were invoked in the last 3 days (from bash-history or session JSONL).

Report:
- Skills used today
- Skills **not used in 3 days** → suggest cleanup

## Step 5 — Command & Skill Recommendations (MANDATORY)

Every review MUST include ALL of the following:

### 5a. Latest commands (1-2)
Fetch the changelog:
```
WebFetch: https://raw.githubusercontent.com/anthropics/claude-code/main/CHANGELOG.md
Prompt: Extract new slash commands or CLI features from the last 3 versions. Each: name, one-line description, version.
```
Pick 1-2 that match the user's workflow. Explain why.

### 5b. Commonly used but unused commands (2)
From this reference list, pick 2 that the user didn't use today but should have based on their activity:
- `/compact` — compress context, save tokens
- `/resume` — resume a previous session
- `/model` — switch models mid-session
- `/cost` — check current spend
- `/memory` — manage persistent memories
- `/config` — modify settings
- `/terminal` — open terminal
- `/vim` — vim mode
- `/fast` — fast output mode (same model)
- `/clear` — clear context
- `/pr-review` — PR review
- `/init` — initialize project CLAUDE.md

Each must explain **why it fits this user's workflow**.

### 5c. Official skills (2)
Fetch official skills:
```
WebFetch: https://raw.githubusercontent.com/anthropics/claude-code/main/SKILLS.md
Prompt: List all officially recommended skills with name, description, install method.
```
If unavailable, use skills mentioned in the CHANGELOG. Pick 2 relevant to user's work. Explain why.

## Step 6 — Output

Target: under 25 lines.

```
# Daily Review · {DATE}

**Overview**: {N} sessions · {N} commands · est. ${X.XX}
**7-day avg**: ${X.XX}/day · week total ${X.XX}

**What you worked on**
- [3 specific bullets from commands + sessions]

**Suggestions**
- [1-2 cost/habit suggestions with data]

**Skill usage**
- Used today: /xxx, /yyy
- Not used in 3 days: /aaa, /bbb → still need these?

**Recommendations**
- 🆕 New: `/xxx` (vX.X.X) — [why it fits you]
- 💡 Try: `/xxx` — [reason], `/yyy` — [reason]
- 📦 Skills: `name` — [desc], `name` — [desc]

**One thing for tomorrow**: [single highest-impact change]
```

If bash-history hook is missing, append:
`Tip: install a bash-history hook for richer command tracking.`
