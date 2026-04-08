---
name: claude-code-token-optimization
description: Use when session costs feel high, context fills quickly, choosing between Haiku/Sonnet/Opus, or wanting to reduce token usage in Claude Code workflows.
compatibility: Designed for Claude Code
license: MIT
metadata:
  author: Randagio13
---

# Claude Code Token Optimization

## Quick Command Reference

| Command | Effect | Est. Savings |
|---|---|---|
| `/compact [focus hint]` | Summarise history, re-inject CLAUDE.md fresh | 20–30% |
| `/clear` | Wipe history, keep code changes | 100% of history |
| `/model haiku` | Switch to cheapest model (1× cost) | up to 90% |
| `/model sonnet` | Balanced default (5–6× Haiku) | baseline |
| `/model opus` | Deepest reasoning (12× Haiku) | — |
| `/model opusplan` | Plan in Opus, execute in Sonnet | 25–40% |
| `/effort low` | Disable extended thinking | 20–30% |
| `/effort high` | Enable extended thinking | — |
| `/cost` | Show session spend (API mode) | visibility |
| `/context` | Visualise token usage grid | insight |
| `! <cmd>` | Run bash directly, skip tool overhead | 3–8% |

## Model Quick-Pick

```
Simple refactoring, subagent work    → haiku   + /effort low
Daily coding, bug fixes, features    → sonnet  + /effort medium  ← default
Complex debugging                    → sonnet  + /effort high
Architecture, deep reasoning         → opus    + /effort high
Multi-phase plan + implement         → opusplan
```

## Top Savings Strategies (ranked)

1. **Switch to Haiku for simple work** — up to 90%
2. **Specific prompts** ("fix auth.ts line 47" not "improve codebase") — 30–40%
3. **Subagents for exploration** — isolate heavy reads; only summary returns — 30–50%
4. **`/compact` proactively** — before switching tasks, not just at limit — 20–30%
5. **`/effort low`** for routine tasks — 20–30%
6. **Skills instead of long CLAUDE.md** — on-demand vs every request — 15–20%
7. **Move specialised rules to `.claude/rules/`** — path-scoped, loads on demand — 10–15%

## What Loads at Every Startup (~7,850 tokens before any work)

| Component | Tokens |
|---|---|
| System prompt | 4,200 |
| Project CLAUDE.md | 1,800 ← biggest lever you control |
| Auto memory | 680 |
| Environment info | 280 |
| Skill descriptions | 450 |
| MCP schemas | 120+ |

A 50 KB source file read adds ~12,500 tokens. Thinking tokens (`/effort high`) add 8K–32K billed as output.

## CLAUDE.md Rules

**Keep under 200 lines.** Include: build/test commands, conventions, "never do X" rules.

**Move to `.claude/rules/` with path scoping** (only loads when matching files accessed):
```markdown
---
paths:
  - "src/**/*.tsx"
---
# React rules — only loaded for tsx files
```

**Move to skills:** anything invoked occasionally (deployment checklists, API docs, specialised workflows).

## Auto-Compact Config

```bash
CLAUDE_CODE_DISABLE_AUTO_COMPACTION=1    # disable auto-compact
MAX_THINKING_TOKENS=4000                 # cap thinking budget
CLAUDE_CODE_DISABLE_ADAPTIVE_THINKING=1  # disable thinking entirely
claude -p --max-budget-usd 5.00 "query"  # session spend cap
claude -p --max-turns 3 "query"          # limit agentic turns
```

Add a compaction hint to your CLAUDE.md:
```markdown
## Compact instructions
Preserve: test failures, code changes, API patterns, decisions made.
Discard: exploratory analysis, intermediate steps.
```

## Typical Costs (Sonnet, approximate)

- Per developer per day: ~$6
- 90th percentile: < $12/day
- Monthly average: $100–200/developer
