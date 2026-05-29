---
name: agent-memory
description: Teach cross-session memory patterns using MEMORY.md — what to save, how to organize it, how to maintain it over time, and how to structure topic files as memory grows. Works in any Claude Code project with no external dependencies. Trigger words: remember this, save for later, across sessions, persistent memory, don't forget, note this, keep this, write this down.
license: MIT
metadata:
  author: sagemindai
  version: "1.0"
---

# agent-memory — Cross-Session Memory Patterns for Claude Code

Claude Code has no memory between sessions by default. Every conversation starts blank. But a project's knowledge accumulates — commands discovered, patterns debugged, preferences revealed, mistakes made and corrected. Without persistence, that knowledge is lost every time the window closes.

This skill establishes a simple, durable memory pattern using a single file: `MEMORY.md`.

---

## The Core Pattern

One file. Written by the agent. Read at session start.

```
.claude/
  MEMORY.md          # The agent's persistent knowledge base
  identity/          # Optional: separate identity files (see agent-identity skill)
  memory/            # Optional: topic files as memory grows
    debugging.md
    deployment.md
    user-preferences.md
```

---

## Setting Up MEMORY.md

Create `.claude/MEMORY.md` with this structure:

```markdown
# [Project/Agent] Memory

> This file persists across sessions. Write here when you learn something
> worth remembering. Remove entries that become outdated. Keep it useful,
> not comprehensive.

## Project Patterns

[Commands, scripts, conventions specific to this project]

## Tools & Scripts

[Purpose-built scripts and how to invoke them]

## Lessons Learned

[Mistakes made and corrections. Dated entries.]

## User Preferences

[Communication style, workflow preferences, discovered through interaction]

## Open Questions

[Unresolved things to investigate — remove when resolved]
```

Then add this to your `CLAUDE.md`:

```markdown
## Memory

At the start of every session, read `.claude/MEMORY.md` before doing any work.
After context compaction, re-read it immediately.

When you learn something worth keeping, write it to MEMORY.md before the session ends.
```

---

## What to Write vs. What to Skip

The most common mistake: writing everything, making the file so long it stops being read carefully.

**Write to MEMORY.md:**

- Project-specific commands, especially non-obvious ones
  - "Run `npm run build:prod` not `npm run build` — the latter overwrites staging"
- Scripts you built and their locations
  - ".claude/scripts/check-email.py — reads Gmail unread, takes --limit flag"
- Mistakes made once that shouldn't happen again
  - "2025-03-12: Pushed to main while on detached HEAD. Always verify branch before committing."
- User preferences discovered through interaction, not assumed
  - "Prefers Telegram summaries over file links"
- Patterns that took time to figure out
  - "Prisma requires explicit `include` for relations — no auto-eager-loading"

**Do not write to MEMORY.md:**

- Session-specific context ("currently working on auth PR")
- Information available in the codebase or docs
- Reminders for things you'll do this session (use a TODO comment)
- Generic programming knowledge any agent would have
- Things that will be outdated next week

The test: *Would a fresh session six months from now benefit from this?* If no, skip it.

---

## Organizing Growing Memory

MEMORY.md works well up to ~150-200 lines. Beyond that, introduce topic files:

```bash
mkdir -p .claude/memory
```

Move detailed sections to topic files and keep MEMORY.md as an index:

```markdown
# Memory Index

## Quick Reference

- Build: `npm run build:prod`
- Deploy: `.claude/scripts/deploy.sh --env production`
- DB migrate: `npm run db:migrate` (always after schema changes)

## Topic Files

- Debugging patterns: `.claude/memory/debugging.md`
- Deployment notes: `.claude/memory/deployment.md`
- User preferences: `.claude/memory/user-preferences.md`
- API integrations: `.claude/memory/apis.md`

## Recent Lessons

[Last 3-5 lessons only — older ones move to topic files]
```

Reference topic files in `CLAUDE.md`:

```markdown
## Memory

Read at session start:
- `.claude/MEMORY.md` — always
- `.claude/memory/debugging.md` — when debugging
- `.claude/memory/deployment.md` — when deploying
```

---

## Writing Memory During a Session

Don't wait until the session ends. Write memory entries when you learn something:

```bash
# Append an entry immediately
cat >> .claude/MEMORY.md << 'EOF'

## New Discovery (2025-03-20)

- The Redis connection string requires `?family=6` for IPv6 — without it,
  connections timeout silently on this server.
EOF
```

When adding a dated lesson:

```bash
DATE=$(date +%Y-%m-%d)
cat >> .claude/MEMORY.md << EOF

## Lesson (${DATE})

- [What happened, what was wrong, what the correct approach is]
EOF
```

---

## Maintaining Memory Over Time

Memory files need occasional pruning — entries go stale, contexts change, projects evolve.

**Review MEMORY.md when:**
- Starting a major new phase of the project
- A remembered pattern stops being true
- The file grows past 200 lines

**What to prune:**
- Lessons from debugging a problem that's now fixed and closed
- Preferences that were superseded
- Scripts that no longer exist
- Anything prefixed "TODO" that was resolved

**What to archive, not delete:**
- Significant debugging investigations (move to `.claude/memory/archive/`)
- Historical context that might matter for understanding decisions

---

## Memory vs. Documentation

MEMORY.md is not documentation. It's the agent's personal notebook.

| MEMORY.md | Docs (`docs/`) |
|-----------|----------------|
| For the agent | For humans |
| Informal, first-person | Structured, third-person |
| Includes mistakes and corrections | Shows correct state |
| Updated constantly | Updated deliberately |
| Short entries OK | Complete explanations expected |

Don't put architecture decisions in MEMORY.md. Do put "when I touch the auth module, I always forget to rebuild the token cache — run `npm run cache:reset` after any change to `lib/auth/`."

---

## Memory After Compaction

Context compaction is the main threat to in-session memory. When the context window fills and compresses, the agent loses anything it learned mid-session that wasn't written to disk.

Two protections:

1. **Write early** — When you learn something important, write it to MEMORY.md before you forget or before compaction hits.

2. **Re-read after compaction** — Claude Code fires a `PostCompact` notification event when context compresses. If you have a hook registered for it, you can automatically re-read MEMORY.md. Without a hook, train yourself to re-read when you notice context was compressed.

---

## Multiple Agents, Shared Memory

When multiple agents work on the same project, they can share MEMORY.md — but this requires a discipline: write facts, not opinions. Shared memory entries should be:

- Verifiable ("The deploy script requires X")
- Durable ("This pattern has been stable for 3 months")
- Agent-neutral ("Whoever runs this, the same caveat applies")

Agent-specific preferences, styles, or goals should stay in each agent's own identity files (see the `agent-identity` skill).
