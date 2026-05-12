---
name: git-history
description: "Git history intelligence for coding tasks. Indexes entire git history into SQLite+FTS5, computes analytics (churn hotspots, coupling, decision points, quality metrics), and writes health summaries to Claude memory. TRIGGER when: user asks about codebase evolution, prior attempts, file history, who wrote code, why something was changed, or before modifying high-churn files. Requires: npm package @m2015agg/git-skill, Node.js 18+."
license: Complete terms in LICENSE.txt
---

# Git History Intelligence for AI Agents

Give AI agents institutional memory over a codebase's evolution, decisions, and health trends. Indexes git history into SQLite with FTS5 search, computes derived analytics, and writes a health summary directly into Claude's memory system.

## Why This Exists

AI coding agents start every session blind. They don't know which files are churning, what was reverted last week, or that someone already tried the approach they're about to suggest. git-skill fixes this by making git history queryable, analyzable, and automatically loaded into context.

## What It Enables

- **"We tried that already"** — `verify` checks staged changes against enriched history before committing
- **"Why does this keep breaking?"** — Churn hotspots and fix-on-fix metrics surface unstable files
- **"Who knows this code?"** — Author expertise mapping per file/directory
- **"The agent has no memory"** — Health summary written to Claude's memory system every commit

## Setup (One-Time)

If `git-skill` is not installed, guide the user through setup:

```bash
npm install -g @m2015agg/git-skill
git-skill config             # Interactive: configure embeddings + API key
git-skill init               # Per-project: hook, snapshot, workflow commands, 30-day context
```

`init` automatically:
1. Installs post-commit hook (captures commits + refreshes memory)
2. Indexes full git history into SQLite
3. Computes analytics (hotspots, coupling, decisions, expertise, metrics)
4. Writes 30-day health summary to Claude's memory
5. Installs workflow commands (`/plan`, `/implement`, `/review`, `/finalize`, `/trace`)
6. Pre-approves read-only commands

## How to Search History

### Full-text search (BM25 + vector hybrid when embeddings exist)
```bash
git-skill search "auth refactor"
git-skill search "rate limiting" --bm25    # force keyword-only
```

### File/directory evolution
```bash
git-skill timeline src/auth/
git-skill timeline src/api/routes.ts --since 2026-01-01
```

### Who has context on a file
```bash
git-skill experts src/services/
```

### What changes together
```bash
git-skill coupling src/auth/index.ts
```

## How to Check Codebase Health

### Churn hotspots (which files are most volatile)
```bash
git-skill hotspots --limit 10
```

### Major decision points (reverts, refactors, architecture changes)
```bash
git-skill decisions
git-skill decisions --type revert
```

### Quality metrics over time
```bash
git-skill trends
git-skill regression         # detect change-point shifts
```

### Full health check
```bash
git-skill doctor
```

## Before Committing: Verify Against History

Check if staged changes repeat a known mistake:

```bash
git add .
git-skill verify
```

Returns per-file:
- **PASS** — no concerning history
- **WARN** — file has been churning or relates to a reverted change
- **BLOCK** — change re-introduces something that was explicitly reverted

Works without LLM (local analysis: edit counts, revert history). With LLM configured, provides deep reasoning about why previous attempts failed.

## Understanding a Commit

### View enrichment (intent, reasoning, impact)
```bash
git-skill why <hash>
git-skill why HEAD
```

### Range summary
```bash
git-skill diff-summary v1.0..v1.1
```

### Enhanced blame
```bash
git-skill blame src/auth/index.ts
```

## Dev Workflow Commands

`init` installs gated slash commands:

```
/plan → /implement → /review → /finalize
```

- `/plan` checks git history for prior attempts before designing features
- `/implement` follows TDD with WIP commits for backup
- `/review` soft-resets last WIP commit, runs `verify` on staged changes, re-commits clean
- `/finalize` final verify, PR ready for merge
- `/trace` debug unexpected behavior by tracing broken assumptions across git history

Each phase stops and waits for approval before proceeding.

## Debugging with Git History

When code looks correct but behaves wrong, use `/trace` or the `historical-context-debugging` skill:

```bash
git-skill search "feature keyword"     # find related commits
git-skill why <hash>                   # understand original assumptions
git-skill timeline <file>              # see all changes chronologically
git-skill verify                       # validate fix against history
```

Three fault types to look for:
1. **Missing Guard** — a flag exists for case X but not similar case Y
2. **Parallel Evolution** — two systems built independently that should share logic
3. **Stale Side Effect** — code updated but cache/config/state wasn't

## Optional: LLM Enrichment

Analyze each commit with an LLM (Anthropic or OpenAI) to extract intent, reasoning, and impact:

```bash
git-skill config       # set up API key
git-skill enrich       # analyze all unenriched commits
```

Enrichments power deeper `verify` analysis and semantic search.

## Optional: Embeddings

For semantic search ("auth changes" finds "login", "session", "JWT"):

```bash
git-skill config       # set up embedding provider (Ollama is free)
git-skill embed        # generate embeddings for commits + enrichments
```

## Automation

**Every commit** (post-commit hook):
- Captures new commit to SQLite + FTS
- Refreshes Claude memory with latest alerts (5-min cache)

**Nightly** (`git-skill cron`):
- Fetches team members' commits
- Full re-index + analytics + metrics + auto-embed + memory update

## Memory System Integration

`context-update` writes a health summary to `~/.claude/projects/<path>/memory/git_context.md`:
- Codebase state (commits, branches, tags)
- Hotspots (last 30 days + all-time)
- Recent decisions (reverts, refactors)
- Health metrics (revert rate, fix-on-fix rate)
- Active alerts (thrashing, revert chains, fix-on-fix patterns)
- Recent activity digest

Claude's `findRelevantMemories` loads this at session start when doing code work.

## Troubleshooting

```bash
git-skill doctor              # full health check
git-skill snapshot --force    # rebuild from scratch
git-skill context-update --days 30   # regenerate memory context
```
