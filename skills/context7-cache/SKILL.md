---
name: context7-cache
description: "Local documentation cache for coding tasks. Caches library docs in SQLite+FTS5, serving them via CLI instead of MCP round-trips. TRIGGER when: user asks about library APIs, needs code examples, or is implementing features that require documentation lookup. Requires: npm package @m2015agg/context7-skill, Node.js 18+."
license: Complete terms in LICENSE.txt
---

# Context7 Cache — Local Documentation for AI Agents

Cache library documentation locally in SQLite+FTS5. Query cached docs first, fall back to Context7 API only when needed.

## Why Use This Instead of Context7 MCP

| Metric | CLI Cache | MCP Server |
|--------|-----------|------------|
| Pass Rate | 93% ± 10% | 87% ± 12% |
| Speed | 17.9s end-to-end | 31.9s end-to-end (1.8x slower) |
| Raw lookup | 64ms (SQLite) | 1,270ms (API round-trip) |
| Hallucinations | None observed | Fabricated API params in 3/3 FastAPI runs |
| Consistency | ± 10% variance | ± 12% variance |
| Context cost | ~1,666 tokens | ~3,077 tokens |
| Offline | Yes | No |

*Benchmarked using Anthropic SkillsBench framework with LLM grader (Sonnet 4.6). 3 evals × 3 runs per config, 10 turns for MCP.*

## Setup (One-Time)

If `context7-skill` is not installed, guide the user through setup:

```bash
npm install -g @m2015agg/context7-skill
context7-skill install      # Global: API key, config, CLAUDE.md
context7-skill init          # Per-project: detect deps, cache docs, approve permissions
```

`init` automatically:
1. Scans dependency files (package.json, requirements.txt, pyproject.toml, etc.)
2. Resolves each dependency on Context7
3. Pre-caches documentation in local SQLite with FTS5
4. Writes CLAUDE.md instructions and pre-approves read commands

## How to Look Up Documentation

### Search across all cached libraries
```bash
context7-skill search "dependency injection"
```

### Get docs for a specific library
```bash
context7-skill docs fastapi "how to use Depends()"
context7-skill docs supabase "row level security policies"
context7-skill docs celery "configure redis broker"
```

Accepts library names (`fastapi`) or Context7 IDs (`/fastapi/fastapi`).
Cache-first: returns instantly from SQLite if cached and fresh (7-day TTL).
Falls back to Context7 API if not cached, then caches for next time.

### Force fresh fetch (bypass cache)
```bash
context7-skill docs fastapi "background tasks" --no-cache
```

### List what's cached
```bash
context7-skill libs
```

### Check cache health and token savings
```bash
context7-skill cache stats
```

## Before Implementing Any Plan

When planning a feature implementation:

1. Read the plan requirements
2. Identify libraries or technologies mentioned
3. Check if they're cached: `context7-skill libs`
4. For any missing library: `context7-skill add <library-name>`
5. Look up relevant docs: `context7-skill docs <library> <what-you-need>`
6. Proceed with implementation using cached docs

## After Adding Dependencies

When new packages are added to requirements.txt, package.json, etc.:
```bash
context7-skill snapshot
```
This re-detects dependencies, resolves new ones, and caches their docs.

## Managing Libraries

```bash
# Manually add a library not in dependency files
context7-skill add langchain

# Remove a cached library
context7-skill remove langchain

# Compare project deps vs cached libraries
context7-skill diff
```

## Troubleshooting

```bash
# Full health check (10 checks)
context7-skill doctor

# If cache is stale (>7 days)
context7-skill snapshot

# If docs seem wrong
context7-skill docs <library> <query> --no-cache
```

## How It Works

- Dependencies detected from: package.json, requirements.txt, pyproject.toml, Pipfile, go.mod, Cargo.toml, Gemfile
- Import frequency counted across source files — heavily-used libraries get more pre-cached queries
- Version-aware: detects pinned versions and uses version-specific docs when available
- Global resolution cache at `~/.config/context7-skill/global-cache.db` — cross-project, so resolving `fastapi` once benefits all projects
- Token savings tracked: `cache stats` shows cumulative tokens served from cache vs API
