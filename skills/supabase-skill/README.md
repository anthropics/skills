# supabase-skill

Replace the Supabase MCP server with CLI instructions + local SQLite schema cache. Zero context window overhead, 29 pre-approved commands, multi-environment support.

## Install

```bash
npm install -g @m2015agg/supabase-skill
supabase-skill install
```

## Benchmark Results (Anthropic SkillsBench)

| Metric | With Skill | Without (MCP) |
|--------|-----------|---------------|
| Pass Rate | **100% (18/18)** | 22% (4/18) |
| Avg Quality | **4.8/5** | 1.8/5 |
| Speed Wins | **4/6 evals** | 1/6 evals |

See `benchmarks/` for full data.

## What It Does

1. **Schema Cache** — Snapshots your entire database to SQLite + FTS5. Agent reads local files (~80 tokens) instead of running SQL queries (~1,247 tokens).
2. **CLI Skill Doc** — 20-section instruction set teaching agents every Supabase CLI command with correct flags.
3. **Permission Pre-Approval** — 29 read-only commands auto-approved in Claude Code.
4. **Multi-Environment** — Tag projects as prod/stage/dev, agent routes automatically.

## Links

- [npm package](https://www.npmjs.com/package/@m2015agg/supabase-skill)
- [GitHub](https://github.com/m2015agg/supabase-skill)
