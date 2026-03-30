---
name: linkedin-intel
description: >-
  Orchestrates the linkedin-mcp server for LinkedIn research tasks.
  Triggers on: hiring manager lookup, recruiter search, org chart mapping,
  job market analysis, salary benchmarking, hidden job market, interview
  prep, competitive intelligence, company team research, person dossier,
  LinkedIn profile lookup. Read-only scraping via headless Chromium.
  Does NOT post, message, connect, or modify LinkedIn data.
---

# LinkedIn Intel

Research people, companies, jobs, and teams on LinkedIn via the linkedin-mcp
MCP server. All tools are read-only scrapers — no write operations.

## Prerequisite

The linkedin-mcp MCP server must be connected. If tools return auth errors,
the user must run: `uv run -m linkedin_mcp_server --login`

## Rate Limiting

Execute LinkedIn tool calls **sequentially, never in parallel**. The server
uses mixture-model timing (1.2-12s) for anti-detection.

## Dispatch

Route requests to the appropriate reference file before calling tools.

| Request type | Read first |
|---|---|
| Person profile / dossier | [reference/fields.md](reference/fields.md) then [reference/tools.md](reference/tools.md) |
| Company profile / team | [reference/fields.md](reference/fields.md) then [reference/tools.md](reference/tools.md) |
| Job search / salary data | [reference/tools.md](reference/tools.md) |
| Multi-step workflow (hiring manager, org chart, interview prep, etc.) | [reference/plays.md](reference/plays.md) |
| Combine with other MCP servers or skills | [reference/cross-mcp.md](reference/cross-mcp.md) |

## Output Format

Return a structured markdown brief with one section per entity. Include:

- Source attribution (which tool returned each data point)
- Data gaps (what was requested but not found)
- Timestamps (when the data was scraped)

For multi-entity results, use tables for comparison.
