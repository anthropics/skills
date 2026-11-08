---
source: https://github.com/firecrawl/skills/tree/main/skills/core/firecrawl-crawl
name: firecrawl-crawl
description: |
  Bulk-extract many pages from one site or section. Use for "crawl", "everything under /docs", or content spanning linked pages.
allowed-tools:
  - Bash(firecrawl *)
  - Bash(npx firecrawl-cli *)
---

# firecrawl crawl

Bulk extract content from a website. Crawls pages following links up to a depth/limit.

**Prerequisite:** `crawl` requires authentication (no keyless free tier); without credentials the CLI prompts an interactive login.

## Quick start

```bash
# Crawl a docs section
firecrawl crawl "<url>" --include-paths /docs --limit 50 --wait -o .firecrawl/crawl.json

# Full crawl with depth limit
firecrawl crawl "<url>" --max-depth 3 --wait --progress -o .firecrawl/crawl.json

# Check status of a running crawl
firecrawl crawl <job-id>
```

Run `firecrawl crawl --help` for the full option list.

**Done when:** the crawl reaches a terminal status and the saved output under `.firecrawl/` contains the expected pages.

## Tips

- Use `--wait` when you need the results immediately. It has no default timeout; use `--timeout <seconds>` to bound polling. Without `--wait`, crawl returns a job ID for async polling.
- **Scope crawls with `--include-paths`** whenever the request names a section — crawl only the pages you need.
- Crawl consumes credits per page. Check `firecrawl credit-usage` before large crawls (`credit-usage` requires authentication).

## See also

- [firecrawl-scrape](../firecrawl-scrape/SKILL.md) — scrape individual pages
- [firecrawl-map](../firecrawl-map/SKILL.md) — discover URLs before deciding to crawl
- [firecrawl-download](../firecrawl-download/SKILL.md) — download site to local files (uses map + scrape)
