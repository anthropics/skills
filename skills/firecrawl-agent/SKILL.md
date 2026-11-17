---
source: https://github.com/firecrawl/skills/tree/main/skills/core/firecrawl-agent
name: firecrawl-agent
description: |
  Autonomous multi-page extraction into structured JSON. Use when the user wants website data matching a schema — pricing tiers, product listings — beyond a single-page scrape.
allowed-tools:
  - Bash(firecrawl *)
  - Bash(npx firecrawl-cli *)
---

# firecrawl agent

AI-powered autonomous extraction. The agent navigates sites and extracts structured data (takes 2-5 minutes).

## Quick start

```bash
# Extract structured data
firecrawl agent "extract all pricing tiers" --wait --json -o .firecrawl/pricing.json

# With a JSON schema for structured output
firecrawl agent "extract products" --schema '{"type":"object","properties":{"name":{"type":"string"},"price":{"type":"number"}}}' --wait --json -o .firecrawl/products.json

# Focus on specific pages
firecrawl agent "get feature list" --urls "<url>" --wait --json -o .firecrawl/features.json
```

Run `firecrawl agent --help` for the full option list.

**Done when:** the output file contains valid JSON answering the request — or a job ID was intentionally returned for later polling.

## Job IDs

Omitting `--wait` returns a job ID. A UUID positional argument is auto-detected as a status check:

```bash
# Check once (equivalent to adding --status)
firecrawl agent "<job-id>"

# Wait on an existing job, polling every 10 seconds for up to 5 minutes
firecrawl agent "<job-id>" --wait --poll-interval 10 --timeout 300

# Cancel an active job
firecrawl agent "<job-id>" --cancel
```

## Tips

- Use `--wait` for inline results; omit it only when you want a job ID to poll later (see [Job IDs](#job-ids)).
- Use `--schema` for predictable, structured output — otherwise the agent returns freeform data.
- Agent runs consume more credits than simple scrapes. Use `--max-credits` to cap spending.
- For simple single-page extraction, prefer `scrape` — it's faster and cheaper.

## See also

- [firecrawl-scrape](../firecrawl-scrape/SKILL.md) — simpler single-page extraction
- [firecrawl-interact](../firecrawl-interact/SKILL.md) — scrape + interact for manual page interaction (more control)
- [firecrawl-crawl](../firecrawl-crawl/SKILL.md) — bulk extraction without AI
