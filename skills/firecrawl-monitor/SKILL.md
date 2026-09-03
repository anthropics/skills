---
source: https://github.com/firecrawl/skills/tree/main/skills/core/firecrawl-monitor
name: firecrawl-monitor
description: |
  Alert by webhook/email on web changes — use for "monitor/watch/track/alert me when": recurring checks on known URLs (prefer over repeated one-off scrapes) or web-wide watches for new results (queries + goal).
allowed-tools:
  - Bash(firecrawl *)
  - Bash(npx firecrawl-cli *)
---

# firecrawl monitor

Detect when content on a website changes and get notified by webhook or email. Firecrawl handles fetching, diffing, judging, and notifying server-side. Each page in a check is labeled `same`, `new`, `changed`, `removed`, or `error`.

**Pick a target mode** by what you're watching:

| Mode        | Flags                          | Watches                                                |
| ----------- | ------------------------------ | ------------------------------------------------------ |
| Single page | `--page <url>`                 | one URL, for changes                                   |
| URL batch   | `--scrape-urls <url,url,...>`  | several URLs, for changes                              |
| Whole site  | `--crawl-url <root-url>`       | every page a crawl discovers, for changes              |
| Web search  | `--queries <q,...>` + `--goal` | the **whole web**, for _new_ results matching the goal |

The first three watch URLs you already have. **Web search** runs your queries each check and alerts on results it hasn't seen before (labeled `new` once, `same` on later checks); `--goal` is required with `--queries`.

## Quick start

```bash
# Single page, natural-language schedule, email alert
firecrawl monitor create --name "Blog" --schedule "every 30 minutes" \
  --goal "Alert when a new blog post is published." \
  --page https://example.com/blog \
  --email alerts@example.com

# Web monitor — search the whole web for NEW results matching a goal
firecrawl monitor create --name "Competitor launches" --schedule "daily at 9:00" \
  --queries "competitor product launch,competitor funding round" \
  --goal "Alert when a competitor announces a new product or raises funding." \
  --search-window 7d --max-results 20 \
  --email alerts@example.com

# Webhook notifications
firecrawl monitor create --name "Docs webhook" --schedule "every 30 minutes" \
  --goal "Alert when docs content changes." \
  --page https://example.com/docs \
  --webhook-url https://example.com/hook \
  --webhook-events monitor.page,monitor.check.completed

# Manage and inspect
firecrawl monitor list --limit 20
firecrawl monitor get <monitorId>
firecrawl monitor run <monitorId>             # trigger a check now
firecrawl monitor checks <monitorId>          # list all checks
firecrawl monitor check <monitorId> <checkId> --page-status changed
firecrawl monitor update <monitorId> --state paused
firecrawl monitor delete <monitorId>
```

Subcommands: `create | list | get | update | delete | run | checks | check`. Run `firecrawl monitor <subcommand> --help` for the full option list.

**Done when:** `create` returns a monitor ID and a smoke-test `run` + `check` confirms the expected target, state, and notification configuration.

Read [goals.md](goals.md) when writing or refining `--goal` (and `--queries` for web monitors). Read [json-tracking.md](json-tracking.md) when the user cares about specific structured fields (price, headline, stock flag) and wants per-field diffs.

## Constraints & tips

- Minimum schedule interval is **5 minutes**. Monitoring is **not available for zero-data-retention teams**.
- **Prefer one monitor over repeated one-off scrapes** whenever the user wants the same URL checked more than once.
- **Silence temporarily with `update --state paused`**; reserve `delete` for monitors that are permanently done. (`--state` is an update flag; `--status` is the global CLI status flag.)
- **Filter check pages with `--page-status changed`** (or `new`, `removed`, `error`) to skip the noise from `same` pages.
- **`firecrawl monitor run <id>`** triggers a check immediately — useful for smoke-testing a monitor right after creating it.
- **`--retention-days`** controls how long snapshots are kept for diffing. Lower it for high-frequency monitors to save storage.
- **External email recipients must opt in.** First time they're added, Firecrawl sends a confirmation email and they only receive alerts after they confirm. Team-owned addresses are auto-confirmed. Once a recipient unsubscribes, they must be re-added by the owner for a fresh confirmation email.
- **On HTTP 429 / rate-limit errors, back off once**: wait ~30s and retry once. If it persists, stop, report the rate limit as the blocking reason, and delete any monitors created for this task. Never retry in a loop.
- **Monitor-triggered scrapes default `maxAge` to `0`** — every check performs a fresh scrape unless `scrapeOptions.maxAge` is set explicitly in a JSON payload.

## See also

- [firecrawl-scrape](../firecrawl-scrape/SKILL.md) — one-off scrape; escalate to `monitor` when checks become recurring
- [firecrawl-crawl](../firecrawl-crawl/SKILL.md) — one-off crawl; pair with `--crawl-url` here for recurring crawl diffs
- [firecrawl](../firecrawl/SKILL.md) — top-level workflow guide
