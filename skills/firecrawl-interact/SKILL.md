---
source: https://github.com/firecrawl/skills/tree/main/skills/core/firecrawl-interact
name: firecrawl-interact
description: |
  Drive a live browser on a scraped page: click, fill forms, log in, paginate, infinite-scroll. Use when content requires interaction or a scrape failed or returned incomplete content.
allowed-tools:
  - Bash(firecrawl *)
  - Bash(npx firecrawl-cli *)
---

# firecrawl interact

Interact with scraped pages in a live browser session. Scrape a page first, then use natural language prompts or code to click, fill forms, navigate, and extract data. For web searches, use `search` — interact is for acting on a specific page.

## Quick start

```bash
# 1. Scrape a page (scrape ID is saved automatically)
firecrawl scrape "<url>"

# 2. Interact with the page using a positional prompt
firecrawl interact "Click the login button"
firecrawl interact "Fill in the email field with test@example.com"
firecrawl interact "Extract the pricing table"

# A UUID first argument is auto-detected as the scrape ID
firecrawl interact "<scrape-id>" "Extract the pricing table"

# 3. Or use code for precise control
firecrawl interact --code "agent-browser click @e5" --bash
firecrawl interact --code "agent-browser snapshot -i" --bash

# 4. Stop the session when done
firecrawl interact stop
```

Run `firecrawl interact --help` for the full option list.

**Done when:** the requested content or action result is captured and the session is stopped with `firecrawl interact stop`.

## Profiles

Use `--profile` on the scrape to persist browser state (cookies, localStorage) across scrapes:

```bash
# Session 1: Login and save state
firecrawl scrape "https://app.example.com/login" --profile my-app
firecrawl interact --prompt "Fill in email with user@example.com and click login"

# Session 2: Come back authenticated
firecrawl scrape "https://app.example.com/dashboard" --profile my-app
firecrawl interact --prompt "Extract the dashboard data"
```

Read-only reconnect (no writes to profile state):

```bash
firecrawl scrape "https://app.example.com" --profile my-app --no-save-changes
```

## Tips

- Always scrape first — `interact` requires a scrape ID from a previous `firecrawl scrape` call
- The scrape ID is saved automatically, so you can omit `--scrape-id` for subsequent interact calls. Saved sessions may expire after about 10 minutes; re-scrape if the CLI warns that the session is stale
- Use `firecrawl interact stop` to free resources when done
- For parallel work, scrape multiple pages and interact with each using `--scrape-id`

## See also

- [firecrawl-scrape](../firecrawl-scrape/SKILL.md) — try scrape first, escalate to interact only when needed
- [firecrawl-search](../firecrawl-search/SKILL.md) — use `search` for web searches
- [firecrawl-agent](../firecrawl-agent/SKILL.md) — AI-powered extraction (less manual control)
