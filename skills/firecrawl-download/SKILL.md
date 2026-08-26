---
source: https://github.com/firecrawl/skills/tree/main/skills/core/firecrawl-download
name: firecrawl-download
description: |
  Save a site or section as local files (markdown, screenshots). Use for "download the site", offline docs, or a local copy for reference.
allowed-tools:
  - Bash(firecrawl *)
  - Bash(npx firecrawl-cli *)
---

# firecrawl download (invoked as `firecrawl x download`)

> **Experimental.** `download` is available under the `firecrawl x` command group.

**Prerequisite:** `download` requires authentication (no keyless free tier); without credentials the CLI prompts an interactive login.

Maps the site origin first to discover pages, then scrapes each one into nested directories under `.firecrawl/`. Use `--include-paths` to scope a non-root URL to one section. Automated runs always pass `-y` — without it the command opens an interactive wizard that blocks on a prompt.

## Quick start

```bash
# With screenshots
firecrawl x download https://docs.example.com --screenshot --limit 20 -y

# Multiple formats (each saved as its own file per page)
firecrawl x download https://docs.example.com --format markdown,links --screenshot --limit 20 -y
# Creates per page: index.md + links.txt + screenshot.png

# Filter to specific sections
firecrawl x download https://docs.example.com --include-paths "/features,/sdks" -y

# Skip translations
firecrawl x download https://docs.example.com --exclude-paths "/zh,/ja,/fr,/es,/pt-BR" -y
```

Run `firecrawl x download --help` for the full option list, including which scrape options download supports.

**Done when:** the command exits successfully and the expected files exist under `.firecrawl/`.

## See also

- [firecrawl-map](../firecrawl-map/SKILL.md) — just discover URLs without downloading
- [firecrawl-scrape](../firecrawl-scrape/SKILL.md) — scrape individual pages
- [firecrawl-crawl](../firecrawl-crawl/SKILL.md) — bulk extract as JSON (not local files)
