# Firecrawl MCP — setup and Phase 0 crawl procedure

This skill uses the Firecrawl MCP server to crawl documentation websites. Read this file when the user provides an `https://` URL as input, or when Firecrawl tools are unavailable and you need to tell the user how to install them.

Firecrawl handles JS-rendered sites (Docusaurus, Mintlify, Nextra, hosted GitBook), robots.txt compliance, rate limiting, and HTML-to-markdown conversion automatically. No custom crawl logic is needed.

## Setup (one-time, user-facing)

If the Firecrawl tools (e.g. `mcp__firecrawl__firecrawl_map`) are not available, stop and tell the user:

> This skill needs the Firecrawl MCP server for URL inputs. One-time setup:
>
> 1. Get a Firecrawl API key at [firecrawl.dev](https://firecrawl.dev) (free tier: 500 credits — about 9 full course crawls)
> 2. Add the MCP server to Claude Code:
>
>    ```bash
>    claude mcp add firecrawl -e FIRECRAWL_API_KEY=fc-your-key-here -- npx -y firecrawl-mcp
>    ```
>
>    Or add to `~/.claude/settings.json` manually:
>
>    ```json
>    {
>      "mcpServers": {
>        "firecrawl": {
>          "command": "npx",
>          "args": ["-y", "firecrawl-mcp"],
>          "env": {
>            "FIRECRAWL_API_KEY": "fc-your-key-here"
>          }
>        }
>      }
>    }
>    ```
>
> Restart Claude Code and confirm `mcp__firecrawl__firecrawl_map` appears in available tools. Local files and GitHub repos work without Firecrawl.

## Phase 0: Web crawl procedure

### 0A: Map the site

Use `firecrawl_map` to discover all URLs at the documentation domain:

```
Tool: mcp__firecrawl__firecrawl_map
Arguments: { "url": "<the URL the user provided>" }
```

`firecrawl_map` returns a list of all URLs Firecrawl can see on the site. It respects robots.txt automatically — if a path is disallowed, those URLs will not appear in the results.

If the map returns zero URLs or only the root URL, the site is likely behind authentication or heavily bot-protected. Tell the user:

> "Firecrawl couldn't index this site — it may require a login or block automated access. Try downloading the docs locally or finding the source repository."

### 0B: Filter URLs to documentation pages

From the map results, filter down to documentation-relevant URLs before spending fetch credits. Apply this logic mentally (no code to run — you're reading the URL list):

**Exclude patterns** — drop any URL matching:
- `/blog/`, `/changelog/`, `/release-notes/`, `/news/`
- `/legal/`, `/privacy/`, `/terms/`, `/license/`
- `/tag/`, `/category/`, `/author/`
- File extensions: `.pdf`, `.zip`, `.png`, `.jpg`, `.svg`, `.css`, `.js`

**Prioritize** shorter paths first — top-level section pages (e.g., `/docs/guide/`) before deep sub-pages (e.g., `/docs/guide/advanced/edge-cases/`).

**Cap at 50 URLs.** If the filtered list exceeds 50, take the 50 with the shortest paths (broadest coverage). If the user's URL already points to a specific sub-section (e.g., `https://docs.example.com/api/`), keep only URLs within that prefix.

Tell the user the filtered count before fetching:

> "Found 73 pages — scoping to 50 most relevant for the documentation section. Fetching now..."

### 0C: Fetch all pages as clean markdown

Use `firecrawl_batch_scrape` to fetch all filtered URLs in one call:

```
Tool: mcp__firecrawl__firecrawl_batch_scrape
Arguments: {
  "urls": ["<url1>", "<url2>", ...],   // the filtered list from 0B
  "options": {
    "formats": ["markdown"],
    "onlyMainContent": true
  }
}
```

`onlyMainContent: true` tells Firecrawl to strip navigation, footers, sidebars, and cookie banners — returning only the page body as clean markdown. This is the key advantage over a plain HTTP fetch.

Each result in the response includes:
- `url` — the source URL (use this in spec citation references)
- `markdown` — the clean page content

If a batch exceeds Firecrawl's credit limit mid-run, it will return partial results. Proceed with what was returned and note what was skipped.

### 0D: Hand off to Phase 1

Read the markdown content from the batch scrape results. Phase 1 proceeds identically to the local-files case — treat each page's `markdown` field as a document to analyze.

Tell the user:

> "Crawled N pages from [domain]. Proceeding to analysis."

**Always record the source `url` for each page** so spec translation blocks can cite the exact page URL rather than a generic domain reference.

## Credit usage reference

| Operation | Firecrawl credits |
|---|---|
| `firecrawl_map` (site discovery) | 1 credit |
| `firecrawl_batch_scrape` per page | 1 credit per URL |
| 50-page course crawl (typical) | ~51 credits |
| Free tier | 500 credits |

A free account covers roughly 9 full course crawls at 50 pages each. Credits reset monthly on paid plans.
