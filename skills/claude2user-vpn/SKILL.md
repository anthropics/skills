---
name: claude2user-vpn
description: Fetch public web pages from the user's machine with browser-equivalent HTTP headers, so requests for public news/finance/reference content succeed when the agent's default fetch tool returns errors. Use when WebFetch returns "Unable to fetch", 4xx, or empty content for a public URL that the user could open in their own browser. Triggers on words like "won't fetch", "fetch failed", "fetch error", or after any WebFetch failure on a public news/finance/data site.
license: MIT — see LICENSE.txt
---

# claude2user-vpn

A `curl`-based fetch helper that runs on the user's machine and sends the same headers a desktop browser would. Useful when the agent's default fetch tool fails on a public page that the user can open normally — usually because the default tool's HTTP signature doesn't match what the site expects from a desktop browser.

## When to use this skill

- `WebFetch` (or the agent's default fetch path) returned an error or empty content
- The URL is public (no login required) and the user could open it in their own browser
- You need the raw HTML so you can extract structured content with `python3` + BeautifulSoup, `pup`, `jq`, etc.

## When NOT to use this skill

- The URL is behind a login / paywall the user hasn't authenticated to.
- You need automated, high-volume scraping. This is a one-shot helper, not a scraping framework.
- The page renders its data via JavaScript after load (no useful content in initial HTML). Open it in a real browser instead.

## Workflow

### Step 1 — try the default fetch tool first

The default `WebFetch` is the right first choice: it summarizes via an LLM and handles redirects/encoding for you. Only fall through to this skill when it returns an error or obviously incomplete content.

### Step 2 — fetch with browser-equivalent headers

```bash
${CLAUDE_PLUGIN_ROOT}/scripts/fetch_as_user.sh "<url>" [output_path]
```

Writes the raw HTML to a temp file (or the path you specify) and prints the path on success. Parse it with whatever extraction tooling fits.

The wrapper sets the same headers a desktop Safari sends: User-Agent, Accept, Accept-Language, gzip/brotli encoding, `sec-ch-ua`/`sec-fetch-*`, and `Upgrade-Insecure-Requests`. 20-second timeout, no retry.

### Step 3 — if it still doesn't work

| Response | What it means | What to do |
|---|---|---|
| 401 / 403 | Site needs authentication | Ask the user whether they have an account; if so, see *Authenticated content* below. Otherwise treat the content as unavailable. |
| 503 / 000 / a "Just a moment…" HTML stub | Page requires JavaScript execution that `curl` can't provide | Open it in a real browser instead. |
| Empty HTML body or skeleton | Page renders content via JS after load | Same — open in a real browser, or look for an underlying JSON API the user can hit instead. |

## Authenticated content

For sites where the user has an account (Reuters subscription, Bloomberg terminal, paid newsletters, etc.), the supported pattern is cookies:

1. Ask the user to export cookies for the target site via Safari/Chrome devtools or a "Get cookies.txt" browser extension.
2. The user saves the file under `~/.claude/secrets/cookies/<site>.txt` in Netscape format.
3. Modify the curl call (or wrap it) to add `-b ~/.claude/secrets/cookies/<site>.txt`.

Cookie files contain session credentials — treat them like API keys. Never commit them to git.

## Site behavior reference

`references/site_gating.md` documents typical response patterns for common news / finance / reference sites as of the last sweep. Sites change behavior frequently; re-test with `scripts/site_test.sh <url1> <url2> ...` before relying on the snapshot for a critical workflow.

## Important notes

- **The user's machine, the user's IP.** This is the entire architectural point: the fetch is the same request the user would make from their own browser. Do not route through a VPN/proxy unless the user explicitly asks.
- **Respect rate limits.** The wrapper has no throttling. If polling, add a few seconds between calls. Behave like a person reading, not a scraper.
- **Cite sources.** Whatever you fetch, include the URL + retrieval date in the work product.
- **Respect robots.txt and ToS.** The wrapper doesn't check either. If the user's intended use of a source is against the site's terms, this skill doesn't fix that.

## Files

- `scripts/fetch_as_user.sh` — one-shot `curl` wrapper with browser-equivalent headers
- `scripts/site_test.sh` — sweep a URL list and report response codes per method
- `references/site_gating.md` — known site response patterns with last-tested dates
