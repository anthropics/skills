---
source: https://github.com/firecrawl/skills/tree/main/skills/core/firecrawl-search
name: firecrawl-search
description: |
  Web search with full page content. Use when no URL is known: finding sources, articles, or news. For papers use firecrawl-research-index; for library, API, error, or bug questions use firecrawl-developer-index.
allowed-tools:
  - Bash(firecrawl *)
  - Bash(npx firecrawl-cli *)
---

# firecrawl search

Web search with optional content scraping. Returns search results as JSON, optionally with full page content.

## Quick start

```bash
# Basic search
firecrawl search "your query" -o .firecrawl/result.json --json

# Search and scrape full page content from results
firecrawl search "your query" --scrape -o .firecrawl/scraped.json --json

# News from the past day
firecrawl search "your query" --sources news --tbs qdr:d -o .firecrawl/news.json --json
```

Run `firecrawl search --help` for the full option list.

`--categories developer` weighs the developer index beside ordinary web results in this same call (no passage control, no index filters). `--categories research` is a website filter, not the paper index. Dedicated skills: [firecrawl-developer-index](../firecrawl-developer-index/SKILL.md) and [firecrawl-research-index](../firecrawl-research-index/SKILL.md).

**Done when:** results are saved under `.firecrawl/`, verified non-empty, processed for the request, and one feedback event is sent within the time window (unless opted out).

## Tips

- **`--highlights` on by default:** results are query-relevant excerpts, not full-page snippets. Use `--no-highlights` for the original snippets.
- **`--scrape` fetches full content** — reuse that content instead of re-scraping result URLs. This saves credits and avoids redundant fetches.
- Always write results to `.firecrawl/` with `-o` to avoid context window bloat.
- Use `jq` to extract URLs or titles: `jq -r '.data.web[].url' .firecrawl/search.json`
- Naming convention: `.firecrawl/search-{query}.json` or `.firecrawl/search-{query}-scraped.json`

## Send feedback after every search (refunds 1 credit)

Search costs 2 credits. After you've actually used the results (or decided they were useless), send structured feedback with `firecrawl search-feedback <id>`. The first feedback per search refunds 1 credit and helps us improve search quality. **Do this once per search**, in the background, after you finish processing the results — it does not block your main task.

**Opt out:** if `FIRECRAWL_NO_SEARCH_FEEDBACK=1` (or `FIRECRAWL_DISABLE_SEARCH_FEEDBACK=1`) is set, the CLI silently skips the call and never sends anything. Respect that — do not try to work around it. (Team admins can also disable this server-side; the API will return `feedbackErrorCode: "TEAM_OPTED_OUT"` and the CLI will exit 0 silently.)

**Rules to know before you call this:**

- **Time window:** must be sent within ~2 minutes of the search. Late feedback is rejected.
- **`--missing-content` is the most important field.** It's a list of _specific pieces_ of content you expected but did not find. One topic per entry, each in its own string. These aggregate across teams and tell us what to index next.
- **Substantive content required** (zero-effort feedback is rejected with HTTP 400):
  - `good` → must include at least one `--valuable-sources` entry.
  - `partial` → must include `--valuable-sources` or `--missing-content`.
  - `bad` → must include `--missing-content` or `--query-suggestions`.
- **Daily refund cap (per team, per UTC day, default 100 credits).** Once your team has been refunded 100 credits today, further submissions still record feedback but no longer refund credits. The response includes `creditsRefundedToday` / `dailyRefundCap` / `dailyCapReached`. **When `dailyCapReached: true`, stop calling `search-feedback` for the rest of the UTC day** — it won't refund anything and you're wasting bandwidth.
- **Idempotent:** re-submitting for the same search id returns success but no extra refund.
- **`--silent &`** is the right pattern — exit code 0 even on failure, so a rejected/expired call never crashes your pipeline.

Verify the search returned results before reading its `id`. Zero-result searches write no output file, so the file may be missing — or left over from an earlier search. The guard below skips feedback when the file is missing or has zero results; call `search-feedback` only inside it:

```bash
# Send once per search. Rate honestly and replace the placeholder with the
# rating that matches what actually happened. The two fields shown
# satisfy the substantive-content rule for every rating.
if SEARCH_ID=$(jq -er 'select(any(.data[]; length > 0)) | .id' .firecrawl/search-react-hooks.json); then
  firecrawl search-feedback "$SEARCH_ID" \
    --rating "<good|partial|bad>" \
    --valuable-sources '[{"url":"https://react.dev/reference/react/hooks","reason":"Most authoritative"}]' \
    --missing-content '[{"topic":"useDeferredValue","description":"No example of useDeferredValue with Suspense"}]' \
    --silent &
fi
```

**`--missing-content` accepts:**

- JSON array of `{topic, description?}` objects (richest, preferred)
- `"topic: description"` strings (shorthand)
- Plain `"topic1, topic2, topic3"` (when you only have topic names)
- Repeated `--missing-content` flags

`--silent` suppresses output and `&` runs it in the background so feedback never blocks you.

## See also

- [firecrawl-scrape](../firecrawl-scrape/SKILL.md) — scrape a specific URL
- [firecrawl-map](../firecrawl-map/SKILL.md) — discover URLs within a site
- [firecrawl-crawl](../firecrawl-crawl/SKILL.md) — bulk extract from a site
- [firecrawl-developer-index](../firecrawl-developer-index/SKILL.md) — issues, merged PRs, READMEs, and docs
- [firecrawl-research-index](../firecrawl-research-index/SKILL.md) — published papers, not `search --categories research`
