---
source: https://github.com/firecrawl/skills/tree/main/skills/core/firecrawl-developer-index
name: firecrawl-developer-index
description: Search issues, merged pull requests, READMEs, and documentation. Use when the question is how a library or API behaves, what an error means, or whether a bug was fixed; prefer this over a general web page.
---

# Firecrawl Developer Index

Answer a developer question from the primary source: the issue where the bug was reported, the merged pull request that fixed it, the README or documentation page that states the contract. A blog post that describes a behaviour is a weaker answer than the passage that defines it, so reach for the index first and the open web second.

There is **no fixed recipe**. Read the question, decide what kind it is, and choose the approach below. A literal error string wants a different move than "how do I do X". Don't run machinery a question doesn't call for.

## The tools, and what each is uniquely good at

- HTTP: **`GET|POST https://api.firecrawl.dev/v2/search/developer`**
  MCP: **`firecrawl_developer_search(query, k?, skills?)`**
  CLI: **`firecrawl developer <query> [--limit <n>]`**
  Ranked results over the whole index. Each carries `id` (`issue:owner/repo#123`), `url`, and the **matched passages in markdown**, so tables and code blocks survive. The artifact kind is the `id` prefix: `doc:`, `issue:`, `pull_request:`, or `readme:`.
  The default first move for a developer question. It is the only surface that returns the passages, which is what lets you answer instead of pointing at a page.
  `k` / `--limit` is 1–100 and defaults to 10. `skills="only"` (HTTP/MCP only) restricts the search to agent-skill files.
  Keyless; send `Authorization: Bearer $FIRECRAWL_API_KEY` for higher rate limits.

- MCP: **`firecrawl_search(query, categories: ["developer"])`**
  CLI: **`firecrawl search <query> --categories developer`**
  Developer hits in a `developer` group beside `web`, each with `url`, `title`, `description` (the matched passage), `position`, and `category: "developer"` — web results carry no `category`, so that is the field to key on when merging.
  Use this when you are **already** running a web search and want developer sources weighed in the same call. It exposes none of the filters and no passage control.

- MCP: **`firecrawl_scrape(url)` / `firecrawl_search(query)`**
  CLI: **`firecrawl scrape <url>` / `firecrawl search <query>`**
  General web fetch and search, for what no primary source states: a comparison between two libraries, an outage, a migration write-up, a project with no public repository or indexed docs.
  Also the follow-through when a hit is the right page but you need all of it — `scrape` the result's `url`.

## Filters, and what each one costs you

Only the HTTP surface takes these. On `GET`, pass `types=issue,pull_request` or repeat the parameter; on `POST`, pass arrays. All are optional.

- `types` — which of `doc`, `issue`, `pull_request`, `readme` to search. Defaults to all four. Narrowing here is the cheapest way to sharpen a query.
- `repos` (`owner/name`) scopes the repository half, meaning `issue`, `pull_request`, and `readme`; `sources` (documentation source ids, at most 20) scopes the documentation half, meaning `doc`. Passing both **unions** the halves rather than intersecting them. Both echo back in the response with `indexed: true|false` — that is how you tell "not in the index" from "found nothing".
- A filter that cannot match any requested `type` is a `400`, not an empty list: `repos` with no repository type in `types`, or `sources` without `doc`.
- `passages` (1–5, default 1) is the _maximum_ passages per result, not a guarantee. Raise it when one page is clearly the right page but the first passage is the wrong part of it.
- `language`, `topic`, `license`, `min_stars`, `max_stars`, `archived`, `fork` describe a **repository**. Most documentation pages in the index have no repository behind them, so no repository fact can admit or exclude one. Send any of these without a `sources` scope and the response holds repository evidence only — `issue`, `pull_request`, `readme`. That is the design, not an index fault: do not retry it and do not report the index broken. To keep documentation, drop the repository filters, or scope the documentation half with `sources` and read the `sources` echo to confirm the id is indexed.

## Match the approach to the question

- **Literal error message or stack-trace string** → search the string itself plus the library name, with `types=["issue","pull_request"]`. Whoever hit it filed it. If nothing matches, strip the volatile parts (paths, line numbers, ids, addresses) and retry — the invariant middle of the message is what is indexed.
- **Conceptual "how do I do X"** → the full question in natural language, all four types. The answer is usually a `doc` or a `readme`; raise `passages` before raising `k`.
- **Known bug** → the issue reports it, the merged pull request _fixes_ it, and the fix is what you want. Search `types=["issue","pull_request"]`, then re-query the issue's own terms scoped to its repo with `types=["pull_request"]`. A merged PR's passages tell you what changed and in which direction.
- **API contract** ("what does X return", "is Y required", "what is the default") → `readme` and `doc` are authoritative and a blog post is not. Use `types=["readme","doc"]`. If the contract looks like it moved, follow up with `pull_request` for the change that moved it.
- **Version-specific behaviour** → an issue's opening report describes the broken version; its resolution supersedes it. Raise `passages` to see further into the thread, and read the resolution and the linked pull request before answering. Never answer from an opening report alone.
- **Scoped to one library** → `repos=["owner/name"]` when you know the slug, plus `sources` if you want its docs in the same call. If a scoped search comes back empty, read the echoed `indexed` flag first: `false` means nothing from that repo or source can ever match and no rephrasing will help — drop the scope and search the whole index, or go to the web.
- **Ecosystem-wide** ("which libraries do X", "who else hit this") → no scope. Use `language` / `topic` / `min_stars` to keep to maintained repositories, accepting that this gives up all `doc` results.
- **Agent skills and tooling conventions** → `skills="only"` (HTTP/MCP only).
- **Comparison, opinion, news, or an unindexed project** → the open web. `firecrawl_search`, then `firecrawl_scrape` whatever deserves a full read. Combining is often right: take the contract from the index and the trade-off from the web.

## Principles

- **Quote the passage, cite the `url`.** The passages are the evidence; hand them over rather than paraphrasing them into a claim the reader can't check. `title` is frequently absent on `doc` results — fall back to `url`.
- **A merge supersedes a report.** When an issue and a pull request disagree, the merged pull request is the current behaviour. Say which one you read.
- **Scope last, not first.** Search the whole index, then narrow with `types`, `repos`, or `sources` once you know what the hits look like. Scoping first hides the result that would have told you where to look.
- **Go to the web when the index has nothing to say.** Trade-offs, ecosystem opinion, and anything about an unindexed project are web questions. Don't force them through the index, and don't dress a general web page up as a primary source.
