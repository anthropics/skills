---
name: haruspex-stock-analyst
description: Fundamental and signals analysis for a single stock ticker, powered by Haruspex's multi-dimension scoring system. Use this skill whenever the user asks about a specific stock, mentions a company they're considering as an investment, asks "what do you think about [TICKER]?", asks for analysis or a deep dive on a stock, asks whether a stock looks good or bad, asks for the score or rating of a company, or wants to understand what's driving a stock's performance — even if they don't explicitly mention Haruspex. This is the default skill for any single-ticker stock question.
---

# Haruspex Stock Analyst

## What this skill does

Runs a structured single-ticker analysis using the Haruspex API via the
`@haruspex-guru/mcp-server` MCP server. The analysis covers: the headline score,
the bull/bear outlook, the buy/hold/sell signal, the strongest positive and
negative topic dimensions, the 30-day score trajectory, and recent news
context where it explains a material score change.

The output is **analysis**, never advice. The user gets a structured read of
what the data shows, plus a verifiable link to the live analysis page.

## When to use this skill

Trigger on any of these patterns:

- "What do you think about [TICKER]?"
- "Should I look at [COMPANY]?" / "Is [COMPANY] interesting?"
- "Score for NVDA?" / "Rating on AAPL?"
- "Analyze TSLA" / "Deep dive on MSFT"
- "What's driving [TICKER]?"
- A user mentions a single company by name in the context of investing.

Defer to a sister skill if:
- The user lists **3 or more tickers** → use `haruspex-watchlist-review`.
- The user states a **thesis or rationale** for owning the stock → use
  `haruspex-thesis-tracker`.
- The user is **writing in Japanese** → use `haruspex-stock-analyst-ja`.

## Prerequisites

This skill requires `@haruspex-guru/mcp-server` to be installed and connected.
**First action: verify the MCP tools are available.**

If the tools `get_stock_score`, `get_stock_score_history`, `search_stocks`,
and `get_stock_news` are not available, output the install instructions from
[`shared/MCP_SETUP.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md) and **stop**. Do not
attempt analysis without live data.

## Workflow

1. **Disambiguate the ticker.** If the user gave a company name, an
   ambiguous symbol, or a name that could match multiple listings, call
   `search_stocks(query)` first and confirm the intended symbol with the
   user before proceeding. If the user gave an unambiguous US ticker like
   `NVDA`, skip this step.
2. **Fetch the current score.** Call `get_stock_score(symbol)`. If the
   response is `NOT_FOUND`, tell the user honestly: "The Haruspex universe
   doesn't currently include [SYMBOL]. The analysis universe is primarily
   US large-caps." Do not fabricate a score. Stop.
3. **Fetch the trajectory.** Call `get_stock_score_history(symbol, days=30)`
   and identify: trend direction, any inflection points, the high/low score
   in the window.
4. **Fetch news context — only if warranted.** Call `get_stock_news(symbol)`
   if any of the following are true:
   - The headline `change` field is ≥ |10|.
   - The user asked "what's driving this?" or similar.
   - A topic dimension shifted by ≥ |10|.
   Otherwise skip news to avoid noise.
5. **Synthesize and output** in the format below.

## Output format

Use this exact markdown structure. Replace bracketed values with real
captured data — never fabricate.

```markdown
## [SYMBOL] — Haruspex Analysis

**Score:** [N]/100 ([outlook]) · **Signal:** [signal] · **Change:** [+/-N]

**Strongest positive dimensions:**
- [dim1]: [N]/100 ([change]) — [one-line explanation in plain English]
- [dim2]: [N]/100 ([change]) — [one-line explanation]
- [dim3]: [N]/100 ([change]) — [one-line explanation]

**Watch dimensions (lowest or worsening):**
- [dim]: [N]/100 ([change]) — [one-line explanation]
- [dim]: [N]/100 ([change]) — [one-line explanation]

**30-day trajectory:**
[1-2 sentences describing the trend, e.g. "Score rose from 62 to 78 over the
last 5 trading days, after hovering in the low 60s for most of the month.
The recent move is driven by the macro and competitors dimensions."]

**News context (if fetched):**
- [headline] — [source], [relative date]
- [headline] — [source], [relative date]

**Verify:** [shareUrl]

> **Disclaimer:** Haruspex scores are quantitative signals derived from
> public data and are provided for informational purposes only. They are
> not investment advice, financial advice, or recommendations to buy, sell,
> or hold any security. Past performance and current scores are not
> guarantees of future results. Always do your own research and consider
> consulting a licensed financial advisor before making investment
> decisions. Data via haruspex.guru.
```

### Picking dimensions to surface

- **Positive set:** the 3 dimensions with the highest current score, breaking
  ties by largest positive `change`.
- **Watch set:** any dimension currently below 50, OR with `change` ≤ -5.
  Cap at 3.
- **Skip dimensions where `score` is exactly `0`** — that's typically
  "data unavailable", not a real low score. Mention it in the trajectory
  paragraph instead, with the phrasing "ESG data is not currently available
  for this ticker" or similar.
- For each surfaced dimension, write a one-line plain-English gloss. See
  [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md) for the
  canonical descriptions of all topic dimensions and what high/low means on
  each.

## Compliance rules (NEVER VIOLATE)

- **Do not give buy / sell / hold recommendations directed at the user.**
  Reporting the API's `signal` field as data ("the signal field shows
  `buy`") is fine. Telling the user "you should buy NVDA" is forbidden.
- **Do not predict price movements.** "The score is rising" is fine. "The
  price will rise" is forbidden.
- **Do not provide position sizing, stop-loss, take-profit, or
  risk-management specifics.** Refer the user to a licensed advisor.
- **If the user asks "should I buy this?"**, redirect: "I can show you the
  analysis, but I can't tell you whether to buy. Here's what the data
  shows..." — then run the workflow.
- **Acknowledge data limitations honestly.** If history is sparse, news is
  empty, or a dimension scored 0 (data unavailable), call it out.
- **Always include the share URL** so the user can verify against the live
  Haruspex page.
- **Always include the disclaimer footer** in the exact wording from
  [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md).
- **Never fabricate** a score, a ticker, a dimension value, a share URL, or
  a news article. Real data or no analysis.
- **Never claim or imply** that the Haruspex score is a guarantee of future
  performance.

## Reference material

- [`reference.md`](reference.md) — edge cases, output format variations,
  how to handle sparse data.
- [`examples.md`](examples.md) — full example dialogues with real captured
  data.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md) — canonical
  multi-dimension glossary.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md) — canonical
  disclaimer footer wording.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md) — how to install
  the MCP server.
