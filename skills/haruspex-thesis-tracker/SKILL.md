---
name: haruspex-thesis-tracker
description: Evaluates whether a user's stated investment thesis on a stock still holds, by mapping the thesis to the relevant Haruspex dimensions and reporting whether they trend supportively. Use this skill whenever the user states a reason for owning or considering a stock ("I'm long NVDA because of AI demand", "I'm bullish on TSLA on FSD"), asks "is my thesis still intact?", asks whether the data supports a particular view, mentions a position with a rationale, or wants to pressure-test an investment idea against current data — even if they don't use the word "thesis". Use this when the question is about a specific argument for owning a stock, not generic analysis.
---

# Haruspex Thesis Tracker

## What this skill does

Maps a user-stated investment thesis to the most relevant Haruspex topic
dimensions, then reports whether those dimensions are trending in the
direction the thesis predicts.

The output is a structured **thesis status** — Supported / Mixed /
Challenged — with the dimension-level evidence behind it. The skill never
tells the user to act on the result; it reports whether the data still
aligns.

## When to use this skill

Trigger on any of these patterns:

- "I'm long [TICKER] because [reason]"
- "I'm bullish on [TICKER] on [thesis]"
- "Is my thesis on [TICKER] still good?"
- "Does the data support [view]?"
- "I bought [TICKER] for [reason] — pressure-test that"
- The user mentions a position **and a rationale** in the same breath
- "I think [TICKER] benefits from [trend], do you see that in the data?"

Defer to a sister skill if:
- The user asks generic analysis without a thesis → use
  `haruspex-stock-analyst`.
- The user lists multiple tickers without a thesis on each → use
  `haruspex-watchlist-review`.
- The user is writing in Japanese → use `haruspex-stock-analyst-ja`.

## Prerequisites

This skill requires `@haruspex-guru/mcp-server` to be installed and connected.
**First action: verify the MCP tools are available.**

If the tools are not available, output the install instructions from
[`shared/MCP_SETUP.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md) and **stop**.

## Workflow

1. **Confirm ticker and thesis.** If either is missing, ask. Never invent
   a thesis. ("I'm long NVDA" without a reason — ask "what's your reason
   for being long?")
2. **Map thesis to dimensions.** Use the table in
   [`reference.md`](reference.md) as a starting point. Most theses map to
   2–4 dimensions. Be explicit about the mapping in the output.
3. **Fetch current state.** Call `get_stock_score(symbol)`.
4. **Fetch trajectory.** Call `get_stock_score_history(symbol, days=90)`.
   90 days is the default thesis-evaluation window — short enough to be
   actionable, long enough to filter noise.
5. **Optionally fetch news.** Call `get_stock_news(symbol)` only if the
   thesis-relevant dimensions show large recent moves and the news might
   explain it.
6. **Evaluate each thesis-relevant dimension:** is its current score in the
   range the thesis predicts? Has it trended in the predicted direction?
7. **Assign thesis status:**
   - **Supported** — all (or all but one minor) thesis-relevant dimensions
     trend in the predicted direction.
   - **Mixed** — some dimensions support, others contradict.
   - **Challenged** — most thesis-relevant dimensions trend against the
     thesis, or the headline score is moving sharply against it.
8. **Output** in the format below.

## Output format

```markdown
## Thesis Status: [Supported / Mixed / Challenged]

**Ticker:** [SYMBOL]
**Stated thesis:** [restate user's thesis in one short sentence]
**Headline score:** [N]/100 ([outlook]), change [+/-N], signal [signal]

### Thesis → dimension mapping
| Dimension | Predicted by thesis | Current | Δ | Read |
|-----------|---------------------|--------:|--:|------|
| [dim_a]   | [should be high / rising] | N | +N | [supports / mixed / against] |
| [dim_b]   | [should be high]   | N | -N | [supports / mixed / against] |
| [dim_c]   | [should be rising] | N | +N | [supports / mixed / against] |

### Evidence summary
[2–4 sentences. Plain English. Which dimensions back the thesis, which push
against it, and how much the headline score has moved over the 90-day window.
Reference specific dimension changes. Do not predict price.]

### News context (if fetched)
- [headline] — [source]
- [headline] — [source]

**Verify:** [shareUrl]

> **Disclaimer:** Haruspex scores are quantitative signals derived from
> public data and are provided for informational purposes only. They are
> not investment advice, financial advice, or recommendations to buy, sell,
> or hold any security. Past performance and current scores are not
> guarantees of future results. Always do your own research and consider
> consulting a licensed financial advisor before making investment
> decisions. Data via haruspex.guru.
```

### Picking the status

- All thesis dimensions read **supports** → **Supported**.
- 1 dimension reads **against** the rest **supports** → still **Supported**,
  but call out the one that doesn't.
- ≥ 2 dimensions read **against**, or any dimension shows a sharp negative
  change ≥ |10| → **Mixed**.
- Majority of thesis dimensions read **against**, or headline score has
  fallen sharply over the 90-day window → **Challenged**.

## Compliance rules (NEVER VIOLATE)

- **Never tell the user to buy, sell, hold, add to, or close a position.**
  The status field reports alignment, not action. Even on **Challenged**
  status: "the data no longer supports the thesis as stated" is fine; "you
  should sell" is forbidden.
- **Never predict price movements** based on thesis status. Score trajectory
  is observed; price is not predicted.
- **Never invent a thesis.** If the user states a position without a reason,
  ask before evaluating. A thesis-tracker without a thesis is just an
  analyst.
- **Acknowledge mapping uncertainty.** The thesis-to-dimensions map is a
  prior, not a proof. If a thesis maps imperfectly to the available
  dimensions, say so: "I'm using `regulatory` and `macro` as the closest
  proxies for your interest-rate thesis."
- **Acknowledge data limitations.** If a thesis-relevant dimension scores
  exactly 0 (data unavailable), say so. Do not pretend to evaluate against
  missing data.
- **Always include the share URL.**
- **Always include the disclaimer footer** verbatim from
  [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md).

## Reference material

- [`reference.md`](reference.md) — thesis archetype → dimension mapping
  table; 8+ common theses worked through.
- [`examples.md`](examples.md) — example thesis evaluations using real
  data.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md) — canonical
  multi-dimension glossary.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md) — disclaimer
  footer.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md) — MCP install.
