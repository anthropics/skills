---
name: haruspex-watchlist-review
description: Batch review of a stock watchlist using Haruspex scores, optimized for daily or weekly portfolio scans. Use this skill whenever the user wants to review multiple tickers at once, asks for a "watchlist update" or "portfolio review", lists 3 or more ticker symbols and wants analysis on all of them, asks "how are my stocks doing", wants a daily or weekly market check on specific names, or asks to compare or rank a group of stocks — even if they don't say "watchlist" explicitly. Prefer this skill over running haruspex-stock-analyst once per ticker when 3+ tickers are involved.
---

# Haruspex Watchlist Review

## What this skill does

Runs a single batched call against the Haruspex API and produces a scannable
table review of a watchlist: ranked by score, grouped by signal, with the
biggest movers and the largest dimensional flags surfaced separately.

Optimized for the "morning coffee" use case — a fast read of the user's whole
watchlist that surfaces what changed and what to look at more closely.

## When to use this skill

Trigger on any of these patterns:

- "Watchlist update" / "Run my watchlist" / "Daily check"
- "How are my stocks doing?"
- The user lists **3 or more tickers** in a single message
- "Compare AAPL, MSFT, GOOGL, META, AMZN"
- "Portfolio review" / "Weekly review"
- "Which of these is strongest?" with a list
- "Rank these tickers"

Defer to a sister skill if:
- Only **1–2 tickers** mentioned → use `haruspex-stock-analyst` instead.
- The user states a thesis on a position → use `haruspex-thesis-tracker`.
- The user is writing in Japanese → use `haruspex-stock-analyst-ja`.

## Prerequisites

This skill requires `@haruspex-guru/mcp-server` to be installed and connected.
**First action: verify the MCP tools are available.**

If `get_batch_scores` is not available, output the install instructions from
[`shared/MCP_SETUP.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md) and **stop**.

## Workflow

1. **Collect the ticker list.** If the user provided tickers, parse them. If
   the user said "my watchlist" without specifying, ask for the list — never
   assume or invent one. Trim to ≤50 tickers (the batch limit).
2. **Single batched call.** Call `get_batch_scores(symbols=[...])`. Do not
   call `get_stock_score` per ticker — the batched call exists for this.
3. **Handle partial NOT_FOUND.** Some tickers in the list may not be in the
   Haruspex universe. They will be absent from `data.scores`. Compute the
   missing set and report it honestly. Do not fabricate scores for missing
   tickers.
4. **Sort and group.** Sort returned scores by `score` descending. Group by
   `signal` (buy / hold / sell). Within each group, list largest score
   first.
5. **Surface movers.** Identify the top 3 by absolute `|change|`. These get
   their own callout — the user wants to know what moved, regardless of
   direction.
6. **Surface flags.** Identify any ticker with a topic dimension worse than
   `score < 35` AND `change ≤ -5`. These are the "watch closely" flags.
7. **Output** in the format below.

## Output format

Use this exact markdown structure. Replace bracketed values with real
captured data.

```markdown
## Watchlist Review — [N] tickers

### Buy signals
| Ticker | Score | Δ    | Outlook | Top driver        |
|--------|------:|-----:|---------|-------------------|
| [SYM]  |   N/100 | +N | bullish | [strongest dim]   |
| ...    |   ...  | ... | ...     | ...               |

### Hold signals
| Ticker | Score | Δ    | Outlook |
|--------|------:|-----:|---------|
| ...    | ...   | ...  | ...     |

### Sell signals
| Ticker | Score | Δ    | Outlook |
|--------|------:|-----:|---------|
| ...    | ...   | ...  | ...     |

### Biggest movers
- **[SYM]** [+N] — [one-line context]
- **[SYM]** [-N] — [one-line context]
- **[SYM]** [+N] — [one-line context]

### Watch closely
- **[SYM]** — [dim] dropped to [N]/100 ([change]); [one-line context]

### Coverage gaps
- [SYM_A], [SYM_B] — not currently in the Haruspex universe.

### Verify links
- [SYM]: [shareUrl]
- [SYM]: [shareUrl]
- ...

> **Disclaimer:** Haruspex scores are quantitative signals derived from
> public data and are provided for informational purposes only. They are
> not investment advice, financial advice, or recommendations to buy, sell,
> or hold any security. Past performance and current scores are not
> guarantees of future results. Always do your own research and consider
> consulting a licensed financial advisor before making investment
> decisions. Data via haruspex.guru.
```

### Section omission rules

- Drop empty signal-group sections (e.g. if no `sell` signals, omit that
  table entirely).
- Drop "Coverage gaps" if all tickers returned scores.
- Drop "Watch closely" if no dimension flags trigger.
- Always include "Biggest movers" — pick 1-3 by absolute change.
- Always include "Verify links" — one per ticker.

## Compliance rules (NEVER VIOLATE)

- **Do not give buy / sell / hold recommendations directed at the user.**
  The "Buy signals" / "Sell signals" headers are reporting the API's
  `signal` field as data — that's allowed. Do not say "you should buy
  these" or "sell these now."
- **Do not predict price movements.** Score change is observed; price is
  not predicted.
- **Do not provide position sizing, stop-loss, take-profit, or
  risk-management specifics** for any ticker on the list.
- **Do not infer holdings, allocation, or risk profile** from the list. The
  user gave you tickers, not a portfolio.
- **Acknowledge data limitations honestly.** Coverage gaps must be
  reported, not silently dropped.
- **Always include verify links** so the user can spot-check any row.
- **Always include the disclaimer footer** in the exact wording from
  [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md).
- **Never fabricate** a score, ticker, change value, or share URL.

## Reference material

- [`reference.md`](reference.md) — table layout details, mover-selection
  logic, threshold tuning.
- [`examples.md`](examples.md) — real example dialogues.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DIMENSIONS.md) — canonical
  multi-dimension glossary.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/DISCLAIMER.md) — canonical
  disclaimer footer.
- [`https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md`](https://github.com/Haruspex-guru/haruspex-skills/blob/main/shared/MCP_SETUP.md) — MCP install
  instructions.
