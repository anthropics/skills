# Reference: haruspex-watchlist-review

## API response shape — `get_batch_scores`

```json
{
  "status": "success",
  "data": {
    "count": 5,
    "scores": [
      { "symbol": "AAPL", "score": 75, "signal": "buy", "outlook": "bullish",
        "change": 23, "topicScores": { ... }, "shareUrl": "https://..." },
      { "symbol": "NVDA", "score": 78, ... },
      ...
    ]
  }
}
```

Tickers that are not in the analysis universe are simply **absent** from
`data.scores`. The skill must compare requested vs. returned to compute the
coverage gap.

## Batch limits

- Maximum 50 tickers per call. Reject inputs above 50 with a clear message.
- The batch endpoint counts as 1 credit per ticker scored, not 1 credit per
  call. Mention this if a user asks why a 50-ticker scan used 50 credits.

## Mover selection

Definition: a "mover" is a ticker with the largest `|change|` since the
previous reading.

- Pick top 3 by absolute change.
- If a ticker has change of 0, never call it a mover even if everything else
  has small changes.
- Show direction explicitly with `+`/`-`.
- Provide a one-line context per mover. Acceptable contexts:
  - "Driven by competitors dimension (+9)."
  - "Macro and supplychain both improved this period."
  - "us_china_unofficial fell -26."
- Do not speculate about news catalysts unless news has actually been
  fetched for that ticker. Within this skill, we don't fetch news.

## Watch-closely flag selection

A ticker enters the "watch closely" set if **any** topic dimension satisfies
both:

- `score < 35` (currently in poor territory), AND
- `change ≤ -5` (recently deteriorated by ≥5 points).

Cap at 3. If more than 3 qualify, prefer the dimensions with the largest
negative change, breaking ties by lowest current score.

Risk dimensions (`climate-risk`, `concentration-risk`, `us_china_official`,
`us_china_unofficial`) get the same treatment — recall that for those, low
score = high risk.

## Sort order

- Within each signal group, sort by `score` descending.
- The signal groups themselves are ordered: **Buy → Hold → Sell**, regardless
  of group sizes. This is the most-scannable order for a daily check.

## When the watchlist has subgroups

If the user pre-organized their watchlist (e.g. "my tech watchlist: AAPL
MSFT NVDA, my energy watchlist: XOM CVX"), preserve their grouping in the
output rather than merging. Run one batch call (still limit 50 total) but
present results in their groups. Each group gets its own buy/hold/sell
mini-tables.

## Refusing implausible inputs

- If the user pastes more than 50 tickers, ask them to trim. Do not
  silently truncate.
- If they include obvious junk strings (e.g. "AAPL, hello, NVDA"), ask
  whether the junk strings were meant as tickers or accidental.
- If they include lowercase or formatted symbols ("aapl", "$AAPL"),
  normalize to uppercase before the API call.

## Re-running the same watchlist

If the user asks for "the same as yesterday" or references a prior watchlist
review in this conversation, reuse the ticker list from earlier in the
conversation if it's clearly there. If you can't find it in conversation
context, ask for the list rather than guessing.

The skill does not persist watchlists across conversations. That's a feature,
not a bug — Haruspex doesn't store user portfolios via the MCP path.
