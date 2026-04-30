# Reference: haruspex-stock-analyst

Edge cases, output variations, and details that didn't fit in `SKILL.md`.

## API response shape

`get_stock_score(symbol)` returns:

```json
{
  "status": "success",
  "data": {
    "symbol": "NVDA",
    "name": null,
    "score": 78,
    "previousScore": 62,
    "change": 16,
    "outlook": "bullish",
    "signal": "buy",
    "topicScores": {
      "ai-exposure":      { "name": "ai-exposure",      "score": 57, "change": 0 },
      "climate-risk":     { "name": "climate-risk",     "score": 53, "change": 0 },
      "competitors":      { "name": "competitors",      "score": 75, "change": 5 },
      "concentration-risk":{"name": "concentration-risk","score": 44, "change": 0 },
      "earnings":         { "name": "earnings",         "score": 72, "change": 0 },
      "esg":              { "name": "esg",              "score": 0,  "change": 0 },
      "github-activity":  { "name": "github-activity",  "score": 69, "change": 0 },
      "insider-trading":  { "name": "insider-trading",  "score": 50, "change": 0 },
      "institutional":    { "name": "institutional",    "score": 65, "change": 0 },
      "macro":            { "name": "macro",            "score": 65, "change": 6 },
      "management":       { "name": "management",       "score": 49, "change": 0 },
      "patents":          { "name": "patents",          "score": 50, "change": 0 },
      "regulatory":       { "name": "regulatory",       "score": 65, "change": 0 },
      "supplychain":      { "name": "supplychain",      "score": 44, "change": 0 },
      "us_china_official":{"name": "us_china_official", "score": 35, "change": -9 },
      "us_china_unofficial":{"name":"us_china_unofficial","score":35, "change": -9 }
    },
    "date": "2026-04-29",
    "analyzedAt": "2026-04-29T05:02:11.104Z",
    "tradingTimeline": "investment",
    "shareUrl": "https://haruspex.guru/s/9JWj9_sZzYKtcBgfhpkB4K3m"
  }
}
```

`get_stock_score_history(symbol, days=30)` returns `data.scores` as an array
of the same per-day objects, ordered most-recent first, plus `data.from`,
`data.to`, `data.count`.

`get_stock_news(symbol)` returns `data.articles` as an array of
`{title, url, publishedAt, source, image}`.

## Outlook vs. signal

These are two independent fields and may disagree.

- **`outlook`** is the directional read (e.g. `bullish`, `bearish`, `neutral`).
- **`signal`** is the action signal (`buy`, `hold`, `sell`).

A stock can be `outlook: bullish, signal: hold` (favorable conditions but no
clear actionable edge), or `outlook: neutral, signal: buy`, etc. When they
disagree, surface both and let the user reconcile — don't pick one.

## Edge case: NOT_FOUND

API returns:

```json
{
  "status": "error",
  "error": {
    "code": "NOT_FOUND",
    "message": "No Haruspex Score found for symbol \"TM\". The stock may not be in our analysis universe."
  }
}
```

Output the message honestly. Suggest `search_stocks(name)` if the user gave
a company name — but only if a search is likely to help. Do **not** fabricate
a score for the symbol.

## Edge case: dimension scoring exactly 0

Treat as "data unavailable" rather than "real low score." For example, NVDA
currently shows `esg: 0` — the right phrasing is "ESG data is not currently
available for NVDA," not "NVDA has terrible ESG."

## Edge case: sparse history

If `data.count` is below ~10, the trajectory paragraph should call this out:
"Only N days of history are available, so the trend read is preliminary."
Do not extrapolate beyond the data.

## Edge case: no recent change

If headline `change` is 0 and no dimension changed by more than a few points,
skip the news call and write a brief trajectory paragraph noting the score is
stable.

## Edge case: `cached: true`

The API may return a cached score. The `analyzedAt` timestamp tells you when
the underlying analysis ran. If `analyzedAt` is more than ~24 hours old, note
it in the output: "(score last refreshed [date])".

## Picking the watch set

A dimension qualifies for the "watch" set if any of:

- Current `score` < 50.
- `change` ≤ -5.
- It's a **risk** dimension (`climate-risk`, `concentration-risk`,
  `us_china_official`, `us_china_unofficial`) where lower means more risk
  — even if not yet below 50.

Cap the list at 3. Pick the most informative — typically the ones with the
largest negative `change`, breaking ties by lowest current score.

## Topic-dimension priority hints

Some dimensions matter more for some sectors:

| Sector approximation       | Dimensions worth surfacing first       |
|----------------------------|----------------------------------------|
| Semiconductors / AI infra  | ai-exposure, supplychain, us_china_*   |
| Software / SaaS            | github-activity, ai-exposure, earnings |
| Banks / Financials         | regulatory, macro, earnings            |
| Energy / Materials         | climate-risk, supplychain, macro       |
| Consumer (retail, CPG)     | macro, supplychain, concentration-risk |
| Pharma / Biotech           | regulatory, patents, management        |
| Mega-cap diversified       | competitors, institutional, regulatory |

Use these as priors, not rules. Always defer to what the actual `change`
values say.
