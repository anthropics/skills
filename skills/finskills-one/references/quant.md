# Quant / Alternative Data Reference

Wall Street consensus, Congress trading, insider activity, retail sentiment, short volume, factor returns, earnings calendars.

## Analyst Ratings

| Endpoint | Use |
|----------|-----|
| `GET /v1/free/stocks/analyst-ratings/{symbol}` | Per-firm rating history (upgrades/downgrades) |
| `GET /v1/free/stocks/analyst-rating-summary/{symbol}` | Consensus summary: counts of Strong Buy / Buy / Hold / Sell / Strong Sell + average target |
| `GET /v1/free/stocks/estimates/{symbol}` | Forward EPS / revenue estimates and price targets |

```json
{
  "symbol": "AAPL",
  "ratings": { "strongBuy": 14, "buy": 18, "hold": 8, "sell": 1, "strongSell": 0 },
  "consensus": "Buy",
  "averageTarget": 245.7,
  "highTarget": 290.0,
  "lowTarget": 195.0,
  "currentPrice": 232.4,
  "upside": 0.057
}
```

## Congress Trading

`GET /v1/free/stocks/congress-trades` — recent disclosed transactions (House + Senate, STOCK Act).

Query: `symbol=NVDA` (filter), `limit=50`, `chamber=house|senate`.

`data`: `[ { politician, party, chamber, symbol, transactionType, amount, transactionDate, disclosureDate } ]`.

## Insider Trades

`GET /v1/free/stocks/insider-trades/{symbol}` (alias path; same as `/v1/free/sec/insider-trades/{symbol}`).

`GET /v1/free/sec/insider-summary/{symbol}` — 90-day net activity.

Read as **buys − sells** in dollar terms; persistent insider buying is more informative than selling (which can be 10b5-1 / tax driven).

## WallStreetBets Sentiment

`GET /v1/free/stocks/wsb-sentiment/{symbol}` — mention counts, sentiment polarity, comment growth.

`data`: `{ symbol, mentions24h, mentionsChange, sentiment: { positive, neutral, negative }, rank }`.

Useful for retail-flow / meme-stock screening; do not use as a fundamental signal.

## Short Volume (FINRA Reg-SHO)

| Endpoint | Use |
|----------|-----|
| `GET /v1/free/market/short-volume/{symbol}` | Daily short volume + % of total volume |
| `GET /v1/free/market/short-volume-top` | Highest short-volume ratio names |

## Earnings Calendar

`GET /v1/free/market/earnings-calendar?date=YYYY-MM-DD` (default = today).

`data`: `[ { symbol, name, time: "BMO|AMC", epsEstimate, epsActual, revenueEstimate } ]`.

## Fama–French Factors

`GET /v1/free/market/fama-french?model=3factor&freq=daily`

- `model`: `3factor` or `5factor`.
- `freq`: `daily`, `monthly`.

`data`: `[ { date, mktRf, smb, hml, rmw, cma, rf } ]`.

For backtests / factor regressions.

## Patterns

- **Smart-money screen**: insider-summary (net buy positive) + congress-trades recent buys + analyst rating Buy/Strong Buy → cross-reference.
- **Meme-stock detector**: wsb-sentiment mentionsChange > 200% AND short-volume ratio > 30%.
- **Pre-earnings prep**: earnings-calendar for tomorrow → for each ticker pull analyst-rating-summary, recent 8-K filings, news.
