# Workflows — End-to-End Examples

Concrete multi-step recipes. Each shows which endpoints to call and how to combine the responses.

---

## 1. Single-Ticker Deep Dive ("Tell me everything about AAPL")

Parallel calls:

1. `GET /v1/stocks/quote/AAPL` — current price, volume, market cap.
2. `GET /v1/stocks/profile/AAPL` — sector, industry, description.
3. `GET /v1/stocks/financials/AAPL?freq=yearly` — last 4 fiscal years.
4. `GET /v1/stocks/dividends/AAPL` — dividend history.
5. `GET /v1/stocks/earnings/AAPL` — upcoming + last 8 quarters.
6. `GET /v1/free/stocks/analyst-rating-summary/AAPL` — consensus.
7. `GET /v1/free/sec/insider-summary/AAPL` — 90d insider net.
8. `GET /v1/free/stocks/congress-trades?symbol=AAPL` — recent Congress.
9. `GET /v1/news/by-symbol/AAPL?limit=10` — recent news.
10. `GET /v1/stocks/history/AAPL?range=1y&interval=1d` — for sparkline.

Render as a Markdown report:

```
# AAPL — Apple Inc.
**Price**: $232.40 (+1.2%)   |   Mkt Cap $3.5T   |   Sector: Technology

## Consensus
35 analysts: 14 SB / 18 B / 8 H / 1 S / 0 SS — avg target $245.7 (+5.7% upside).

## Recent Activity
- Insider 90d net: -$12M (selling)
- Congress: 3 trades (2 buys / 1 sell, last 30d)

## Latest News
- ...
```

---

## 2. Compare Two Assets

> "Compare BTC vs ETH 30-day."

Parallel:
- `GET /v1/free/crypto/history/bitcoin?days=30`
- `GET /v1/free/crypto/history/ethereum?days=30`

Normalize each `prices` array to base 100 at first sample, compute % return, vol (std of daily log returns × √365), max drawdown.

---

## 3. Daily Market Briefing

Parallel:
- `GET /v1/market/summary`
- `GET /v1/free/market/sectors`
- `GET /v1/free/market/fear-greed`
- `GET /v1/free/market/vix`
- `GET /v1/free/market/top-gainers?count=10`
- `GET /v1/free/market/top-losers?count=10`
- `GET /v1/free/market/news?limit=10`
- `GET /v1/free/macro/treasury-rates`

Output structure:

```
1. Indices (S&P / Nasdaq / Dow / Russell / VIX)
2. Sectors (best / worst)
3. Sentiment (Fear & Greed, VIX)
4. Movers (top 5 up / down)
5. Yield curve snapshot (3M / 2Y / 10Y / 30Y, 10Y-2Y spread)
6. Headlines
```

---

## 4. Macro Dashboard

Parallel FRED calls:
- `GDPC1` (Real GDP)
- `CPIAUCSL` (CPI)
- `UNRATE` (unemployment)
- `FEDFUNDS` (policy rate)
- `DGS10`, `DGS2`, `T10Y2Y`
- `M2SL`
- `INDPRO`
- `UMCSENT`

For each, report latest value, 1-year change, 5-year context.

---

## 5. Pre-Earnings Prep

1. `GET /v1/free/market/earnings-calendar?date=<tomorrow>` → list.
2. For top N tickers in parallel:
   - `GET /v1/stocks/quote/{sym}`
   - `GET /v1/free/stocks/analyst-rating-summary/{sym}`
   - `GET /v1/free/sec/insider-summary/{sym}`
   - `GET /v1/news/by-symbol/{sym}?limit=5`
3. Highlight tickers where consensus is "Strong Buy" but insider net selling > $10M (caution flag).

---

## 6. ETF X-Ray

> "What's inside ARKK and how is it doing today?"

1. `GET /v1/free/etf/holdings/ARKK`.
2. Top 15 holdings by weight → `GET /v1/stocks/quotes?symbols=...`.
3. Compute weighted-average daily return = Σ (weight × changePercent).
4. Flag biggest contributors / detractors.

---

## 7. Macro × Commodity Correlation

> "How does WTI track 10Y yields over the last 2 years?"

- `GET /v1/free/commodity/history/CL=F?range=2y&interval=1d`
- `GET /v1/macro/indicator/DGS10` (or `/v1/free/commodity/fred/DCOILWTICO` if equivalent series wanted).
- Align on dates, compute Pearson correlation and rolling 60-day correlation.

---

## 8. Smart-Money Screen

For a watchlist, in parallel:
- `analyst-rating-summary/{sym}`
- `insider-summary/{sym}`
- `congress-trades?symbol={sym}`
- `wsb-sentiment/{sym}`

Score each ticker:
```
score = 2*(consensus=="Strong Buy") + (consensus=="Buy")
      + 2*(insider_net_30d > 0) + (congress_buys_30d - congress_sells_30d)
```

Rank and present top 10.
