# Stocks Reference

Equities endpoints. All require `X-API-Key`.

## Quotes

### `GET /v1/stocks/quote/{symbol}`
Real-time quote: price, change, change%, volume, market cap, day range, 52-week range.

```bash
curl -H "X-API-Key: $KEY" https://finskills.net/v1/stocks/quote/AAPL
```

Response `data`: `{ symbol, price, change, changePercent, volume, marketCap, dayHigh, dayLow, fiftyTwoWeekHigh, fiftyTwoWeekLow, currency, exchange, timestamp }`.

### `GET /v1/stocks/quotes?symbols=AAPL,MSFT,TSLA`
Batch quotes (≤ 50 symbols per call). Returns `data: [ {…quote}, … ]`.

### `GET /v1/stocks/search?q=apple&limit=10`
Search by name/ticker. Returns `[ { symbol, name, exchange, type } ]`.

## History (OHLCV)

### `GET /v1/stocks/history/{symbol}`
Query: `interval` (`1m,5m,15m,30m,1h,1d,1wk,1mo`), `range` (`1d,5d,1mo,3mo,6mo,1y,2y,5y,10y,ytd,max`), or explicit `start=YYYY-MM-DD&end=YYYY-MM-DD`.

```bash
curl -H "X-API-Key: $KEY" \
  "https://finskills.net/v1/stocks/history/AAPL?interval=1d&range=1y"
```

Response: `data: [ { date, open, high, low, close, adjClose, volume } ]`.

## Fundamentals (Yahoo Finance backed)

| Endpoint | Purpose |
|----------|---------|
| `GET /v1/stocks/profile/{symbol}` | Sector, industry, employees, description, website |
| `GET /v1/stocks/financials/{symbol}?freq=yearly\|quarterly` | Income statement, balance sheet, cash flow |
| `GET /v1/stocks/dividends/{symbol}` | Dividend history |
| `GET /v1/stocks/options/{symbol}?date=YYYY-MM-DD` | Options chain (omit `date` for nearest expiry) |
| `GET /v1/stocks/holders/{symbol}` | Major + institutional holders |
| `GET /v1/stocks/recommendations/{symbol}` | Analyst recommendations history |
| `GET /v1/stocks/earnings/{symbol}` | Earnings history & estimates |

### Financials shape

```json
{
  "freq": "yearly",
  "incomeStatement": [ { "date": "2025-09-28", "totalRevenue": 391035000000, "netIncome": 93736000000, ... } ],
  "balanceSheet":   [ { "date": "...", "totalAssets": ..., "totalLiabilities": ..., ... } ],
  "cashFlow":       [ { "date": "...", "operatingCashFlow": ..., "capex": ..., "freeCashFlow": ... } ]
}
```

## Symbol Conventions

- US: plain ticker — `AAPL`, `MSFT`, `BRK-B` (use hyphen for class shares).
- HK: `0700.HK` (Tencent), `0005.HK` (HSBC).
- Tokyo: `7203.T` (Toyota).
- London: `HSBA.L`.
- China A: `600519.SS` (Shanghai), `000001.SZ` (Shenzhen).

## Tips

- For lots of tickers prefer `/quotes?symbols=…` over many single calls.
- The `/profile` endpoint is the cheapest way to validate a symbol exists.
- Options chain volume can be heavy; always pass an explicit `date` when possible.
- Survey-style requests ("show me Apple's everything") → call profile + quote + financials(yearly) + dividends + earnings + recommendations in parallel.

## Related

- Analyst consensus / price targets → `references/quant.md`.
- News for a symbol → `references/news.md`.
- SEC filings for a symbol's CIK → `references/sec.md`.
