# Market Overview Reference

Indices, sectors, breadth, sentiment.

## Premium tier (`/v1/market/...`)

| Endpoint | Description |
|----------|-------------|
| `GET /v1/market/summary` | Major indices (S&P 500, Dow, Nasdaq, Russell 2000), trending tickers, top movers |
| `GET /v1/market/sectors` | S&P 500 sector performance (1d, 5d, 1mo, ytd) |
| `GET /v1/market/indices` | Snapshot of global indices |
| `GET /v1/market/indices/historical?symbol=^GSPC&range=1y` | Historical index series |
| `GET /v1/market/top-gainers?count=25` | Top gainers (US) |
| `GET /v1/market/top-losers?count=25` | Top losers |
| `GET /v1/market/advance-decline` | NYSE/Nasdaq advance-decline counts |
| `GET /v1/market/fear-greed` | CNN Fear & Greed Index |
| `GET /v1/market/movers` | Combined gainers/losers/active |
| `GET /v1/market/news` | Aggregated market news |

## Free tier (`/v1/free/market/...`)

Same surface plus extras:

| Endpoint | Description |
|----------|-------------|
| `GET /v1/free/market/sectors` | Sector ETF performance (XLK, XLF, XLE, …) |
| `GET /v1/free/market/top-gainers?count=25` | |
| `GET /v1/free/market/top-losers?count=25` | |
| `GET /v1/free/market/most-active?count=25` | Volume leaders |
| `GET /v1/free/market/indices` | Global indices |
| `GET /v1/free/market/advance-decline` | A/D line |
| `GET /v1/free/market/fear-greed` | Fear & Greed |
| `GET /v1/free/market/vix` | VIX (^VIX) standalone |
| `GET /v1/free/market/movers?count=25` | Three-list combined movers |
| `GET /v1/free/market/news?limit=20` | Market news |
| `GET /v1/free/market/breadth` | Detailed breadth: A/D, new highs/lows, %above 50/200d MA |
| `GET /v1/free/market/short-volume/{symbol}` | FINRA reg-SHO short volume |
| `GET /v1/free/market/short-volume-top` | Highest short-volume ratio names |
| `GET /v1/free/market/earnings-calendar?date=YYYY-MM-DD` | Daily earnings calendar |
| `GET /v1/free/market/fama-french?model=3factor&freq=daily` | Fama–French factor returns |

### Index symbol cheatsheet

| Symbol | Index |
|--------|-------|
| `^GSPC` | S&P 500 |
| `^DJI` | Dow Jones |
| `^IXIC` | Nasdaq Composite |
| `^NDX` | Nasdaq 100 |
| `^RUT` | Russell 2000 |
| `^VIX` | CBOE Volatility |
| `^FTSE` | FTSE 100 |
| `^N225` | Nikkei 225 |
| `^HSI` | Hang Seng |
| `000001.SS` | Shanghai Composite |
| `^STOXX50E` | Euro Stoxx 50 |

## Index Constituents

`GET /v1/free/index/{index}/constituents` — accepted IDs: `SP500`, `NDX` (Nasdaq 100), `DJIA`, `RUT` (Russell 2000).

```bash
curl -H "X-API-Key: $KEY" https://finskills.net/v1/free/index/SP500/constituents
```

## Patterns

- **Daily market briefing**: parallel calls to `summary`, `sectors`, `fear-greed`, `vix`, `top-gainers`, `top-losers`, `news?limit=10`. Stitch into a markdown report.
- **Risk-off check**: VIX > 25 + Fear-Greed < 30 + 10Y–2Y inverted → flag risk-off.
