# ETF Reference

## Endpoints

| Endpoint | Use |
|----------|-----|
| `GET /v1/free/etf/list` | All available ETFs (US-listed) |
| `GET /v1/free/etf/holdings/{symbol}` | Holdings of an ETF |

### `holdings` response

```json
{
  "symbol": "SPY",
  "name": "SPDR S&P 500 ETF Trust",
  "asOf": "2026-05-08",
  "holdings": [
    { "symbol": "AAPL", "name": "Apple Inc.", "weight": 0.0721, "shares": 184_321_000 },
    ...
  ]
}
```

## Common ETF tickers

| Theme | Ticker |
|-------|--------|
| S&P 500 | `SPY`, `VOO`, `IVV` |
| Nasdaq 100 | `QQQ` |
| Russell 2000 | `IWM` |
| Dow | `DIA` |
| Total US | `VTI` |
| World ex-US | `VXUS` |
| Emerging Markets | `EEM`, `VWO` |
| Sectors (SPDR) | `XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLRE, XLB, XLC` |
| Bonds | `AGG, BND, TLT, IEF, HYG, LQD` |
| Gold | `GLD, IAU` |
| Crypto | `IBIT` (Bitcoin), `ETHA` (Ethereum) |
| Semiconductors | `SMH, SOXX` |
| Cybersecurity | `HACK, CIBR` |
| Clean Energy | `ICLN, TAN` |

## Patterns

- **ETF X-ray**: `holdings/SPY` → top 10 by weight → for each, parallel `/v1/stocks/quote/...` for daily contribution to ETF.
- **Sector exposure**: hit `XLK, XLF, XLE, XLV, XLI` quotes via `/v1/stocks/quotes?symbols=...`.
- **Index passthrough**: prefer `/v1/free/index/SP500/constituents` over `holdings/SPY` for the underlying index itself.
