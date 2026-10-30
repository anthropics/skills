# Forex Reference

Backed by Frankfurter (ECB) primary, with Open ER API and FloatRates fallback.

## `GET /v1/free/forex/rates`

Latest exchange rates.

Query:
- `base` — base currency, default `USD`. Common: `USD, EUR, GBP, JPY, CNY, HKD, AUD, CAD, CHF, SGD`.
- `symbols` — comma-separated list to filter target currencies (optional).

```bash
curl -H "X-API-Key: $KEY" \
  "https://finskills.net/v1/free/forex/rates?base=USD&symbols=EUR,JPY,CNY"
```

`data`: `{ base, date, rates: { EUR: 0.92, JPY: 156.4, CNY: 7.21 } }`.

## `GET /v1/free/forex/history`

Historical exchange rates between two currencies.

Query (all required except `interval`):
- `base` (e.g. `USD`)
- `target` (single, e.g. `EUR`)
- `start` — `YYYY-MM-DD`
- `end` — `YYYY-MM-DD`

```bash
curl -H "X-API-Key: $KEY" \
  "https://finskills.net/v1/free/forex/history?base=USD&target=CNY&start=2025-01-01&end=2026-01-01"
```

`data`: `{ base, target, rates: { "2025-01-02": 7.15, "2025-01-03": 7.16, ... } }`.

## Conversion Pattern

```python
amount_eur = amount_usd * rates["EUR"]
```

For cross rates not directly returned, triangulate via USD:
```
EUR/JPY = (USD/JPY) / (USD/EUR)
```

## Notes

- ECB updates once per business day around 16:00 CET. Weekend/holiday queries return the last business day.
- For **intraday** FX, this skill is not the right place — Frankfurter is daily-only. Use a stock symbol like `EURUSD=X` via `/v1/stocks/quote/EURUSD=X` for live FX quotes.
