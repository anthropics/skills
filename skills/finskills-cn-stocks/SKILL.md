---
name: finskills-cn-stocks
description: Retrieve and interpret China A-share and exchange-traded fund data through the Finskills REST API, including quotes, batch quotes, adjusted daily or intraday history, security search and profiles, financials, dividends, options, holders, recommendations, and earnings. Use when a user asks about mainland Chinese stocks or ETFs by six-digit code, Chinese company name, Shanghai/Shenzhen suffix, A-share price history, 前复权/后复权, or comparative A-share research.
---

# FinSkills China A-Shares

Use `https://finskills.net` as the only public API base URL. Never call the private upstream service directly.

## Execute a request

1. Obtain a Finskills API key from the user or the `FINSKILLS_API_KEY` environment variable. Direct users without a key to `https://finskills.net/register`.
2. Normalize the requested security code. Accept bare six-digit codes such as `600519`, or qualified codes such as `600519.SH` and `000001.SZ`. Preserve an explicit suffix.
3. Select the smallest endpoint that answers the question. Read [references/api.md](references/api.md) for parameters and response fields.
4. Send `X-API-Key: <key>` over HTTPS. Never print, echo, log, or repeat the key.
5. Report the normalized symbol, exchange, currency, observation timestamp, interval, source, and cache state when available.

Use the bundled client for repeatable calls:

```bash
export FINSKILLS_API_KEY='fh_live_...'
python3 scripts/cn_stocks.py quote 600519
python3 scripts/cn_stocks.py history 600519 --interval 1d --adjustment qfq --limit 100
python3 scripts/cn_stocks.py quotes 600519 000001 300750
```

## Choose the endpoint

| Intent | Command / endpoint |
|---|---|
| Latest price for one security | `quote` → `/v1/stocks/quote/{symbol}` |
| Compare several latest prices | `quotes` → `/v1/stocks/quotes?symbols=...` |
| OHLCV history or returns | `history` → `/v1/stocks/history/{symbol}` |
| Resolve a name or code | `search` → `/v1/stocks/search?q=...` |
| Identity and listing profile | `profile` → `/v1/stocks/profile/{symbol}` |
| Fundamentals or event datasets | `financials`, `dividends`, `options`, `holders`, `recommendations`, `earnings` |

For comparisons, call independent endpoints concurrently where possible, then align observations by timestamp before calculating changes or returns.

## Apply A-share conventions

- Treat `600xxx` and `601xxx` codes as typically Shanghai, and `000xxx` and `300xxx` as typically Shenzhen, but trust the API's normalized `symbol` and `exchange` fields over inference.
- Use `qfq` (前复权) for return and chart analysis unless the user requests raw (`none`) or 后复权 (`hfq`) prices.
- Use `1d` for long-range analysis; use `30m` or `60m` only for intraday questions.
- Interpret all timestamps in `Asia/Shanghai` when the response declares that timezone.
- Treat `amount` as turnover value and `volume` as traded quantity; do not interchange them.
- Do not invent missing fundamentals. Some dataset endpoints may validly return `count: 0` and `data: []`.

## Present results

- Distinguish latest available close from a live intraday quote by checking `timestamp`, `interval`, and `source`.
- State that prices are in CNY unless the response says otherwise.
- For calculated performance, name the adjustment mode and date range.
- Present factual analysis, not personalized investment advice.
- When an upstream endpoint fails or returns no rows, state that limitation and suggest a narrower date range, another adjustment mode, or a later retry.

See [references/api.md](references/api.md) for the complete focused API reference and response examples.
