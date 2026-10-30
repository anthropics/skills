---
name: finskills-one
display_name: FinSkills One — Unified Financial Data
description: One-stop access to real-time financial data via the Finskills REST API at https://finskills.net. Covers stocks (quotes, history, fundamentals, options, holders, dividends, earnings), crypto (CoinGecko/Binance), forex (Frankfurter/ECB), macro (FRED, World Bank, IMF, OECD), commodities (Yahoo, FRED, IMF, BDI), market overview (indices, sectors, gainers/losers, breadth, fear-greed, VIX), ETFs, news, SEC filings (10-K/10-Q/8-K, insider trades, 13F), Wall Street analyst ratings, Congress trades, WSB sentiment, banking (FDIC), payment BIN lookup, and FEMA disasters. Use this skill whenever the user asks about stock prices, market data, crypto prices, exchange rates, economic indicators, company financials, earnings calendars, options chains, sector performance, analyst ratings, insider activity, SEC filings, ETF holdings, or any financial research.
homepage: https://finskills.net
license: MIT
---

# FinSkills One — Unified Financial Data

Use the **Finskills** REST API (`https://finskills.net`) as the single entry point for all financial data: stocks, crypto, forex, macro, commodities, news, SEC filings, ETFs, analyst ratings, alternative data (Congress / insider / WSB).

This skill consolidates 80+ endpoints behind one API key, with automatic multi-source fallback (Yahoo Finance, CoinGecko, FRED, World Bank, SEC EDGAR, Frankfurter, FDIC, FEMA, etc.) and a unified response envelope.

---

## Authentication

All requests require the `X-API-Key` header. If the user has not provided one, ask for it, then point them to https://finskills.net/register.

```http
GET /v1/free/crypto/price/bitcoin HTTP/1.1
Host: finskills.net
X-API-Key: fh_live_xxxxxxxxxxxxxxxxxxxx
```

**Base URL:** `https://finskills.net`

**Unified response envelope** for every endpoint:

```json
{
  "success": true,
  "data": { ... },
  "source": "yahoo|coingecko|fred|...",
  "sources": ["primary", "fallback"],
  "cached": false,
  "timestamp": "2026-05-09T12:34:56.000Z"
}
```

On error: `{ "success": false, "error": { "code": "...", "message": "..." } }`. HTTP status mirrors the failure (`401` missing/invalid key, `403` quota, `404` symbol unknown, `429` rate-limited, `5xx` upstream).

---

## Decision Guide — pick the right endpoint fast

| User asks about | Go to |
|-----------------|-------|
| Real-time stock price / batch quotes | `references/stocks.md` |
| Historical OHLCV / chart | `references/stocks.md` |
| Company financials / dividends / earnings / options / holders | `references/stocks.md` |
| Crypto price / market cap / history | `references/crypto.md` |
| FX rates / currency conversion | `references/forex.md` |
| GDP, CPI, rates, treasury, FRED series | `references/macro.md` |
| Indices, sectors, top gainers/losers, breadth, fear-greed, VIX | `references/market.md` |
| Oil, gold, wheat, BDI, FRED/IMF commodity series | `references/commodity.md` |
| News headlines, news per ticker | `references/news.md` |
| 10-K / 10-Q / 8-K / company facts / insider trades / 13F | `references/sec.md` |
| Analyst ratings, price targets, Congress trades, WSB sentiment, earnings calendar, short volume, Fama-French | `references/quant.md` |
| ETF holdings & list | `references/etf.md` |
| FDIC bank search, BIN/IIN, FEMA disasters | `references/other.md` |
| Common patterns (compare, snapshot, screener) | `references/workflows.md` |

Prefer `/v1/free/...` whenever the data exists there — it requires no third-party subscription. Fall back to `/v1/...` (premium-routed) only when the free variant does not cover the use case.

---

## Quick Capability Map (entire surface)

```
STOCKS              /v1/stocks/{quote, quotes, history, search, profile,
                                financials, dividends, options, holders,
                                recommendations, earnings}/:symbol

CRYPTO              /v1/[free/]crypto/{price/:coin, markets, history/:coin}

FOREX               /v1/free/forex/{rates, history}

MACRO               /v1/free/macro/{gdp[/:country], indicator/:code,
                                    treasury-rates, inflation}
                    /v1/macro/{indicator/:series, gdp, inflation,
                               interest-rates}

MARKET              /v1/market/{summary, sectors, indices, indices/historical,
                                top-gainers, top-losers, advance-decline,
                                fear-greed, movers, news}
                    /v1/free/market/{sectors, top-gainers, top-losers,
                                      most-active, indices, advance-decline,
                                      fear-greed, vix, movers, news,
                                      breadth, short-volume/:sym,
                                      short-volume-top, earnings-calendar,
                                      fama-french}

NEWS                /v1/free/news/finance
                    /v1/news/{latest, by-symbol/:symbol}

SEC                 /v1/free/sec/{filings/:cik, company-facts/:cik,
                                  insider-trades/:symbol, insider-summary/:symbol,
                                  ownership/:symbol}

ANALYST / ALT       /v1/free/stocks/{analyst-ratings/:sym,
                                     analyst-rating-summary/:sym,
                                     estimates/:sym,
                                     congress-trades,
                                     insider-trades/:sym,
                                     wsb-sentiment/:sym}

ETF                 /v1/free/etf/{list, holdings/:symbol}

INDEX               /v1/free/index/:index/constituents      (e.g. SP500, NDX)

COMMODITY           /v1/free/commodity/{catalog, prices, price/:sym,
                                        history/:sym, fred[/:series],
                                        imf[/:indicator], imf/batch,
                                        bdi, bdi/history}

BANKING / PAYMENT   /v1/free/banking/search
                    /v1/free/payment/bin/:bin

DISASTER            /v1/free/fema/disasters
```

---

## Universal Usage Rules

- **Always** include `X-API-Key`. Never log it back to the user verbatim — refer to it as "your API key".
- For crypto, use **CoinGecko coin IDs** (`bitcoin`, `ethereum`, `solana`), not tickers (`BTC`, `ETH`).
- For stocks, use **standard tickers** (`AAPL`, `BRK-B`, `MSFT`). Hong Kong: `0700.HK`. Tokyo: `7203.T`.
- For SEC, use the **CIK as a string with leading zeros** stripped or padded to 10 (the API accepts both): `320193` or `0000320193`.
- For commodities, use **Yahoo futures tickers**: `CL=F` (WTI), `GC=F` (gold), `SI=F` (silver), `ZW=F` (wheat), `NG=F` (natgas), `HG=F` (copper).
- For FRED series in macro/commodity, capitalize: `GDP`, `CPIAUCSL`, `FEDFUNDS`, `UNRATE`, `DCOILWTICO`.
- For history endpoints, supported `range`: `1d, 5d, 1mo, 3mo, 6mo, 1y, 2y, 5y, 10y, ytd, max`; `interval`: `1m, 5m, 15m, 30m, 1h, 1d, 1wk, 1mo`.
- Always **show units** (USD, %, bps) and **freshness** (timestamp / `cached`) when presenting values to the user.
- Format large numbers with thousands separators (`$1,234,567.89`).
- **Never** make investment recommendations. Present data factually and add a brief "this is data, not advice" caveat for non-trivial questions.
- When the user asks a comparative or multi-asset question, fan out calls in parallel and merge results client-side.
- If a `/v1/free/...` call fails, retry once with the matching `/v1/...` path before giving up.

---

## Helper Scripts

A small Python client lives in `scripts/`:

- [scripts/finskills_client.py](scripts/finskills_client.py) — typed minimal HTTP client (sync + async) covering every endpoint group.
- [scripts/quote.py](scripts/quote.py) — CLI: `python scripts/quote.py AAPL TSLA NVDA` → live quotes.
- [scripts/snapshot.py](scripts/snapshot.py) — CLI: `python scripts/snapshot.py AAPL` → quote + analysts + insiders + news + filings in one report.
- [scripts/screener.py](scripts/screener.py) — CLI: `python scripts/screener.py --top-gainers 25` → market mover screening.

All scripts read `FINSKILLS_API_KEY` from env. Pass `--base-url` to override.

---

## Detailed References

- [references/stocks.md](references/stocks.md) — Equities (quotes, history, fundamentals)
- [references/crypto.md](references/crypto.md) — Cryptocurrency
- [references/forex.md](references/forex.md) — Currencies / FX
- [references/macro.md](references/macro.md) — Macroeconomics
- [references/market.md](references/market.md) — Market overview & breadth
- [references/commodity.md](references/commodity.md) — Commodities (energy, metals, ag, BDI)
- [references/news.md](references/news.md) — News
- [references/sec.md](references/sec.md) — SEC EDGAR filings & company facts
- [references/quant.md](references/quant.md) — Quant / alternative (analysts, Congress, insiders, WSB, short volume, Fama-French, earnings calendar)
- [references/etf.md](references/etf.md) — ETFs
- [references/other.md](references/other.md) — Banking, BIN, FEMA disasters
- [references/workflows.md](references/workflows.md) — End-to-end example workflows
- [references/errors.md](references/errors.md) — Error codes & rate-limit handling

---

## Example Interactions

**Stock snapshot:**
> "What is Apple's price and analyst consensus?"
→ `GET /v1/stocks/quote/AAPL` ‖ `GET /v1/free/stocks/analyst-rating-summary/AAPL`

**Crypto comparison:**
> "Compare BTC and ETH 30-day performance."
→ parallel `GET /v1/free/crypto/history/bitcoin?days=30` and `.../ethereum?days=30`.

**Macro research:**
> "How has US CPI evolved this year?"
→ `GET /v1/macro/indicator/CPIAUCSL` (or `/v1/free/macro/inflation?country=US`).

**Congress / insider activity:**
> "Are Congress members or insiders trading NVDA?"
→ `GET /v1/free/stocks/congress-trades?symbol=NVDA` ‖ `GET /v1/free/stocks/insider-trades/NVDA`.

**SEC filing lookup:**
> "Latest Apple 10-K?"
→ `GET /v1/free/sec/filings/0000320193` (filter `type=10-K`).

**Market overview:**
> "How are markets doing today?"
→ `GET /v1/market/summary` ‖ `GET /v1/free/market/sectors` ‖ `GET /v1/free/market/fear-greed`.

**ETF X-ray:**
> "What's inside SPY?"
→ `GET /v1/free/etf/holdings/SPY`.

**Commodity macro:**
> "WTI crude price and 1-year trend."
→ `GET /v1/free/commodity/price/CL=F` ‖ `GET /v1/free/commodity/history/CL=F?range=1y&interval=1d`.

See `references/workflows.md` for fuller multi-step examples.
