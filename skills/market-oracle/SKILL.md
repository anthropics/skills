---
name: market-oracle
description: Multi-signal financial intelligence synthesizer. Combines crypto prices, stock indices, macro economic data, news sentiment, and Fear and Greed signals to generate actionable market intelligence. Use when user wants comprehensive market analysis, macro picture, trading context, risk-on/risk-off assessment, or market research. Triggers on phrases like "market overview", "market conditions", "what's the market doing", "macro picture", "risk assessment", "market intelligence", "financial overview", "market analysis", "what should I know about markets today".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(python:*) WebFetch
metadata:
  author: Maksim Soltan
  version: 1.0.0
  apis: CoinGecko, Yahoo Finance, FRED, Fear-Greed-Index
  auth: none-required-for-basic
---

# Market Oracle

Cross-signal financial intelligence. Detects divergence between price, narrative, and macro reality — the contradiction hunter pattern applied to markets.

## APIs Used

- **CoinGecko**: `https://api.coingecko.com/api/v3` — crypto prices/market caps (no auth, rate limited)
- **Yahoo Finance (unofficial)**: `https://query1.finance.yahoo.com/v8/finance/chart/{TICKER}` — equities (no auth)
- **FRED**: `https://fred.stlouisfed.org/graph/fredgraph.csv?id={SERIES}` — macro data (no auth for basic)
- **Alternative.me Fear & Greed**: `https://api.alternative.me/fng/?limit=2` — sentiment (no auth)
- **Hacker News**: `https://hn.algolia.com/api/v1/search?query=market+crypto&tags=story` — community signals

## Workflow

### Step 1: Parse User Intent

Determine scope:
- `crypto` → CoinGecko priority
- `stocks` / `equities` → Yahoo Finance priority
- `macro` → FRED priority
- `all` / unspecified → run everything

Extract specific assets if mentioned (BTC, ETH, SPY, AAPL, etc.)

### Step 2: Parallel Fetch

Run all fetches simultaneously:

```python
scripts/market_fetch.py --mode all
```

**Crypto (CoinGecko):**
```
GET https://api.coingecko.com/api/v3/coins/markets?vs_currency=usd&order=market_cap_desc&per_page=20&page=1&sparkline=false&price_change_percentage=24h,7d
```

**Equities (Yahoo Finance):**
Key tickers: SPY, QQQ, DIA, VIX, GLD, TLT, DXY
```
GET https://query1.finance.yahoo.com/v8/finance/chart/SPY?interval=1d&range=5d
```

**Macro (FRED — no auth needed for CSV):**
- DFF: Fed Funds Rate
- CPIAUCSL: CPI
- UNRATE: Unemployment
- DGS10: 10-year Treasury yield
```
GET https://fred.stlouisfed.org/graph/fredgraph.csv?id=DFF
```

**Fear & Greed:**
```
GET https://api.alternative.me/fng/?limit=2
```
Returns: index 0-100 (0=extreme fear, 100=extreme greed) + classification

### Step 3: Cross-Signal Analysis

**Risk-on / Risk-off classification:**
```
Risk-ON signals:
- VIX < 20
- Crypto up > 2% 24h
- SPY up > 0.5%
- Fear & Greed > 60

Risk-OFF signals:
- VIX > 25
- Crypto down > 3% 24h
- SPY down > 1%
- Fear & Greed < 30
- DXY rising
- TLT rising (flight to safety)
```

**Contradiction detection (the edge):**
- Price rising but Fear & Greed in extreme greed → distribution zone signal
- Price falling but on-chain accumulation → potential bottom signal
- News bullish but VIX elevated → narrative vs. reality gap
- Crypto up but DXY up → unusual correlation break

### Step 4: Generate Report

```
## Market Oracle Report
[DATE] [TIME UTC]

### Macro Pulse
| Indicator | Value | Change | Signal |
|-----------|-------|--------|--------|
| SPY       | $XXX  | +X%    | 🟢/🔴  |
| QQQ       | $XXX  | +X%    | 🟢/🔴  |
| VIX       | XX    | +X     | 🟢/🔴  |
| DXY       | XXX   | +X%    | 🟢/🔴  |
| 10Y Yield | X.XX% | +X bps | 🟢/🔴  |

### Crypto Markets
| Asset | Price | 24h | 7d | Mkt Cap |
|-------|-------|-----|----|---------|
| BTC   | $XXX  | +X% | +X%| $XTTB  |
| ETH   | $XXX  | +X% | +X%| $XTTB  |

### Sentiment
**Fear & Greed:** XX/100 — [Classification]
**Yesterday:** XX/100

### Macro Context
- Fed Funds Rate: X.XX%
- CPI (latest): X.X% YoY
- 10Y Treasury: X.XX%

### Signal Matrix
**Risk posture:** 🟢 RISK-ON / 🔴 RISK-OFF / 🟡 NEUTRAL

**Contradictions detected:**
- [Any divergences between signals]

### Key Narratives vs. Data
[What news says vs. what data shows]
```

## Error Handling

- CoinGecko rate limit (429): exponential backoff, use cached data if available
- Yahoo Finance blocked: note in output, provide known last values
- FRED CSV unavailable: skip macro indicators, note gap
- All equities sources fail: output crypto + sentiment only, flag equity data gap

## Notes on Rate Limits

- CoinGecko free: 10-30 req/min — batch asset fetches
- Yahoo Finance: unofficial, may break — wrap in try/except always
- FRED: very permissive for public data
- Alternative.me: generous limits

## Examples

User: "What's the market doing today?"
→ Run all sources, generate full report

User: "Crypto market overview"
→ CoinGecko top 20 + Fear & Greed + HN crypto signals

User: "Is it risk-on or risk-off right now?"
→ VIX + SPY + crypto + Fear & Greed → risk classification

User: "Macro picture for markets"
→ FRED data (rates, CPI, yields) + equity indices
