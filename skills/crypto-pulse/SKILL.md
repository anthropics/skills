---
name: crypto-pulse
description: Real-time cryptocurrency market intelligence. Fetches prices, market caps, volume, dominance, trending coins, and DEX data. Use when user asks about crypto prices, market cap rankings, trending coins, DeFi data, token research, on-chain metrics, or cryptocurrency portfolio context. Triggers on phrases like "crypto prices", "bitcoin price", "ethereum", "top coins", "what's pumping", "crypto market", "coin research", "token analysis", "DeFi stats", "crypto dominance".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(python:*) WebFetch
metadata:
  author: Maksim Soltan
  version: 1.0.0
  apis: CoinGecko, DexScreener, Alternative.me
  auth: none-required
---

# Crypto Pulse

Deep crypto market intelligence from free APIs. CoinGecko + DexScreener + sentiment.

## APIs Used (all free)

- **CoinGecko**: `https://api.coingecko.com/api/v3` — top coins, market data, coin details
- **DexScreener**: `https://api.dexscreener.com/latest/dex` — DEX pairs, new tokens, liquidity
- **Alternative.me**: `https://api.alternative.me/fng/` — Fear & Greed index

## Workflow

### Step 1: Parse Intent

Determine what the user wants:
- **Price check** → single coin or list → `/coins/markets` with specific IDs
- **Market overview** → top 20 by market cap → `/coins/markets`
- **Trending** → what's hot right now → `/search/trending`
- **Specific coin research** → detailed data → `/coins/{id}`
- **DEX token research** → new/small cap → DexScreener
- **Dominance** → BTC/ETH dominance → `/global`

### Step 2: Fetch Data

**Top coins:**
```
GET https://api.coingecko.com/api/v3/coins/markets?vs_currency=usd&order=market_cap_desc&per_page=20&page=1&sparkline=false&price_change_percentage=1h,24h,7d
```

**Trending coins:**
```
GET https://api.coingecko.com/api/v3/search/trending
```

**Global market data:**
```
GET https://api.coingecko.com/api/v3/global
```

**Specific coin:**
```
GET https://api.coingecko.com/api/v3/coins/{id}?localization=false&tickers=false&market_data=true&community_data=false&developer_data=false
```

**DEX pairs (for new/small tokens):**
```
GET https://api.dexscreener.com/latest/dex/search?q={TOKEN_SYMBOL}
GET https://api.dexscreener.com/latest/dex/tokens/{CONTRACT_ADDRESS}
```

**Fear & Greed:**
```
GET https://api.alternative.me/fng/?limit=7
```

### Step 3: Coin ID Resolution

CoinGecko uses IDs not tickers. Common mappings:
- BTC → bitcoin
- ETH → ethereum
- SOL → solana
- BNB → binancecoin
- USDC → usd-coin
- XRP → ripple
- DOGE → dogecoin
- ADA → cardano
- AVAX → avalanche-2
- LINK → chainlink

For unknown symbols: use `/search?query={SYMBOL}` to resolve.

### Step 4: Output Format

**Market overview:**
```
## Crypto Pulse
[DATE] | Fear & Greed: [X]/100 — [Classification]

### Global Stats
- Total Market Cap: $X.XT
- BTC Dominance: X.X%
- ETH Dominance: X.X%
- 24h Volume: $X.XB

### Top 20 by Market Cap
| Rank | Coin | Price | 1h | 24h | 7d | Mkt Cap |
|------|------|-------|----|----|-----|---------|

### Trending Now
[CoinGecko trending list]
```

**Single coin research:**
```
## [COIN NAME] (SYMBOL)
Price: $XXX | Rank: #X | Category: [X]

### Market Data
- Market Cap: $X.XB (#X)
- 24h Volume: $X.XB
- Circulating Supply: X.XM / X.XM (XX% issued)
- ATH: $XXX (date, XX% from ATH)
- ATL: $XXX (date)

### Price Changes
- 1h: +X%
- 24h: +X%
- 7d: +X%
- 30d: +X%

### DEX Data (if available)
[Liquidity pools, pair data from DexScreener]
```

## Rate Limit Handling

CoinGecko free tier: ~10-30 requests/minute
- Batch coin requests (use `ids=bitcoin,ethereum,solana` not 3 separate calls)
- Cache responses locally if making multiple queries
- On 429: wait 10s and retry once

## Examples

User: "What are crypto prices right now?"
→ `/coins/markets` top 20 + global + Fear & Greed

User: "Research Solana"
→ `/coins/solana` full data + DexScreener for SOL pairs

User: "What's trending in crypto?"
→ `/search/trending` + recent 24h gainers

User: "BTC and ETH prices"
→ `/coins/markets?ids=bitcoin,ethereum`
