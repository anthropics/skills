---
name: ai-oracle-query
description: "Directly query the APRO AI Oracle Ticker API to fetch live cryptocurrency data — prices, categories, and OHLCV candlestick charts. No code generation needed; the agent calls the API and returns results immediately. Use this skill whenever the user asks for real-time crypto prices, market data, coin categories, price history, candlestick data, or anything related to querying crypto market information from the APRO Oracle. Also triggers on 'check BTC price', 'show me ETH chart', 'what coins are in DeFi category', 'crypto market data', etc."
allowed-tools: Read, Bash
---

# APRO AI Oracle Ticker — Live Query

This skill lets you call the APRO AI Oracle Ticker API directly and return data to the user. No code generation — just HTTP requests and formatted results.

## Authentication

API calls require two headers: `X-API-KEY` and `X-API-SECRET`.

**Resolution order** (try each in sequence, use the first that works):

1. **Environment variables**: Check for `APRO_API_KEY` and `APRO_API_SECRET`
   ```bash
   echo "${APRO_API_KEY:-NOT_SET}" && echo "${APRO_API_SECRET:-NOT_SET}"
   ```
2. **Ask the user**: If either is `NOT_SET`, ask the user to provide their API key and secret before proceeding. Do not make API calls without valid credentials.

Once obtained, store them in shell variables for the session:
```bash
API_KEY="<value>"
API_SECRET="<value>"
```

## API Base

```
https://api-ai-oracle.apro.com
```

## CRITICAL: Parameter Naming

This API uses **full cryptocurrency names** (e.g., `"Bitcoin"`, `"Ethereum"`), NOT ticker symbols like `"BTC"` or `"ETH"`. When a user says "BTC price", you must translate to `name=Bitcoin`. Common mappings:

| User says | API `name` param |
|-----------|-----------------|
| BTC | Bitcoin |
| ETH | Ethereum |
| SOL | Solana |
| DOGE | Dogecoin |
| ADA | Cardano |
| DOT | Polkadot |
| AVAX | Avalanche |
| MATIC / POL | Polygon |
| LINK | Chainlink |
| UNI | Uniswap |
| TON | Toncoin |
| XRP | XRP |
| TRX | TRON |
| SUI | Sui |
| APT | Aptos |

If unsure of the full name, call **currency/support** with `restricted=relaxed` first to verify and resolve the name.

## Available Endpoints

There are 6 endpoints. Read the user's request and pick the right one(s).

---

### 1. List Currencies — `GET /v2/ticker/currencies/list`

**When to use**: User asks what coins are available, or you need to look up the full name for a symbol.

**Parameters**:
| Param | Required | Default | Example |
|-------|----------|---------|---------|
| `page` | No | `1` | `1`, `2`, `3` |
| `size` | No | `20` | `10`, `50`, `100` |

**Call pattern**:
```bash
curl -s -X GET "https://api-ai-oracle.apro.com/v2/ticker/currencies/list?page=1&size=20" \
  -H "X-API-KEY: ${API_KEY}" \
  -H "X-API-SECRET: ${API_SECRET}"
```

**Response data**: Direct JSON array of `{name, symbol, keywords, support_providers}` (data is the array itself, not `{currencies: [...]}`)

---

### 2. Check Currency Support — `GET /v2/ticker/currency/support`

**When to use**: User asks if a specific coin is supported, or you need to verify a coin exists before querying price/OHLCV.

**Parameters**:
| Param | Required | Default | Example |
|-------|----------|---------|---------|
| `name` | **Yes** | — | `Bitcoin`, `Ethereum` |
| `restricted` | **Yes** | — | **always use `relaxed`** |

**Call pattern**:
```bash
curl -s -X GET "https://api-ai-oracle.apro.com/v2/ticker/currency/support?name=Bitcoin&restricted=relaxed" \
  -H "X-API-KEY: ${API_KEY}" \
  -H "X-API-SECRET: ${API_SECRET}"
```

**Response data fields**: `{name, symbol, keywords, support_providers}`

---

### 3. Get Price — `GET /v2/ticker/currency/price`

**When to use**: User asks for current price, or price data for a coin.

**Parameters**:
| Param | Required | Default | Example |
|-------|----------|---------|---------|
| `name` | **Yes** | — | `Bitcoin`, `Ethereum` |
| `quotation` | **Yes** | — | `USD`, `EUR` |
| `type` | No | `median` | `median`, `average` |

**Call pattern**:
```bash
curl -s -X GET "https://api-ai-oracle.apro.com/v2/ticker/currency/price?name=Bitcoin&quotation=USD&type=median" \
  -H "X-API-KEY: ${API_KEY}" \
  -H "X-API-SECRET: ${API_SECRET}"
```

**Response data fields**: `{name, symbol, quotes, quotes_symbol, price, report_type, timestamp, signature[], prices[]}`

The `prices` array contains individual provider quotes: `{name, symbol, quotes, quotes_symbol, price, provider_name, direct_price, last_updated}`.

Note: `quotes` returns the full currency name (e.g., "United States Dollar"), and `quotes_symbol` returns the code (e.g., "USD").

---

### 4. List Categories — `GET /v2/ticker/currency/category/list`

**When to use**: User asks what coin categories exist, or wants to browse categories.

**Parameters**: None.

**Call pattern**:
```bash
curl -s -X GET "https://api-ai-oracle.apro.com/v2/ticker/currency/category/list" \
  -H "X-API-KEY: ${API_KEY}" \
  -H "X-API-SECRET: ${API_SECRET}"
```

**Response data**: Direct JSON array of `{name, title, description}` (data is the array itself, not `{categories: [...]}`)

---

### 5. Get Coins by Category — `GET /v2/ticker/currency/category/coins`

**When to use**: User asks which coins belong to a category (e.g., "show me DeFi coins").

**Parameters**:
| Param | Required | Default | Example |
|-------|----------|---------|---------|
| `category` | **Yes** | — | `Memes`, `Gaming`, `AI & Big Data` |

**IMPORTANT — Two-step process (ALWAYS required)**:

The `category` parameter takes the `name` field from the category/list response. You **must always** call **endpoint 4** (`category/list`) first, match the user's input against the returned entries, then use the exact `name` field value as the `category` parameter.

Example flow:
1. User says "show me Meme coins"
2. Call `category/list` → find entry `{"name": "Memes", "title": "Memes", ...}`
3. Use `category=Memes` (the exact `name` field value)

**Call pattern**:
```bash
# Step 1: Get category list and find the matching category name
CATEGORIES=$(curl -s -X GET "https://api-ai-oracle.apro.com/v2/ticker/currency/category/list" \
  -H "X-API-KEY: ${API_KEY}" \
  -H "X-API-SECRET: ${API_SECRET}")
# Find category name by matching user input (case-insensitive)
CATEGORY=$(echo "$CATEGORIES" | python3 -c "import sys,json; [print(c['name']) for c in json.load(sys.stdin).get('data',[]) if 'memes' in c.get('name','').lower()]")

# Step 2: Query coins with the resolved category
curl -s -X GET "https://api-ai-oracle.apro.com/v2/ticker/currency/category/coins?category=${CATEGORY}" \
  -H "X-API-KEY: ${API_KEY}" \
  -H "X-API-SECRET: ${API_SECRET}"
```

**Response data**: Direct JSON array of `{name, symbol, ...}` (data is the array itself)

---

### 6. Get OHLCV — `GET /v2/ticker/currency/ohlcv`

**When to use**: User asks for price history, candlestick data, charts, or historical data for a coin.

**Parameters**:
| Param | Required | Default | Example |
|-------|----------|---------|---------|
| `name` | **Yes** | — | `Bitcoin` |
| `quotation` | **Yes** | — | `USD` |
| `type` | No | `median` | `median`, `average` |
| `interval` | No | `daily` | `hourly`, `daily` |
| `start_timestamp` | **Yes** | — | `1704067200000` (Unix ms) |
| `end_timestamp` | **Yes** | — | `1706745599000` (Unix ms) |

**IMPORTANT**: Timestamps are in **milliseconds** (not seconds). To convert a date to milliseconds:
```bash
# Convert ISO date to Unix milliseconds
START_MS=$(date -d "2025-03-01" +%s)000   # Linux
START_MS=$(date -j -f "%Y-%m-%d" "2025-03-01" +%s)000  # macOS
```

**IMPORTANT**: Intervals are `"hourly"` or `"daily"`, NOT `"1h"` or `"1d"`.

**Call pattern**:
```bash
# Compute timestamps (e.g., last 7 days)
END_MS=$(date +%s)000
START_MS=$(( $(date +%s) - 7 * 86400 ))000

curl -s -X GET "https://api-ai-oracle.apro.com/v2/ticker/currency/ohlcv?name=Bitcoin&quotation=USD&type=median&interval=daily&start_timestamp=${START_MS}&end_timestamp=${END_MS}" \
  -H "X-API-KEY: ${API_KEY}" \
  -H "X-API-SECRET: ${API_SECRET}"
```

**Response data fields**: `{name, symbol, quotes, quotes_symbol, points[], report_type, signature[], ohlcvs[]}`

The response has TWO data sets:
- `data.points[]` — Aggregated OHLCV: `{open, high, low, close, volume, timestamp}` (timestamps in **seconds**)
- `data.ohlcvs[]` — Per-provider data, each with `{name, symbol, provider_name, direct, points[]}` where points have `{open, high, low, close, timestamp}` (no volume)

**Note**: Query params use **milliseconds** but response timestamps are in **seconds**.

---

## Environment Check

Before making any API call, verify that `curl` and `python3` are available:

```bash
command -v curl >/dev/null 2>&1 || { echo "curl is required but not installed."; }
command -v python3 >/dev/null 2>&1 || { echo "python3 is required but not installed."; }
```

If either is missing, tell the user what to install:
- **curl**: macOS/Linux usually pre-installed. Windows: `winget install cURL.cURL` or install Git for Windows (includes curl).
- **python3**: macOS: `brew install python3` or https://python.org/. Windows: `winget install Python.Python.3` or https://python.org/. Linux: `sudo apt install python3` / `sudo dnf install python3`.

Do not proceed until both tools are confirmed available.

## Request Execution Rules

1. **Always use `curl -s`** to suppress progress bars.
2. **Always include both auth headers** on every request.
3. **Parse response with `python3`** (pre-installed on macOS/Linux, no extra dependencies). Use `jq` only if you've confirmed it's available.
4. **Translate user symbols to full names**: Users will say "BTC" but the API needs "Bitcoin". Always translate before calling. **If the coin is NOT in the common mappings table above, you MUST call `currency/support?name=<best_guess>&restricted=relaxed` first** to resolve and verify the exact name before calling price or OHLCV endpoints.
5. **Check the response envelope first**: The API always returns a JSON envelope. Check `.status.code` before extracting data. Also guard against non-JSON responses:
   ```bash
   RESPONSE=$(curl -s -w "\n%{http_code}" -X GET "${URL}" \
     -H "X-API-KEY: ${API_KEY}" \
     -H "X-API-SECRET: ${API_SECRET}" \
     --connect-timeout 10 --max-time 30)

   # Split response body and HTTP status code
   HTTP_CODE=$(echo "$RESPONSE" | tail -1)
   BODY=$(echo "$RESPONSE" | sed '$d')

   # Guard: check if body is valid JSON
   if ! echo "$BODY" | python3 -c "import sys,json; json.load(sys.stdin)" 2>/dev/null; then
     echo "Error: API returned non-JSON response (HTTP $HTTP_CODE)"
     echo "$BODY"
     # Stop here — do not try to parse
   fi

   # Check API-level status
   API_CODE=$(echo "$BODY" | python3 -c "import sys,json; print(json.load(sys.stdin).get('status',{}).get('code',''))")

   if [ "$API_CODE" != "200" ]; then
     API_MSG=$(echo "$BODY" | python3 -c "import sys,json; print(json.load(sys.stdin).get('status',{}).get('message','Unknown error'))")
     echo "API Error $API_CODE: $API_MSG"
   else
     echo "$BODY" | python3 -c "import sys,json; print(json.dumps(json.load(sys.stdin).get('data'), indent=2))"
   fi
   ```
6. **Chain calls when needed**: When querying coins by category, you **must always** call the category list endpoint first (`category/list`), match the user's input against the entries, extract the exact `name` field value, then call `category/coins?category=<name>`. Never guess the category value — always look it up first.

## Output Formatting

Adapt the output format based on the data volume and user intent:

### Small data (≤ 10 items, e.g., price of a few coins)
Present directly in conversation as a readable table or summary. Example:

```
| Coin | Price (USD) | Report Type | Provider Count |
|------|-------------|-------------|----------------|
| Bitcoin | $67,432.15 | median | 3 providers |
```

Format numbers for readability: use `$`, `T`/`B`/`M` suffixes, and 2 decimal places for prices.

### Medium data (10-50 items, e.g., coins in a category)
Present a summary + top entries in conversation:

```
Found 245 coins in the DeFi category. Here are the first 10:
[table of first 10]
```

### Large data (> 50 items or OHLCV series)
Save to a file (CSV or JSON) and provide a link, plus a brief summary:

```bash
# Save OHLCV data as CSV — always include header row
echo "timestamp,open,high,low,close,volume" > ohlcv_data.csv
echo "$BODY" | python3 -c "
import sys,json,csv
data = json.load(sys.stdin).get('data',{}).get('points',[])
w = csv.writer(sys.stdout)
for p in data:
    w.writerow([p.get('timestamp',''),p.get('open',''),p.get('high',''),p.get('low',''),p.get('close',''),p.get('volume','')])
" >> ohlcv_data.csv
```

Then tell the user:
```
Fetched 90 daily candles for Bitcoin. Here's a summary:
- Range: $62,100 – $71,300
- Latest close: $68,200
[Full data saved to ohlcv_data.csv]
```

### When the user explicitly asks for JSON
Return the raw JSON, pretty-printed with `python3 -m json.tool`.

## Error Handling

Handle errors based on BOTH the HTTP status code (from curl) and the API-level status code (from the JSON envelope):

```
1. Is the response valid JSON?
   NO  → Report "API returned non-JSON response (HTTP <code>)" and stop
   YES → Continue

2. What is .status.code?
   200 → Extract .data and format output
   400 → Show .status.message, suggest user check parameters
   401 → Tell user: "Authentication failed. Please check your API key and secret."
         Do NOT retry — re-ask user for credentials
   429 → Retry once after 5 seconds. If still 429:
         Tell user: "Rate limit hit. Please wait a moment and try again."
   5xx → Retry once after 3 seconds. If still failing:
         Tell user: "Server error (<code>). The API may be temporarily down."
```

**Complete retry pattern**:
```bash
call_api() {
  local URL="$1"
  local RESPONSE BODY HTTP_CODE API_CODE

  RESPONSE=$(curl -s -w "\n%{http_code}" -X GET "${URL}" \
    -H "X-API-KEY: ${API_KEY}" \
    -H "X-API-SECRET: ${API_SECRET}" \
    --connect-timeout 10 --max-time 30)

  HTTP_CODE=$(echo "$RESPONSE" | tail -1)
  BODY=$(echo "$RESPONSE" | sed '$d')

  # Non-JSON guard
  if ! echo "$BODY" | python3 -c "import sys,json; json.load(sys.stdin)" 2>/dev/null; then
    echo "ERROR: Non-JSON response (HTTP $HTTP_CODE)"
    return 1
  fi

  API_CODE=$(echo "$BODY" | python3 -c "import sys,json; print(json.load(sys.stdin).get('status',{}).get('code',''))")

  # 401: no retry, credential issue
  if [ "$API_CODE" = "401" ]; then
    echo "AUTH_ERROR"
    return 1
  fi

  # 429: retry once after 5s
  if [ "$API_CODE" = "429" ]; then
    sleep 5
    RESPONSE=$(curl -s -w "\n%{http_code}" -X GET "${URL}" \
      -H "X-API-KEY: ${API_KEY}" -H "X-API-SECRET: ${API_SECRET}" \
      --connect-timeout 10 --max-time 30)
    HTTP_CODE=$(echo "$RESPONSE" | tail -1)
    BODY=$(echo "$RESPONSE" | sed '$d')
    API_CODE=$(echo "$BODY" | python3 -c "import sys,json; print(json.load(sys.stdin).get('status',{}).get('code',''))")
  fi

  # 5xx: retry once after 3s
  if [ "$API_CODE" -ge 500 ] 2>/dev/null; then
    sleep 3
    RESPONSE=$(curl -s -w "\n%{http_code}" -X GET "${URL}" \
      -H "X-API-KEY: ${API_KEY}" -H "X-API-SECRET: ${API_SECRET}" \
      --connect-timeout 10 --max-time 30)
    HTTP_CODE=$(echo "$RESPONSE" | tail -1)
    BODY=$(echo "$RESPONSE" | sed '$d')
    API_CODE=$(echo "$BODY" | python3 -c "import sys,json; print(json.load(sys.stdin).get('status',{}).get('code',''))")
  fi

  # Final check
  if [ "$API_CODE" != "200" ]; then
    echo "$BODY" | python3 -c "import sys,json; print(json.load(sys.stdin).get('status',{}).get('message','Unknown error'))"
    return 1
  fi

  echo "$BODY" | python3 -c "import sys,json; print(json.dumps(json.load(sys.stdin).get('data'), indent=2))"
  return 0
}
```

## Interpreting User Requests — Examples

| User says | Endpoint(s) to call | Parameters |
|-----------|---------------------|------------|
| "BTC price" | price | `name=Bitcoin&quotation=USD` |
| "How much is ETH?" | price | `name=Ethereum&quotation=USD` |
| "What coins do you support?" | currencies/list | `page=1&size=50` |
| "Is Solana supported?" | currency/support | `name=Solana&restricted=relaxed` |
| "Top DeFi coins" | category/list → category/coins | Resolve via category/list `name` field → `category=<exact name>`, then query |
| "What categories are there?" | category/list | (none) |
| "BTC daily chart" | ohlcv | `name=Bitcoin&interval=daily` |
| "ETH hourly data" | ohlcv | `name=Ethereum&interval=hourly` |
| "Compare BTC and ETH" | price × 2 | Call price for Bitcoin, then for Ethereum |
| "SOL price history last week" | ohlcv | `name=Solana&interval=daily&start_timestamp=<7 days ago ms>&end_timestamp=<now ms>` |
| "TON price history" | support → ohlcv | First `currency/support?name=Toncoin&restricted=relaxed`, then ohlcv with resolved name |
