---
name: ai-oracle-integration
description: "Generate production-ready client code for integrating with the APRO AI Oracle Ticker API (cryptocurrency price, category, OHLCV endpoints). Supported languages: TypeScript, Python, Go, Rust. Use when a customer needs ticker/crypto integration code. Triggers on mentions of ticker, crypto price, OHLCV, coin category, APRO Oracle, or requests for cryptocurrency data API clients."
argument-hint: "<language> (e.g., typescript, python, go, rust)"
allowed-tools: Read, Grep, Glob, Write, Bash
---

# AI Oracle Ticker Integration Code Generator

Generate a complete, production-ready client library for the **APRO AI Oracle Ticker** API in the requested language.

## Arguments

- `$ARGUMENTS` — Target language (e.g., "typescript", "python", "go", "rust")
- **Supported languages**: TypeScript, Python, Go, Rust. If the user requests an unsupported language, inform them of the supported options.
- If no language is specified, ask the user which language they want.

## Instructions

1. Read this skill document fully before generating any code
2. **Read the OpenAPI spec** at `references/ai-oracle-api.yaml` — this is the authoritative source for all endpoint paths, parameters, request/response schemas, and field types. All generated type definitions and method signatures must match this spec exactly.
3. Generate a complete client library following the **Mandatory Directory Structure** below
4. Write the output to `examples/<language>/ticker/` directory
5. **Run compilation verification** — execute the language-appropriate compile/check command (see **Compilation Verification** section). If it fails, read the error output, fix the source files, and re-run until zero errors. This step is mandatory and the output is not considered complete until compilation passes.

## API Quick Reference

> The full specification lives in `references/ai-oracle-api.yaml`. This section is a condensed overview for quick orientation — when in doubt, the YAML is the source of truth.

- **Base URL**: `https://api-ai-oracle.apro.com`
- **Auth**: Two headers on every request — `X-API-KEY` and `X-API-SECRET`
- **Response envelope**: `{ "status": { "code", "message", "timestamp" }, "data": { ... } }`

### IMPORTANT: Parameter Naming Convention

This API uses **full currency names** (e.g., `"Bitcoin"`, `"Ethereum"`), NOT ticker symbols.

| Common Pattern | This API |
|---------------|----------|
| `symbol=BTC` | `name=Bitcoin` |
| `currency=USD` | `quotation=USD` |
| `interval=1d` | `interval=daily` |
| `start`/`end` (seconds) | `start_timestamp`/`end_timestamp` (milliseconds) |
| `category_id=defi` | `category=defi` |

### Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/v2/ticker/currencies/list` | GET | List all supported currencies (paginated) |
| `/v2/ticker/currency/support` | GET | Check if a specific currency is supported |
| `/v2/ticker/currency/price` | GET | Current price for a cryptocurrency |
| `/v2/ticker/currency/category/list` | GET | List all coin categories |
| `/v2/ticker/currency/category/coins` | GET | Coins in a specific category |
| `/v2/ticker/currency/ohlcv` | GET | OHLCV candlestick data (start_timestamp required) |

### Response Data Shapes

Some endpoints return a **direct array** as `data`, not a wrapped object:

| Endpoint | `data` field type |
|----------|------------------|
| `/v2/ticker/currencies/list` | Direct array: `[{name, symbol, ...}, ...]` |
| `/v2/ticker/currency/support` | Single object: `{name, symbol, ...}` |
| `/v2/ticker/currency/price` | Single object: `{name, symbol, price, signature[], prices[], ...}` |
| `/v2/ticker/currency/category/list` | Direct array: `[{name, title, description}, ...]` |
| `/v2/ticker/currency/category/coins` | Direct array: `[{name, symbol}, ...]` |
| `/v2/ticker/currency/ohlcv` | Single object: `{name, symbol, points[], ohlcvs[], signature[], ...}` |

### OHLCV Response Structure

The OHLCV response has TWO sets of data points:
- `data.points[]` — **Aggregated** OHLCV with `open, high, low, close, volume, timestamp` (timestamps in seconds)
- `data.ohlcvs[]` — **Per-provider** data, each with `provider_name`, `direct`, and its own `points[]` (no volume field)

Query parameters `start_timestamp`/`end_timestamp` use **milliseconds**, but response `timestamp` fields are in **seconds**.

### Key Schema Names (from YAML)

| YAML Schema | Maps to Generated Type |
|-------------|----------------------|
| `ApiStatus` | `ApiStatus` |
| `CurrencyInfo` | `CurrencyInfo` |
| `CurrencySupportResponse` | `CurrencySupport` |
| `TickerPriceData` | `TickerPrice` |
| `CategoryInfo` | `CategoryInfo` |
| `CategoryCoin` | `CategoryCoin` |
| `OHLCVData` | `OHLCVData` |
| `OHLCVEntry` | `OHLCVEntry` |
| `SignatureEntry` | `SignatureEntry` |
| `ProviderPrice` | `ProviderPrice` |
| `Wrapped_*Response` | `ApiResponse<T>` (generic envelope) |
| `ErrorResponse` | `TickerApiError` (error class) |

When generating types, read each schema's `properties` and `required` fields from the YAML — do not guess or hardcode field names.

---

## Mandatory Directory Structure

Every generated project MUST follow this exact directory layout. This is critical for consistency — do not deviate from this structure regardless of the target language.

```
examples/<language>/ticker/
├── src/
│   ├── types/          # All type/model definitions
│   │   └── index.<ext> # TickerPrice, CategoryInfo, CategoryCoin, OHLCV, ApiResponse, ApiStatus, etc.
│   ├── client/         # HTTP client and API method implementations
│   │   └── index.<ext> # TickerClient class with all 6 endpoint methods
│   └── utils/          # Shared utilities
│       └── index.<ext> # Error handling, retry logic, response parsing, helpers
├── examples/
│   └── index.<ext>     # Runnable usage examples for all 6 endpoints
├── .env.example        # Template: APRO_API_KEY=your_api_key_here, APRO_API_SECRET=your_api_secret_here
└── README.md           # Setup instructions, API reference, usage guide
```

### File Extension Mapping

| Language | `<ext>` | Notes |
|----------|---------|-------|
| TypeScript | `.ts` | Use `tsconfig.json` at root if needed |
| Python | `.py` | Use `__init__.py` in each `src/` subdirectory |
| Go | `.go` | Use `go.mod` at root; packages = directory names |
| Rust | `.rs` | Use `Cargo.toml` at root; `src/` is standard |

### Language-Specific Adaptations

While the directory structure is fixed, each language should adapt idiomatically:

- **Python**: Add `__init__.py` files in each `src/` subdirectory for proper package imports. Use `httpx` for async HTTP, `dataclasses` for models, type hints everywhere. Include `requirements.txt` at root.
- **TypeScript**: Use `interface` for types, `async/await` with `fetch`. Include `package.json`, `tsconfig.json`, and `.env.example` at root. **Critical tsconfig requirements**: `"lib": ["ES2020", "DOM"]` (for `fetch`/`Response`/`RequestInit`/`AbortSignal`), `@types/node` in devDependencies (for `process`/`console`/`setTimeout`), `"rootDir": "."`, `"include": ["src/**/*", "examples/**/*"]`. **Critical .env setup**: Add `dotenv` to dependencies and `@types/node` to devDependencies. In example files, call `import 'dotenv/config'` at the top (or `import dotenv from 'dotenv'; dotenv.config()`) so `process.env.APRO_API_KEY` / `process.env.APRO_API_SECRET` are loaded from `.env`. Generate a `.env.example` file containing `APRO_API_KEY=your_api_key_here` and `APRO_API_SECRET=your_api_secret_here`. The tsconfig.json must set `"resolveJsonModule": true` and `"esModuleInterop": true`.
- **Go**: Use Go modules. Struct tags for JSON. Package names match directory names. Include `go.mod` at root. All exported functions must have doc comments.
- **Rust**: Use `reqwest` (with `json` feature) for HTTP, `serde`/`serde_json` for serialization, `tokio` for async runtime. Include `Cargo.toml` at root.

---

## Code Generation Rules

These rules ensure every generated client is production-quality and structurally consistent. Type definitions and method signatures must be derived from the OpenAPI YAML — not invented.

### 1. Type Definitions (`src/types/`)

Read the `components/schemas` section of the YAML and generate types for ALL of the following:

| YAML Schema | Generated Type | Key Fields |
|-------------|---------------|------------|
| `ApiStatus` | `ApiStatus` | `code`, `message`, `timestamp` |
| (generic) | `ApiResponse<T>` | `status: ApiStatus`, `data: T` |
| `CurrencyInfo` | `CurrencyInfo` | `name`, `symbol`, `keywords`, `support_providers` |
| `CurrencySupportResponse` | `CurrencySupport` | `name`, `symbol`, `keywords`, `support_providers` |
| `SignatureEntry` | `SignatureEntry` | `signer`, `hash`, `signature`, `timestamp` |
| `ProviderPrice` | `ProviderPrice` | `name`, `symbol`, `quotes`, `quotes_symbol`, `price`, `provider_name`, `direct_price`, `last_updated` |
| `TickerPriceData` | `TickerPrice` | `name`, `symbol`, `quotes`, `quotes_symbol`, `price`, `report_type`, `timestamp`, `signature`, `prices` |
| `CategoryInfo` | `CategoryInfo` | `name`, `title`, `description` |
| `CategoryCoin` | `CategoryCoin` | `name`, `symbol`, `quotes?`, `quotes_symbol?`, `providers?`, `price?`, `market_cap?`, `volume_24h?`, `percent_change_1h?`, `percent_change_24h?`, `percent_change_7d?`, `percent_change_30d?`, `percent_change_60d?`, `percent_change_90d?`, `last_updated?` |
| `OHLCVEntry` | `OHLCVEntry` | `open`, `high`, `low`, `close`, `volume`, `timestamp` |
| `OHLCVData` | `OHLCVData` | `name`, `symbol`, `quotes`, `quotes_symbol`, `points`, `report_type`, `signature`, `ohlcvs` |

Use the language's idiomatic type system (interfaces, structs, dataclasses, etc.). All fields must have explicit types — no `any` or `interface{}`. Field types (string, number, integer, etc.) should match the YAML's `type` and `format` attributes.

### 2. Client Class (`src/client/`)

Read the `paths` section of the YAML. Each path maps to exactly one client method:

| YAML Path | Method | Signature Pattern |
|-----------|--------|------------------|
| `/v2/ticker/currencies/list` | `listCurrencies` | `(page?: number, size?: number) → CurrencyInfo[]` |
| `/v2/ticker/currency/support` | `checkSupport` | `(name: string, restricted: string = "relaxed") → CurrencySupport` — **always pass `restricted=relaxed`** |
| `/v2/ticker/currency/price` | `getPrice` | `(name: string, quotation: string, type?: string) → TickerPrice` |
| `/v2/ticker/currency/category/list` | `getCategoryList` | `() → CategoryInfo[]` |
| `/v2/ticker/currency/category/coins` | `getCategoryCoins` | `(category: string) → CategoryCoin[]` |
| `/v2/ticker/currency/ohlcv` | `getOHLCV` | `(name: string, quotation: string, startTimestamp: number, opts?: { type?, interval?, endTimestamp? }) → OHLCVData` |

**Note**: `startTimestamp` is **required** for OHLCV. The API returns error 400 if not provided.

Method parameters must match the YAML's `parameters` (name, type, required). Adapt naming to language conventions (e.g., `get_price` in Python, `GetPrice` in Go), but the set of 6 methods must always be present.

**CRITICAL**: Parameters use `name` (full crypto name like "Bitcoin"), NOT `symbol`. The `quotation` param is the quote currency, NOT `currency`. OHLCV intervals are `"hourly"`/`"daily"`, NOT `"1h"`/`"1d"`. OHLCV timestamps are in **milliseconds**, NOT seconds.

Client constructor accepts:
```
{
  baseUrl?: string     // default: "https://api-ai-oracle.apro.com"
  apiKey: string
  apiSecret: string
  timeout?: number     // default: 30000ms
  maxRetries?: number  // default: 3
}
```

### 3. Utilities (`src/utils/`)

Must include:
- **Custom error class** with fields: `statusCode`, `message`, `timestamp` (derived from YAML's `ErrorResponse` schema)
- **Retry logic**: exponential backoff on 429 and 5xx, up to `maxRetries`
- **Response parser**: unwrap the `{ status, data }` envelope (the `Wrapped_*` pattern in YAML), throw on non-200 status codes. **CRITICAL**: The `data` field has different shapes per endpoint — it can be a direct array (for `currencies/list`, `category/list`, `category/coins`) or a single object (for `support`, `price`, `ohlcv`). The parser must handle both: when `data` is an array, return the array directly; when it's an object, return the object. Never assume `data` is always one shape.
- **Request builder**: construct URL with query params, attach auth headers (`X-API-KEY`, `X-API-SECRET`)

### 4. Examples (`examples/`)

Provide a single runnable example file that demonstrates ALL 6 endpoints:
1. List supported currencies (first page)
2. Check if "Bitcoin" is supported
3. Fetch Bitcoin price (in USD, median)
4. List all categories
5. Get coins in a specific category
6. Fetch Bitcoin OHLCV data (daily)

Each example call must include inline comments explaining what it does. The example must be copy-paste runnable. For TypeScript/Node.js, read credentials from `process.env` (loaded via `dotenv`) — the user only needs to copy `.env.example` to `.env` and fill in their keys. For Python, use `os.environ` (with `python-dotenv`). For other languages, use idiomatic env-var loading.

**CRITICAL — Example robustness rules** (these prevent runtime errors in generated examples):

1. **Always guard array operations**: Before calling `.length`, `.slice()`, `.map()`, `.forEach()`, or any array method on API results, check that the value is defined and is an array. Use `Array.isArray(result)` (TypeScript) or equivalent.
2. **Log the right properties per endpoint**: Each endpoint returns different fields. For `category/list`, log `name`/`title`. For `category/coins`, log `name`/`symbol`/`price`. For `currencies/list`, log `name`/`symbol`. Do NOT assume all array responses have the same shape.
3. **Wrap each endpoint demo in its own try/catch**: One failing endpoint must NOT crash the entire example. Catch errors per-call and log them, then continue to the next endpoint.
4. **OHLCV timestamps**: When constructing `start_timestamp` for OHLCV, always use `Date.now() - 7 * 24 * 60 * 60 * 1000` (7 days ago in ms). Do NOT hardcode dates that will expire.
5. **Never use `.slice()` or index access without a guard**: `if (data && data.length > 0) { console.log(data.slice(0, 5)); }` — not `console.log(data.slice(0, 5))` directly.
6. **For `category/coins`**: Always use a known category like `"Memes"`. The category name must exactly match a value from `category/list` — it is case-sensitive.

### 5. README.md

Must contain these exact sections in order:
1. **Installation** — Dependencies and setup steps
2. **Quick Start** — Minimal code to get a price quote
3. **API Reference** — Table of all 6 methods with params and return types
4. **Configuration** — Client options (baseUrl, timeout, retries)
5. **Error Handling** — How errors are structured and how to catch them
6. **Examples** — Reference to the examples directory

---

## Pre-Generation Checklist

Before writing any file, verify mentally:

- [ ] Have I read `references/ai-oracle-api.yaml`?
- [ ] Target directory is `examples/<language>/ticker/`
- [ ] All 4 directories exist: `src/types/`, `src/client/`, `src/utils/`, `examples/`
- [ ] All type definitions will be generated (matching YAML schemas)
- [ ] All 6 client methods will be generated (matching YAML paths)
- [ ] Utils includes: error class, retry, response parser, request builder
- [ ] Example file covers all 6 endpoints
- [ ] README has all 6 required sections
- [ ] Language-specific config file is included (package.json, requirements.txt, go.mod, Cargo.toml, etc.)
- [ ] Parameters use `name`/`quotation` (NOT `symbol`/`currency`)
- [ ] OHLCV intervals are `"hourly"`/`"daily"` (NOT `"1h"`/`"1d"`)
- [ ] OHLCV timestamps are milliseconds (NOT seconds)

## Post-Generation Checklist

After writing all files, verify:

- [ ] No placeholder or TODO comments left in the code
- [ ] All imports/requires resolve correctly between the files
- [ ] Error handling is consistent across all 6 methods
- [ ] Auth headers are set on every request
- [ ] Response envelope unwrapping is applied everywhere
- [ ] Retry logic covers all 6 methods (not just some)
- [ ] Parameter names match the API exactly (`name`, `quotation`, `type`, `interval`, `start_timestamp`, `end_timestamp`, `category`)

## Compilation Verification (MANDATORY)

This step is **not optional**. The generated code must compile/pass static checks before delivery. Follow this exact procedure:

### Step 0: Check Environment

Before generating code, verify the target language toolchain is installed. Run the check command and inspect the output:

| Language | Check Command | If Missing |
|----------|--------------|------------|
| TypeScript | `node --version && npm --version` | Ask user to install Node.js from https://nodejs.org/ |
| Python | `python3 --version` | Ask user to install Python from https://python.org/ |
| Go | `go version` | Ask user to install Go from https://go.dev/dl/ |
| Rust | `cargo --version` | Ask user to install Rust via `curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \| sh` or from https://rustup.rs/ |

If the check command fails, **stop and tell the user** what to install before proceeding. Do not attempt code generation or compilation without a working toolchain.

### Step 1: Install Dependencies

`cd` into the generated project root (`examples/<language>/ticker/`) and install dependencies:

| Language | Install Command |
|----------|----------------|
| TypeScript | `npm install` |
| Python | `pip install -r requirements.txt --break-system-packages` (if httpx not available) |
| Go | `go mod tidy` |
| Rust | (cargo check handles this) |

### Step 2: Run Compilation Check

| Language | Verification Command | Success Criteria |
|----------|---------------------|-----------------|
| TypeScript | `npx tsc --noEmit` | Exit code 0, no output |
| Python | `python3 -m py_compile src/types/index.py && python3 -m py_compile src/client/index.py && python3 -m py_compile src/utils/index.py && python3 -m py_compile examples/index.py` | Exit code 0 for all files |
| Go | `go build ./... && go vet ./...` | Exit code 0, no output |
| Rust | `cargo check` | Exit code 0 |

### Step 3: Auto-Fix Loop

If compilation fails, follow this loop — up to 3 iterations maximum:

```
for each attempt (1 to 3):
    1. Read the FULL error output from the compilation command
    2. Identify the root cause of EVERY error (not just the first one)
    3. Fix all errors in the source files
    4. Re-run the compilation command from Step 2
    5. If exit code is 0 → done, proceed to delivery
    6. If still failing → next attempt
```

After 3 failed attempts, report the remaining errors to the user and ask for guidance.

**Important**: Fix the root cause, not the symptom. For example, if `fetch` is not found in TypeScript, don't add `declare function fetch(...)` — instead fix `tsconfig.json` to include the `DOM` lib.

### Common Pitfalls by Language

**TypeScript** (most common source of example.ts errors):
- `Cannot find name 'fetch'/'Response'/'RequestInit'/'AbortSignal'` → Add `"DOM"` to `tsconfig.json` `lib` array
- `Cannot find name 'process'/'console'/'setTimeout'` → Add `@types/node` to devDependencies and run `npm install`
- `File 'examples/index.ts' is not under 'rootDir'` → Set `"rootDir": "."` (not `"./src"`) and add `"examples/**/*"` to `include`
- `Cannot find module '../types/index'` → Check relative import paths match actual directory structure
- `Cannot find module 'dotenv/config'` → Add `dotenv` to dependencies (not just devDependencies) and `@types/node` to devDependencies, then `npm install`
- `Type 'string | undefined' is not assignable to type 'string'` → When reading `process.env`, always provide a fallback or assert: `process.env.APRO_API_KEY || ''` or use a guard that throws if missing
- Top-level `await` error → **Do NOT use top-level await in examples**. Always wrap example code in an `async function main()` and call `main().catch(console.error)` at the bottom
- `esModuleInterop` errors with `import dotenv from 'dotenv'` → Use `import 'dotenv/config'` (side-effect import) instead, which works without `esModuleInterop`; OR ensure `"esModuleInterop": true` is in tsconfig

**Required TypeScript tsconfig.json template** — always generate exactly this (adjust `target`/`module` only if necessary):
```json
{
  "compilerOptions": {
    "target": "ES2020",
    "module": "commonjs",
    "lib": ["ES2020", "DOM"],
    "outDir": "./dist",
    "rootDir": ".",
    "strict": true,
    "esModuleInterop": true,
    "resolveJsonModule": true,
    "skipLibCheck": true,
    "forceConsistentCasingInFileNames": true,
    "moduleResolution": "node",
    "declaration": true
  },
  "include": ["src/**/*", "examples/**/*"],
  "exclude": ["node_modules", "dist"]
}
```

**Required TypeScript examples/index.ts structure** — always follow this pattern:
```typescript
import 'dotenv/config';
import { TickerClient } from '../src/client';

const apiKey = process.env.APRO_API_KEY;
const apiSecret = process.env.APRO_API_SECRET;

if (!apiKey || !apiSecret) {
  console.error('Missing APRO_API_KEY or APRO_API_SECRET in .env');
  process.exit(1);
}

const client = new TickerClient({ apiKey, apiSecret });

async function main(): Promise<void> {
  // 1. List currencies
  try {
    const currencies = await client.listCurrencies(1, 10);
    console.log(`[OK] Listed ${Array.isArray(currencies) ? currencies.length : 0} currencies`);
    if (Array.isArray(currencies) && currencies.length > 0) {
      console.log('  First:', currencies[0].name, currencies[0].symbol);
    }
  } catch (err) {
    console.error('[FAIL] listCurrencies:', err);
  }

  // 2. Check support
  try {
    const support = await client.checkSupport('Bitcoin', 'relaxed');
    console.log(`[OK] Support: ${support.name} (${support.symbol})`);
  } catch (err) {
    console.error('[FAIL] checkSupport:', err);
  }

  // 3. Get price
  try {
    const price = await client.getPrice('Bitcoin', 'USD', 'median');
    console.log(`[OK] Price: ${price.name} = $${price.price}`);
  } catch (err) {
    console.error('[FAIL] getPrice:', err);
  }

  // 4. List categories
  try {
    const categories = await client.getCategoryList();
    console.log(`[OK] Categories: ${Array.isArray(categories) ? categories.length : 0} found`);
    if (Array.isArray(categories) && categories.length > 0) {
      console.log('  First:', categories[0].name);
    }
  } catch (err) {
    console.error('[FAIL] getCategoryList:', err);
  }

  // 5. Get category coins
  try {
    const coins = await client.getCategoryCoins('Memes');
    console.log(`[OK] Memes coins: ${Array.isArray(coins) ? coins.length : 0} found`);
    if (Array.isArray(coins) && coins.length > 0) {
      console.log('  First:', coins[0].name, coins[0].symbol);
    }
  } catch (err) {
    console.error('[FAIL] getCategoryCoins:', err);
  }

  // 6. OHLCV (last 7 days)
  try {
    const now = Date.now();
    const weekAgo = now - 7 * 24 * 60 * 60 * 1000;
    const ohlcv = await client.getOHLCV('Bitcoin', 'USD', weekAgo, { endTimestamp: now, interval: 'daily' });
    const pointCount = Array.isArray(ohlcv.points) ? ohlcv.points.length : 0;
    console.log(`[OK] OHLCV: ${pointCount} data points`);
    if (pointCount > 0) {
      console.log('  Latest close:', ohlcv.points[ohlcv.points.length - 1].close);
    }
  } catch (err) {
    console.error('[FAIL] getOHLCV:', err);
  }
}

main().catch(console.error);
```

**Python**:
- `ModuleNotFoundError` → Ensure `__init__.py` exists in every `src/` subdirectory
- Circular imports → Move shared types to `src/types/`, import from there in both client and utils
- `httpx` not installed → Include in `requirements.txt`, install before verification
- `KeyError: 'r'` or `missing key 'r'` on signature → **SignatureEntry fields are `signer`, `hash`, `signature`, `timestamp`** (NOT `r`, `s`, `v`). Always derive types from the YAML `SignatureEntry` schema.

**Go**:
- `imported and not used` → Remove unused imports or use `_` blank identifier
- `undefined: SomeType` → Check package names match directory names, ensure exports are capitalized
- `go.mod: missing module` → Run `go mod tidy` before `go build`

**Rust**:
- `unresolved import reqwest` → Ensure `reqwest = { version = "0.11", features = ["json"] }` in Cargo.toml
- `the trait bound 'X: Deserialize' is not satisfied` → Add `#[derive(Deserialize)]` and `use serde::Deserialize`
- `tokio runtime` → Ensure `tokio = { version = "1", features = ["full"] }` in Cargo.toml
- `missing field 'r'` on deserialization → **SignatureEntry fields are `signer`, `hash`, `signature`, `timestamp`** (NOT `r`, `s`, `v`). The struct must match the YAML schema exactly. Use `#[serde(rename_all = "snake_case")]` if needed.
