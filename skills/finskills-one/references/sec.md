# SEC EDGAR Reference

Direct SEC EDGAR pass-through. Use **CIK** (Central Index Key) — leading zeros optional, but pad to 10 digits when in doubt.

## Common CIKs

| Company | CIK |
|---------|-----|
| Apple | `0000320193` |
| Microsoft | `0000789019` |
| Amazon | `0001018724` |
| Alphabet (Google) | `0001652044` |
| Meta | `0001326801` |
| Tesla | `0001318605` |
| NVIDIA | `0001045810` |
| Berkshire Hathaway | `0001067983` |
| JPMorgan | `0000019617` |
| Exxon Mobil | `0000034088` |

To look up an unknown CIK, use `/v1/stocks/search?q=<name>` or hit SEC's company tickers JSON.

## Endpoints

### `GET /v1/free/sec/filings/{cik}`
Recent filings (10-K, 10-Q, 8-K, S-1, DEF 14A, Form 4, …).

Query (optional): `type=10-K`, `limit=20`.

`data`: `[ { accessionNumber, formType, filingDate, reportDate, primaryDocument, fileUrl } ]`.

### `GET /v1/free/sec/company-facts/{cik}`
XBRL-tagged GAAP facts for the company (revenues, EPS, assets, liabilities, …). Heavy payload — filter on the client by concept.

### `GET /v1/free/sec/insider-trades/{symbol}`
Form 3/4/5 insider transactions for a ticker.

`data`: `[ { name, title, transactionDate, transactionType, shares, pricePerShare, valueUsd, sharesOwnedAfter } ]`.

### `GET /v1/free/sec/insider-summary/{symbol}`
90-day rollup: total insider buys vs sells, net activity, top insiders.

### `GET /v1/free/sec/ownership/{symbol}` *(P3)*
Aggregated 13F institutional ownership.

`data`: `[ { fundName, sharesHeld, percentOfPortfolio, changeQoQ, asOf } ]`.

## Patterns

- **Latest 10-K**: filings → filter `formType="10-K"` → take first → fetch `primaryDocument` URL.
- **Earnings drill**: filings type `8-K` recent + `10-Q` recent + insider-summary for context.
- **Fundamentals from XBRL**: company-facts is preferred when you need exact, source-of-truth GAAP numbers; Yahoo `/v1/stocks/financials` is more convenient.
