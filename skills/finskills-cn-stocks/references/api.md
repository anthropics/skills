# China A-share API reference

Base URL: `https://finskills.net`
Authentication: `X-API-Key` header on every request.

## Symbols

Use a six-digit mainland security code. Accepted examples include `600519`, `000001`, `300750`, `600519.SH`, and `000001.SZ`. The API returns a normalized suffixed symbol.

## Endpoints

### Quote

`GET /v1/stocks/quote/{symbol}`

Returns symbol identity and the latest available price record. Important fields include `symbol`, `name`, `exchange`, `asset_type`, `currency`, `price`, `change`, `change_percent`, `open`, `high`, `low`, `volume`, `amount`, `timestamp`, `interval`, and `source`.

```bash
curl -H "X-API-Key: $FINSKILLS_API_KEY" \
  "https://finskills.net/v1/stocks/quote/600519"
```

### Batch quotes

`GET /v1/stocks/quotes?symbols={csv}`

- `symbols` (required): comma-separated A-share codes.

Returns an array of quote objects. Do not assume all returned records share the same timestamp or interval.

### History

`GET /v1/stocks/history/{symbol}`

| Parameter | Values | Default |
|---|---|---|
| `interval` | `1d`, `30m`, `60m` | `1d` |
| `adjustment` | `none`, `qfq`, `hfq` | `qfq` |
| `from` | `YYYY-MM-DD` | optional |
| `to` | `YYYY-MM-DD` | optional |
| `limit` | integer, 1–10000 | 1000 |
| `offset` | non-negative integer | 0 |

The response contains `symbol`, `interval`, `adjustment`, `currency`, `timezone`, `count`, and `data`. Each data row can include `timestamp`, `open`, `high`, `low`, `close`, `volume`, `amount`, and `source`.

```bash
curl -H "X-API-Key: $FINSKILLS_API_KEY" \
  "https://finskills.net/v1/stocks/history/600519?interval=1d&adjustment=qfq&from=2026-01-01&limit=100"
```

### Search

`GET /v1/stocks/search?q={query}&limit={limit}`

- `q` (required): company name or security code.
- `limit`: 1–100, default 20.

Use this endpoint to resolve ambiguous Chinese names before requesting market data.

### Profile

`GET /v1/stocks/profile/{symbol}`

Returns listing identity such as `symbol`, `code`, `name`, `exchange`, `asset_type`, `category`, `status`, `source`, and provider-specific `details`.

### Financials

`GET /v1/stocks/financials/{symbol}?freq={freq}&limit={limit}`

- `freq`: `yearly` or `quarterly`, default `yearly`.
- `limit`: 1–200, default 40.

Returns a dataset envelope with `symbol`, `dataset`, `source`, `count`, and `data`.

### Other datasets

The following endpoints accept an optional `limit` from 1–1000, default 100, and return the same dataset envelope:

- `GET /v1/stocks/dividends/{symbol}`
- `GET /v1/stocks/options/{symbol}`
- `GET /v1/stocks/holders/{symbol}`
- `GET /v1/stocks/recommendations/{symbol}`
- `GET /v1/stocks/earnings/{symbol}`

An empty dataset is a successful response, not evidence that the company has no corresponding events. Say only that the provider returned no rows.

## Adjustment modes

- `none`: raw, unadjusted prices.
- `qfq`: forward-adjusted prices (前复权), useful for recent-price-aligned return charts.
- `hfq`: backward-adjusted prices (后复权), useful for long-run wealth-series continuity.

Never combine series with different adjustment modes in one return calculation.

## Errors

- `401`: missing or invalid Finskills API key.
- `403`: plan or quota restriction.
- `404`: symbol or endpoint not found.
- `422`: invalid parameter format or range.
- `429`: rate limited; respect retry information if provided.
- `5xx`: service or upstream failure; retry once for transient research tasks.
