# Cryptocurrency Reference

Backed by CoinGecko (primary) with Binance and CoinPaprika fallback. Use **CoinGecko coin IDs** (lowercase slugs), not tickers.

| Coin | ID |
|------|----|
| Bitcoin | `bitcoin` |
| Ethereum | `ethereum` |
| Solana | `solana` |
| Binance Coin | `binancecoin` |
| Ripple | `ripple` |
| Cardano | `cardano` |
| Dogecoin | `dogecoin` |
| Polkadot | `polkadot` |
| USDT | `tether` |
| USDC | `usd-coin` |

## Endpoints

### `GET /v1/free/crypto/price/{coinId}`
Current price + 24h change + market cap.

```bash
curl -H "X-API-Key: $KEY" https://finskills.net/v1/free/crypto/price/bitcoin
```

`data`: `{ id, symbol, name, price, marketCap, volume24h, change24h, changePercent24h, lastUpdated, currency }` (default `vs_currency=usd`; pass `?vs_currency=eur|cny|jpy` etc.).

### `GET /v1/free/crypto/markets`
Top coins ranked by market cap.

Query: `vs_currency` (default `usd`), `limit` (default `20`, max `250`), `page`.

### `GET /v1/free/crypto/history/{coinId}`
Historical prices.

Query: `days` ∈ `1, 7, 14, 30, 90, 180, 365, max`. Returns sparse arrays:

```json
{
  "prices":      [ [timestampMs, price], ... ],
  "marketCaps":  [ [timestampMs, mcap], ... ],
  "totalVolumes":[ [timestampMs, vol], ... ]
}
```

### Premium aliases (`/v1/crypto/...`)
Same shape, identical paths under `/v1/crypto/...` if you specifically want premium routing. Prefer free.

## Patterns

- **Compare two coins**: parallel-fetch `history/{a}?days=30` and `history/{b}?days=30`, normalize to first close = 100, plot.
- **Top 10 dashboard**: `markets?limit=10`, render as table.
- **Convert FX → crypto**: hit `/v1/free/forex/rates?base=USD&symbols=EUR` then crypto `price` with `vs_currency=eur`, or compute client-side.
