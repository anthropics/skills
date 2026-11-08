# News Reference

## Endpoints

| Endpoint | Source | Use |
|----------|--------|-----|
| `GET /v1/free/news/finance` | Google News RSS aggregator | General financial news |
| `GET /v1/news/latest` | Marketaux (premium) | Curated market news |
| `GET /v1/news/by-symbol/{symbol}` | Marketaux | News for a specific ticker |
| `GET /v1/free/market/news?limit=20` | Aggregated | Market-wide news (free) |

### Common query params

- `limit` — default `20`, max `100`.
- `language` — `en` (default), `zh`.
- `from` — `YYYY-MM-DD`.
- `to` — `YYYY-MM-DD`.

### Response

```json
{
  "data": [
    {
      "title": "...",
      "summary": "...",
      "url": "https://...",
      "source": "Reuters",
      "publishedAt": "2026-05-09T11:23:00Z",
      "tickers": ["AAPL", "MSFT"],
      "sentiment": "neutral"   // when available
    }
  ]
}
```

## Patterns

- **Per-ticker briefing**: `news/by-symbol/AAPL?limit=10`, summarize headlines + sentiment counts.
- **Macro briefing**: `free/news/finance?limit=20`, group by source, dedupe by URL.
- Always show `publishedAt` and `source`. Cite URLs when summarizing.
- WSB Reddit sentiment for retail-flow signal lives in `references/quant.md` (`/v1/free/stocks/wsb-sentiment/{symbol}`).
