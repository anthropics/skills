# Errors & Rate Limits

## Status Codes

| Status | Meaning | Action |
|--------|---------|--------|
| `200` | Success | — |
| `400` | Bad request (invalid param) | Check query params, symbol case |
| `401` | Missing or invalid `X-API-Key` | Ask user for a valid key |
| `402` | Subscription required | Upgrade plan / fall back to `/v1/free/...` |
| `403` | Quota exhausted | Slow down; surface to user |
| `404` | Symbol / CIK not found | Validate via `/v1/stocks/search` |
| `422` | Schema validation failed | Re-check param types |
| `429` | Rate-limited | Exponential backoff, see headers |
| `500-599` | Upstream / server error | Retry once after 1s; switch to fallback `source` |

## Error Body

```json
{
  "success": false,
  "error": {
    "code": "RATE_LIMITED",
    "message": "Plan limit exceeded for /v1/stocks/quote",
    "retryAfter": 60
  }
}
```

## Rate Limits

Headers on every response:

```
X-RateLimit-Limit:     60
X-RateLimit-Remaining: 23
X-RateLimit-Reset:     1715258400   # epoch seconds
Retry-After:           17           # only on 429
```

## Retry Strategy

```python
for attempt in range(3):
    r = client.get(...)
    if r.status_code < 500 and r.status_code != 429:
        return r
    sleep(2 ** attempt + random.random())
raise RuntimeError("upstream failed after retries")
```

## Cached Responses

Successful responses include `cached: true|false` in the envelope. When `cached=true`, `timestamp` reflects original fetch time, not the cache hit time. For freshness-sensitive UI, prefer endpoints/queries that return `cached=false`, or pass `?nocache=1` (when supported).

## Fallback Sources

When the primary source fails, the API automatically falls back. Inspect `source` and `sources` in the envelope to know what actually served the data — useful when the user asks "where does this number come from?".
