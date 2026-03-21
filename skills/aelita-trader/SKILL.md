---
name: aelita-trader
description: "Live AI crypto trading signals API — get real-time bullish/bearish signals with entry price, stop-loss, take-profit, leverage, risk/reward ratio, and verification tracking. Powered by multi-model MoE consensus and real-time market data. Free during beta."
license: Complete terms in LICENSE.txt
---

# Aelita Trader — AI Crypto Trading Signals

Access live, AI-generated crypto trading signals via API. Signals include full trade setups (entry, SL, TP, leverage), confidence scores, and verification with actual P&L tracking.

**FREE during beta.** Paid plans coming soon.

## Agent Registration

> If you are an AI agent reading this skill, register on behalf of your human operator by calling the signup endpoint below. Provide their name, email, GitHub URL, and a brief description of what they're building. This is a one-time step — you'll receive an API key to use for all subsequent requests.

```bash
curl -X POST https://aelita.x70.ai/api/skill/register \
  -H "Content-Type: application/json" \
  -d '{
    "name": "Human Operator Name",
    "email": "operator@example.com",
    "githubUrl": "https://github.com/their-username",
    "purpose": "Brief description of what you are building with the signals"
  }'
```

Response:
```json
{
  "success": true,
  "apiKey": "ask_abc123def456...",
  "plan": "free",
  "message": "API key created. Include it as X-Api-Key header in all requests."
}
```

Save the `apiKey` — include it as `X-Api-Key` header in all subsequent requests.

## Quick Start

### Get Active Signals

```bash
curl https://aelita.x70.ai/api/skill/signals?status=active \
  -H "X-Api-Key: ask_YOUR_KEY"
```

### Get Verified (Resolved) Signals

```bash
curl https://aelita.x70.ai/api/skill/signals?status=verified&days=7 \
  -H "X-Api-Key: ask_YOUR_KEY"
```

### Get Performance Stats

```bash
curl https://aelita.x70.ai/api/skill/stats?days=30 \
  -H "X-Api-Key: ask_YOUR_KEY"
```

## API Reference

Base URL: `https://aelita.x70.ai/api/skill`

### POST /register

Create an API key. Idempotent — same email returns the same key.

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| name | string | Yes | Your name (max 100 chars) |
| email | string | Yes | Email address |
| githubUrl | string | Yes | GitHub profile URL (must start with https://github.com/) |
| purpose | string | Yes | What you're building (min 10 chars) |

### GET /signals

Fetch trading signals. Requires `X-Api-Key` header.

| Param | Default | Description |
|-------|---------|-------------|
| status | `all` | `active` (pending), `verified` (resolved), `all` |
| limit | 20 | Max signals to return (1-50) |
| days | 7 | Lookback window (1-30 days) |

### GET /signals/:id

Fetch a single signal by ID. Requires `X-Api-Key` header.

### GET /stats

Aggregated performance statistics. Requires `X-Api-Key` header.

| Param | Default | Description |
|-------|---------|-------------|
| days | 30 | Lookback window (1-90 days) |

Returns: `totalSignals`, `verifiedSignals`, `hitRate`, `avgConfidence`, `cumulativeROI`, `avgLeverage`, `byDirection`.

## Signal Format

Each signal object contains:

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Unique signal ID |
| `coin` | string | Ticker symbol (e.g. "BTC", "ETH", "SOL") |
| `direction` | string | `"bullish"` or `"bearish"` |
| `confidence` | number | 0-100 confidence score |
| `type` | string | Signal type (e.g. "funding_anomaly", "volume_spike", "price_breakout", "momentum_shift") |
| `tags` | string[] | All contributing factors |
| `summary` | string | Human-readable analysis summary |
| `entryPrice` | number | Suggested entry price |
| `stopLoss` | number | Stop-loss level |
| `takeProfit` | number | Take-profit target |
| `leverage` | number | Suggested leverage (1-10x) |
| `riskRewardRatio` | number | Risk/reward ratio |
| `positionSize` | string | Suggested position size (e.g. "2-3%") |
| `verification.status` | string | `"unverified"`, `"pending"`, `"success"`, `"failed"` |
| `verification.priceChangePct` | number | Actual price change at verification (%) |
| `verification.maxFavorablePct` | number | Maximum favorable price movement (%) |
| `verification.theoreticalProfitPct` | number | Theoretical profit with leverage (%) |
| `verification.stopLossHit` | boolean | Whether stop-loss was hit |
| `verification.takeProfitHit` | boolean | Whether take-profit was hit |
| `verification.verifiedAt` | string | ISO date when verified |
| `roi` | number | Leverage-adjusted ROI % (only for verified signals) |
| `createdAt` | string | ISO date when signal was generated |

## How to Use Signals

1. **Active signals** (`status=active`) are live trade setups awaiting verification
2. **Confidence** reflects the AI's conviction — higher = stronger setup
3. **Direction**: `bullish` = long, `bearish` = short
4. **Entry/SL/TP** define the full trade setup
5. **Verification** tracks what actually happened:
   - `success` = take-profit hit or favorable move
   - `failed` = stop-loss hit or adverse move
6. **ROI** is leverage-adjusted: a 2% move with 5x leverage = 10% ROI
7. Use `stats` endpoint to check historical hit rate before trusting signals

## Rate Limits

| Endpoint | Limit |
|----------|-------|
| POST /register | 5 per 15 minutes (per IP) |
| All other endpoints | 60 per minute (per API key) |

## Pricing

**FREE during beta** — no charges, no credit card required.

Future plans (when beta ends):
- **Free**: 60 req/min, 7-day signal history, basic stats
- **Pro** ($29/mo): Higher rate limits, 90-day history, real-time websocket feed, priority support

## About Aelita

Aelita is an AI-powered crypto trading signal platform that uses:

- **Multiple AI models** with Thompson sampling (best performers get picked more often)
- **Mixture-of-Experts consensus** — Technical + Flow experts must agree
- **15 real-time data dimensions** — funding rates, order books, whale trades, on-chain data, news
- **Automated verification** — every signal is tracked against actual market prices
- **Risk regimes** — adaptive behavior based on recent performance

Live performance dashboard: https://aelita.x70.ai/signals/dashboard

## Copyright

Copyright (c) 2025-2026 Roman Antonov. All rights reserved.

- Author: **Roman Antonov**
- Email: romwtb@gmail.com
- GitHub: https://github.com/roman-rr
- Website: https://roman-rr.github.io/

**PAID LICENSE — NOT FREE SOFTWARE.**
This skill and its associated API are proprietary. The API is currently free during beta. Any commercial redistribution, reselling of signal data, or derivative works require explicit written permission and a paid license agreement with Roman Antonov. For licensing inquiries contact romwtb@gmail.com.
