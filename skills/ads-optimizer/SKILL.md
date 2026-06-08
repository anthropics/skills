---
name: ads-optimizer
description: AI-powered ad campaign management with performance audits, optimization analysis, A/B testing, and anomaly detection.
author: MCF Agentic
version: 1.0.0
tags: [advertising, campaigns, optimization, analytics, ab-testing, anomaly-detection, google-ads, meta-ads]
pricing: x402 (USDC on Base)
gateway: https://gateway.mcfagentic.com
---

# Ads Optimizer

Manage and optimize advertising campaigns with AI-driven analysis. Run performance audits, get optimization recommendations, manage A/B tests, and detect spending anomalies before they burn budget. Built for AI agents that manage paid media on behalf of clients.

## Authentication

All endpoints require x402 payment (USDC on Base L2). Send a request without payment to receive pricing info in the 402 response.

## Endpoints

### Manage Campaigns
- **Method:** POST
- **Path:** /api/ads/campaigns
- **Price:** $0.05 per call
- **Description:** Create or update an ad campaign configuration. Tracks platform, budget, targeting, and creative details.

**Request:**
```json
{
  "name": "HVAC Dallas - Search",
  "platform": "google-ads",
  "type": "search",
  "daily_budget": 50.00,
  "targeting": {
    "location": "Dallas, TX",
    "radius_miles": 25,
    "keywords": ["hvac repair near me", "ac installation dallas", "heating repair"],
    "negative_keywords": ["diy", "how to"]
  },
  "bid_strategy": "maximize-conversions",
  "landing_page": "https://comfortzonehvac.com/schedule"
}
```

**Response:**
```json
{
  "id": "camp_3x8rp4",
  "name": "HVAC Dallas - Search",
  "platform": "google-ads",
  "status": "active",
  "daily_budget": 50.00,
  "created_at": "2026-04-01T15:00:00Z"
}
```

### Run Audit
- **Method:** POST
- **Path:** /api/ads/audits
- **Price:** $0.50 per call
- **Description:** Run a full AI audit on a campaign. Analyzes spend efficiency, keyword performance, audience targeting, creative fatigue, and competitor positioning.

**Request:**
```json
{
  "campaign_id": "camp_3x8rp4",
  "date_range": {
    "start": "2026-03-01",
    "end": "2026-03-31"
  },
  "include_competitor_analysis": true
}
```

**Response:**
```json
{
  "audit_id": "aud_9m2kf7",
  "campaign_id": "camp_3x8rp4",
  "overall_score": 72,
  "spend_total": 1550.00,
  "conversions": 31,
  "cost_per_conversion": 50.00,
  "findings": [
    {"severity": "high", "area": "keywords", "finding": "3 keywords consuming 40% of budget with zero conversions", "action": "pause-keywords"},
    {"severity": "medium", "area": "bidding", "finding": "CPC 23% above industry average for HVAC", "action": "adjust-bids"},
    {"severity": "low", "area": "creative", "finding": "Ad copy unchanged for 45 days, CTR declining", "action": "refresh-creative"}
  ],
  "estimated_savings_monthly": 320.00
}
```

### Optimization Analysis
- **Method:** POST
- **Path:** /api/ads/optimization/analyze
- **Price:** $0.25 per call
- **Description:** Get specific optimization recommendations for a campaign. Returns actionable changes with projected impact.

**Request:**
```json
{
  "campaign_id": "camp_3x8rp4",
  "optimization_goal": "lower-cpa",
  "constraints": {
    "min_daily_budget": 30.00,
    "max_daily_budget": 75.00
  }
}
```

**Response:**
```json
{
  "recommendations": [
    {
      "action": "pause-keywords",
      "targets": ["hvac repair near me", "heating system cost"],
      "reason": "High spend, zero conversions in 30 days",
      "projected_savings": "$210/mo"
    },
    {
      "action": "increase-bid",
      "targets": ["ac installation dallas"],
      "reason": "Top performer, currently losing impression share",
      "projected_impact": "+8 conversions/mo"
    },
    {
      "action": "add-negative-keywords",
      "targets": ["free", "cost of", "average price"],
      "reason": "Informational queries burning budget",
      "projected_savings": "$85/mo"
    }
  ],
  "projected_new_cpa": 38.50,
  "projected_improvement": "23%"
}
```

### Manage A/B Tests
- **Method:** POST
- **Path:** /api/ads/tests
- **Price:** $0.10 per call
- **Description:** Create and track A/B tests on ad creative, landing pages, or bidding strategies.

**Request:**
```json
{
  "campaign_id": "camp_3x8rp4",
  "test_type": "ad-copy",
  "variant_a": {
    "headline": "Top-Rated HVAC Repair in Dallas",
    "description": "Same-day service. Licensed technicians. Call now."
  },
  "variant_b": {
    "headline": "AC Broken? Dallas Experts On Call",
    "description": "4.8 stars, 500+ reviews. Book online in 30 seconds."
  },
  "traffic_split": 50,
  "duration_days": 14,
  "success_metric": "conversion-rate"
}
```

**Response:**
```json
{
  "id": "test_5k7nw2",
  "campaign_id": "camp_3x8rp4",
  "status": "running",
  "start_date": "2026-04-01",
  "end_date": "2026-04-15",
  "traffic_split": "50/50"
}
```

### Detect Anomalies
- **Method:** GET
- **Path:** /api/ads/anomalies
- **Price:** $0.10 per call
- **Description:** Scan campaigns for spending anomalies, sudden performance drops, or suspicious click patterns.

**Request:**
```
GET /api/ads/anomalies?campaign_id=camp_3x8rp4&lookback_days=7
```

**Response:**
```json
{
  "anomalies": [
    {
      "type": "spend-spike",
      "severity": "high",
      "detected_at": "2026-03-29T08:00:00Z",
      "details": "Daily spend jumped 340% ($50 to $220) due to broad match keyword expansion",
      "recommended_action": "Review and restrict match types"
    },
    {
      "type": "ctr-drop",
      "severity": "medium",
      "detected_at": "2026-03-30T12:00:00Z",
      "details": "CTR dropped 45% on headline variant A, possible ad fatigue",
      "recommended_action": "Rotate creative"
    }
  ]
}
```

## Use Cases

- A media buying agent audits client campaigns monthly and implements optimizations
- An autonomous budget guardian monitors for anomalies and pauses runaway spend
- A creative agent runs A/B tests on ad copy and reports winning variants
- An analytics agent produces monthly performance reports with actionable insights
- A sales agent includes ad optimization as part of a managed services package

## Pricing

| Endpoint | Price | Description |
|----------|-------|-------------|
| /api/ads/campaigns | $0.05 | Create/update campaigns |
| /api/ads/audits | $0.50 | Full AI campaign audit |
| /api/ads/optimization/analyze | $0.25 | Optimization recommendations |
| /api/ads/tests | $0.10 | Manage A/B tests |
| /api/ads/anomalies | $0.10 | Anomaly detection scan |
