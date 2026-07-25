---
name: alphaear-news
description: Fetch hot finance news, unified trends, and prediction financial market data. Use when the user needs real-time financial news, trend reports from multiple finance sources (Weibo, Zhihu, WallstreetCN, etc.), or Polymarket finance market prediction data.
---

# AlphaEar News Skill

## Overview

Fetch real-time hot news, generate unified trend reports, and retrieve Polymarket prediction data.

## Capabilities

### 1. Fetch Hot News & Trends

Use `scripts/news_tools.py` via `NewsNowTools`.

-   **Fetch News**: `fetch_hot_news(source_id, count)`
    -   See [sources.md](references/sources.md) for valid `source_id`s (e.g., `cls`, `weibo`).
-   **Unified Report**: `get_unified_trends(sources)`
    -   Aggregates top news from multiple sources.

### 2. Fetch Prediction Markets

Use `scripts/news_tools.py` via `PolymarketTools`.

-   **Market Summary**: `get_market_summary(limit)`
    -   Returns a formatted report of active prediction markets.

## Dependencies

-   `requests`, `loguru`
-   `scripts/database_manager.py` (Local DB)
