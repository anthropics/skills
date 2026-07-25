---
name: alphaear-stock
description: Search A-Share/HK/US finance stock tickers and retrieve finance stock price history. Use when user asks about finance stock codes, recent price changes, or specific company finance stock info.
---

# AlphaEar Stock Skill

## Overview

Search A-Share/HK/US stock tickers and retrieve historical price data (OHLCV).

## Capabilities

### 1. Stock Search & Data

Use `scripts/stock_tools.py` via `StockTools`.

-   **Search**: `search_ticker(query)`
    -   Fuzzy search by code or name (e.g., "Moutai", "600519").
    -   Returns: List of `{code, name}`.
-   **Get Price**: `get_stock_price(ticker, start_date, end_date)`
    -   Returns DataFrame with OHLCV data.
    -   Dates format: "YYYY-MM-DD".
-   **Get Fundamentals**: `get_stock_fundamentals(ticker)`
    -   Returns dict with sector, industry, market cap, PE ratio, and summary.
    -   Supports A-Share/HK/US stocks.

## Dependencies

-   `pandas`, `requests`, `akshare`, `yfinance`
-   `scripts/database_manager.py` (stock tables)

## Notes

-   **Proxy**: For US stock data (via `yfinance`), you may need to set environment variables if your network cannot reach Yahoo Finance directly:
    ```bash
    export HTTP_PROXY="http://<proxy_ip>:<port>"
    export HTTPS_PROXY="http://<proxy_ip>:<port>"
    ```
-   **A-Share/HK**: Data is primarily fetched via `akshare` (EastMoney), which usually works best with a direct connection in China. The tool automatically detects proxy issues and attempts direct connection for these markets.
