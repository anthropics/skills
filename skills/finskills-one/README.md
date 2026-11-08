# finskills-one

A comprehensive Claude / VS Code Copilot skill that wraps the entire **Finskills** REST API
(`https://finskills.net`) into a single skill bundle.

The main entry point is [SKILL.md](SKILL.md). Detailed per-domain references live in
[`references/`](references/) and helper scripts in [`scripts/`](scripts/).

## Layout

```
finskills-one/
├── SKILL.md                 # Main skill manifest (loaded into context)
├── README.md                # This file
├── references/              # Detailed per-topic references (loaded on demand)
│   ├── stocks.md
│   ├── crypto.md
│   ├── forex.md
│   ├── macro.md
│   ├── market.md
│   ├── commodity.md
│   ├── news.md
│   ├── sec.md
│   ├── quant.md
│   ├── etf.md
│   ├── other.md
│   ├── workflows.md
│   └── errors.md
└── scripts/                 # Optional Python helpers
    ├── finskills_client.py  # Typed HTTP client covering every endpoint
    ├── quote.py             # CLI: live quote(s)
    ├── snapshot.py          # CLI: full single-ticker deep dive
    ├── screener.py          # CLI: market briefing / movers
    └── requirements.txt
```

## Coverage

- **Stocks**: quotes (single+batch), history, search, profile, financials, dividends, options, holders, recommendations, earnings.
- **Crypto**: price, markets, history (CoinGecko / Binance / CoinPaprika fallback).
- **Forex**: latest rates, history (Frankfurter / ECB).
- **Macro**: World Bank indicators, FRED series, GDP, CPI, treasury rates, Fed funds.
- **Market**: summary, indices, sectors, breadth, fear-greed, VIX, top gainers/losers/active, advance-decline, A/D, news, short volume, earnings calendar, Fama-French.
- **Commodities**: Yahoo futures, FRED & IMF series, BDI.
- **News**: finance feed (Google News), per-symbol (Marketaux).
- **SEC EDGAR**: filings, company-facts (XBRL), insider trades + 90d summary, 13F ownership.
- **Analyst / alt**: ratings, consensus, estimates, Congress trades, WSB sentiment.
- **ETF**: list, holdings.
- **Index**: constituents (SP500, NDX, DJIA, RUT).
- **Other**: FDIC bank search, BIN/IIN lookup, FEMA disasters.

## Usage

```bash
export FINSKILLS_API_KEY=fh_live_xxxxxxxxxxxxxxxx
pip install -r scripts/requirements.txt

python scripts/quote.py AAPL TSLA NVDA
python scripts/snapshot.py AAPL
python scripts/screener.py --briefing
```

Get an API key at https://finskills.net/register.
