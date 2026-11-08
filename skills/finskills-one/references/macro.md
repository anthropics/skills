# Macroeconomics Reference

Two tiers:

- **Free tier (`/v1/free/macro/...`)** — World Bank, IMF, OECD, ECB, US Treasury direct.
- **Premium tier (`/v1/macro/...`)** — FRED-backed (St. Louis Fed) for richer US series.

## Free Endpoints

| Endpoint | Purpose | Key Params |
|----------|---------|------------|
| `GET /v1/free/macro/gdp` | GDP across countries | `country` (`US`, `CN`, `JP`, `DE`, `IN`, …) |
| `GET /v1/free/macro/gdp/{countryCode}` | Same, path form | ISO-2 or ISO-3 |
| `GET /v1/free/macro/indicator/{code}` | World Bank indicator | code e.g. `NY.GDP.MKTP.CD`, `FP.CPI.TOTL.ZG`, `SL.UEM.TOTL.ZS` |
| `GET /v1/free/macro/treasury-rates` | US Treasury yield curve (1M–30Y) | — |
| `GET /v1/free/macro/inflation` | CPI inflation | `country` (default `US`) |

### Common World Bank codes

| Code | Meaning |
|------|---------|
| `NY.GDP.MKTP.CD` | GDP (current US$) |
| `NY.GDP.PCAP.CD` | GDP per capita |
| `FP.CPI.TOTL.ZG` | Inflation, consumer prices (annual %) |
| `SL.UEM.TOTL.ZS` | Unemployment (% of total labor force) |
| `FR.INR.RINR` | Real interest rate |
| `NE.EXP.GNFS.ZS` | Exports (% of GDP) |
| `BX.KLT.DINV.WD.GD.ZS` | FDI net inflows (% of GDP) |

## Premium / FRED Endpoints

| Endpoint | Purpose |
|----------|---------|
| `GET /v1/macro/indicator/{series}` | Any FRED series |
| `GET /v1/macro/gdp` | US real GDP (FRED) |
| `GET /v1/macro/inflation` | US CPI |
| `GET /v1/macro/interest-rates` | Fed Funds rate history |

### Common FRED series

| Series | Meaning |
|--------|---------|
| `GDP` | US Nominal GDP |
| `GDPC1` | US Real GDP |
| `CPIAUCSL` | CPI All Urban Consumers |
| `CPILFESL` | Core CPI |
| `FEDFUNDS` | Effective Fed Funds Rate |
| `DFF` | Fed Funds (daily) |
| `DGS10` | 10-Year Treasury |
| `DGS2` | 2-Year Treasury |
| `T10Y2Y` | 10Y–2Y spread (recession indicator) |
| `UNRATE` | Unemployment rate |
| `PAYEMS` | Nonfarm payrolls |
| `M2SL` | M2 money supply |
| `DCOILWTICO` | WTI Crude oil price |
| `VIXCLS` | VIX (close) |
| `UMCSENT` | UMich Consumer Sentiment |
| `INDPRO` | Industrial Production |
| `HOUST` | Housing Starts |

## Treasury Yield Curve

```bash
curl -H "X-API-Key: $KEY" https://finskills.net/v1/free/macro/treasury-rates
```

`data`: `[ { date, "1M": 5.31, "3M": 5.30, "6M": 5.20, "1Y": 5.05, "2Y": 4.65, "5Y": 4.30, "10Y": 4.21, "30Y": 4.40 } ]`.

Inversion check: `data[0]["10Y"] - data[0]["2Y"] < 0` → inverted.

## Tips

- For a "macro dashboard" call FRED `GDPC1`, `CPIAUCSL`, `UNRATE`, `FEDFUNDS`, `DGS10`, `T10Y2Y` in parallel.
- Always present growth rates as % YoY when comparing periods, and label whether values are real or nominal.
