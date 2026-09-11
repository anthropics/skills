# Commodity Reference

Three data backends are unified:

- **Yahoo** (real-time futures): `CL=F`, `GC=F`, etc.
- **FRED** (long history): `DCOILWTICO`, `GOLDAMGBD228NLBM`, etc.
- **IMF** (Primary Commodity Prices): `POILAPSP`, `PGOLD`, `PWHEAMT`, etc.

## Catalog & Prices

| Endpoint | Use |
|----------|-----|
| `GET /v1/free/commodity/catalog?category=energy` | Browse available symbols. Categories: `energy, metals_precious, metals_industrial, agriculture, livestock, softs` |
| `GET /v1/free/commodity/prices?category=metals_precious` | Real-time prices for category (omit for all) |
| `GET /v1/free/commodity/price/{symbol}` | Single Yahoo futures quote |
| `GET /v1/free/commodity/history/{symbol}?range=1y&interval=1d` | Single futures OHLCV history |

### Yahoo futures cheatsheet

| Symbol | Contract |
|--------|---------|
| `CL=F` | WTI Crude Oil |
| `BZ=F` | Brent Crude Oil |
| `NG=F` | Natural Gas |
| `RB=F` | RBOB Gasoline |
| `HO=F` | Heating Oil |
| `GC=F` | Gold |
| `SI=F` | Silver |
| `PL=F` | Platinum |
| `PA=F` | Palladium |
| `HG=F` | Copper |
| `ALI=F` | Aluminum |
| `ZW=F` | Wheat |
| `ZC=F` | Corn |
| `ZS=F` | Soybeans |
| `KC=F` | Coffee |
| `SB=F` | Sugar |
| `CT=F` | Cotton |
| `CC=F` | Cocoa |
| `LE=F` | Live Cattle |
| `HE=F` | Lean Hogs |

## FRED commodity series

| Endpoint | Use |
|----------|-----|
| `GET /v1/free/commodity/fred` | List of curated FRED commodity series |
| `GET /v1/free/commodity/fred/{seriesId}?limit=365&startDate=2020-01-01` | Historical series |

Useful series: `DCOILWTICO` (WTI), `DCOILBRENTEU` (Brent), `DHHNGSP` (Henry Hub gas), `GOLDAMGBD228NLBM` (gold London PM fix), `IR3000` (silver), `PWHEAMTUSDM` (wheat IMF).

## IMF Primary Commodity Prices

| Endpoint | Use |
|----------|-----|
| `GET /v1/free/commodity/imf` | Indicator catalog |
| `GET /v1/free/commodity/imf/batch?indicators=POILAPSP,PGOLD,PWHEAMT` | Batch fetch |
| `GET /v1/free/commodity/imf/{indicator}?periods=120` | Single indicator (monthly periods back) |

Key indicators: `POILAPSP` (avg crude), `PNGASEU` (EU natgas), `PCOAL` (coal), `PGOLD`, `PSILVER`, `PCOPP`, `PALUM`, `PWHEAMT`, `PMAIZMT`, `PSOYB`, `PSUGAISA`, `PCOFFOTM`.

## Baltic Dry Index (shipping)

| Endpoint | Use |
|----------|-----|
| `GET /v1/free/commodity/bdi` | Latest BDI value |
| `GET /v1/free/commodity/bdi/history?range=1y` | Historical |

BDI is a leading indicator of global trade demand; track alongside copper and oil.

## Patterns

- **Energy basket**: parallel `price/CL=F`, `price/BZ=F`, `price/NG=F` then summarize.
- **Inflation hedge dashboard**: gold (`GC=F`), silver (`SI=F`), copper (`HG=F`), oil (`CL=F`), wheat (`ZW=F`), 1Y history each.
- For long history (>1Y), use FRED/IMF endpoints; Yahoo futures are continuous-front-month and limited beyond 2 years.
