# Other Data Sources

## Banking — FDIC

`GET /v1/free/banking/search?q=<name>&state=CA&limit=20`

Returns FDIC-insured institutions matching query.

`data`: `[ { fdicCertNumber, name, city, state, totalAssets, totalDeposits, equityCapital, openedOn, status } ]`.

## Payment — BIN / IIN Lookup

`GET /v1/free/payment/bin/{bin}` — first 6–8 digits of a card number.

`data`: `{ bin, scheme: "visa|mastercard|amex", type: "credit|debit", brand, country: { name, code, currency }, bank: { name, url, phone } }`.

Useful for fraud-flow demos and merchant reconciliation. **Never** ask the user for full card numbers.

## FEMA Disasters

`GET /v1/free/fema/disasters?state=CA&limit=50&year=2025`

Federal disaster declarations (relevant to insurance, REITs, agriculture, utilities).

`data`: `[ { disasterNumber, state, declarationDate, incidentType, title, fipsStateCode, designatedAreas } ]`.

## Patterns

- **Bank stress lookup**: `banking/search?q=<bank>` → check `equityCapital / totalAssets` ratio; cross-reference with stock price via `/v1/stocks/quote/<ticker>`.
- **Climate-risk note**: FEMA disasters in last 12 months for a state, joined with utility/insurance tickers in that footprint.
