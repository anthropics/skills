---
name: trading-signal
description: |
  Subscribe and retrieve on-chain Smart Money signals. Monitor trading activities of smart money addresses,
  including buy/sell signals, trigger price, current price, max gain, and exit rate.
  Use this skill when users are looking for investment opportunities — smart money signals can serve as valuable references for potential trades.
---

# Trading Signal Skill

## API Endpoint

### Get Smart Money Signals

**Method**: POST

**URL**: 
```
https://web3.binance.com/bapi/defi/v1/public/wallet-direct/buw/wallet/web/signal/smart-money/ai
```

**Request Headers**:
```
Content-Type: application/json
Accept-Encoding: identity
User-Agent: binance-web3/1.1 (Skill)
```

**Request Body**:
```
(response: see field tables below)
```

**Request Parameters**:

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| chainId | string | Yes | Chain ID: `56` for bsc, `CT_501` for solana |
| page | number | No | Page number, starting from 1 |
| pageSize | number | No | Items per page, max 100 |

**Example Request**:
```bash
curl --location 'https://web3.binance.com/bapi/defi/v1/public/wallet-direct/buw/wallet/web/signal/smart-money/ai' \
--header 'Content-Type: application/json' \
--header 'Accept-Encoding: identity' \
--header 'User-Agent: binance-web3/1.1 (Skill)' \
--data '{"page":1,"pageSize":100,"chainId":"CT_501"}'
```

**Response Example**:
```json
{
    "code": "000000",
    "message": null,
    "messageDetail": null,
    "data": [
        {
            "signalId": 22179,
            "ticker": "symbol of the token",
            "chainId": "CT_501",
            "contractAddress": "NV...pump",
            "logoUrl": "/images/web3-data/public/token/logos/825C62EC6BE6.png",
            "chainLogoUrl": "https://bin.bnbstatic.com/image/admin_mgs_image_upload/20250303/42065e0a-3808-400e-b589-61c2dbfc0eac.png",
            "tokenDecimals": 6,
            "isAlpha": false,
            "launchPlatform": "Pumpfun",
            "mark": null,
            "isExclusiveLaunchpad": false,
            "alphaPoint": null,
            "tokenTag": {
                "Social Events": [
                    {"tagName": "DEX Paid", "languageKey": "wmp-label-update-dexscreener-social"}
                ],
                "Launch Platform": [
                    {"tagName": "Pumpfun", "languageKey": "wmp-label-title-pumpfun"}
                ],
                "Sensitive Events": [
                    {"tagName": "Smart Money Add Holdings", "languageKey": "wmp-label-title-smart-money-add-position"}
                ]
            },
            "smartSignalType": "SMART_MONEY",
            "smartMoneyCount": 5,
            "direction": "buy",
            "timeFrame": 883000,
            "signalTriggerTime": 1771903462000,
            "totalTokenValue": "3436.694044670495772073",
            "alertPrice": "0.024505932131088482",
            "alertMarketCap": "24505118.720436560690909782",
            "currentPrice": "0.025196",
            "currentMarketCap": "25135683.751234890220129783671668745",
            "highestPrice": "0.027244000000000000",
            "highestPriceTime": 1771927760000,
            "exitRate": 78,
            "status": "timeout",
            "maxGain": "5.4034",
            "signalCount": 23
        }
    ],
    "success": true
}
```

**Response Fields**:

### Basic Information
| Field | Type | Description |
|-------|------|-------------|
| signalId | number | Unique signal ID |
| ticker | string | Token symbol/name |
| chainId | string | Chain ID |
| contractAddress | string | Token contract address |
| logoUrl | string | Token icon URL path |
| chainLogoUrl | string | Chain icon URL |
| tokenDecimals | number | Token decimals |

### Tag Information
| Field | Type | Description |
|-------|------|-------------|
| isAlpha | boolean | Whether it's an Alpha token |
| launchPlatform | string | Launch platform (e.g., Pumpfun) |
| isExclusiveLaunchpad | boolean | Whether it's exclusive launchpad |
| alphaPoint | number | Alpha points (can be null) |
| tokenTag | object | Token tag categories |

### Signal Data
| Field | Type | Description |
|-------|------|-------------|
| smartSignalType | string | Signal type, e.g., `SMART_MONEY` |
| smartMoneyCount | number | Number of smart money addresses involved |
| direction | string | Trade direction: `buy` / `sell` |
| timeFrame | number | Time frame (milliseconds) |
| signalTriggerTime | number | Signal trigger timestamp (ms) |
| signalCount | number | Total signal count |

### Price Data
| Field | Type | Description |
|-------|------|-------------|
| totalTokenValue | string | Total trade value (USD) |
| alertPrice | string | Price at signal trigger |
| alertMarketCap | string | Market cap at signal trigger |
| currentPrice | string | Current price |
| currentMarketCap | string | Current market cap |
| highestPrice | string | Highest price after signal |
| highestPriceTime | number | Highest price timestamp (ms) |

### Performance Data
| Field | Type | Description |
|-------|------|-------------|
| exitRate | number | Exit rate (%) |
| status | string | Signal status: `active`/`timeout`/`completed` |
| maxGain | string | Maximum gain (%) |

## Token Tag Types

**tokenTag categories**: Social Events (DEX Paid), Launch Platform (Pumpfun, Moonshot), Sensitive Events (Smart Money Add/Reduce Holdings, Whale Buy/Sell).

## Supported Chains

| Chain Name | chainId |
|------------|---------|
| BSC | 56 |
| Solana | CT_501 |

## Signal Status

| Status | Description |
|--------|-------------|
| active | Active, signal still valid |
| timeout | Timed out, exceeded observation period |
| completed | Completed, reached target or stop loss |

## User Agent Header

Include `User-Agent` header with the following string: `binance-web3/1.1 (Skill)`

## Use Cases

1. **Track Smart Money**: Monitor professional investor trading behavior
2. **Discover Opportunities**: Get early signals when smart money buys
3. **Risk Alert**: Receive alerts when smart money starts selling
4. **Performance Analysis**: Analyze historical signal performance and max gains
5. **Strategy Validation**: Evaluate signal quality via exitRate and maxGain

## Example Requests

### Get Smart Money Signals on Solana
```bash
curl --location 'https://web3.binance.com/bapi/defi/v1/public/wallet-direct/buw/wallet/web/signal/smart-money/ai' \
--header 'Content-Type: application/json' \
--header 'Accept-Encoding: identity' \
--header 'User-Agent: binance-web3/1.1 (Skill)' \
--data '{"smartSignalType":"","page":1,"pageSize":50,"chainId":"CT_501"}'
```

### Get Signals on BSC
```bash
curl --location 'https://web3.binance.com/bapi/defi/v1/public/wallet-direct/buw/wallet/web/signal/smart-money/ai' \
--header 'Content-Type: application/json' \
--header 'Accept-Encoding: identity' \
--header 'User-Agent: binance-web3/1.1 (Skill)' \
--data '{"smartSignalType":"","page":1,"pageSize":50,"chainId":"56"}'
```

## Notes

1. Token icon URL requires full domain prefix: `https://bin.bnbstatic.com` + logoUrl path
2. Chain icon URL (chainLogoUrl) is already a full URL
3. All timestamps are in milliseconds
4. maxGain is a percentage string
5. Signals may timeout (status=timeout), focus on active signals
6. Higher smartMoneyCount may indicate higher signal reliability
7. exitRate shows smart money exit status, high exitRate may indicate expired signal
