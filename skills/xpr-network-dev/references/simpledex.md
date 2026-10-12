# SimpleDEX — Token Launch & AMM DEX on XPR Network

SimpleDEX is a non-custodial decentralized exchange and token launch platform on XPR Network, built by Proton NZ.

## Quick Reference

| Item | Value |
|------|-------|
| DEX contract | `simpledex` |
| Launch contract | `simplelaunch` |
| Token contract | `simpletoken` |
| XPR token | `eosio.token` (4,XPR) |
| RPC endpoint | `https://api.protonnz.com` |
| Analytics API | `https://indexer.protonnz.com` |
| Frontend | `https://dex.protonnz.com` |
| Treasury | `dex.protonnz` |

All token amounts use integers with 4 decimal places (multiply human amounts by 10,000).

---

## Analytics API

Public REST API with CORS enabled. Base: `https://indexer.protonnz.com`. Refreshes every 5 minutes.

### Key Endpoints

| Endpoint | Description |
|----------|-------------|
| `GET /api/stats` | Platform overview (~200 bytes) |
| `GET /api/prices` | All token prices with 24h/7d changes |
| `GET /api/prices/SYMBOL/history` | Price time-series (~5 min intervals, 30 days) |
| `GET /api/tokens` | Tokens with filters (symbol, creator, graduated) |
| `GET /api/pools` | All pools with TVL, fees, volume, depth metrics |
| `GET /api/movers` | Top gainers/losers by 24h % |
| `GET /api/tvl` | Aggregate TVL history |
| `GET /api/volume` | Daily volume time-series |
| `GET /api/tokens/:id/trades` | Token trades (paginated, max 200) |
| `GET /api/tokens/:id/holders` | Top token holders (zero RPC cost) |
| `GET /api/pools/:id/trades` | Pool trades; add `?live=1` for near-real-time |
| `GET /api/portfolio/:account/pnl` | Per-token P&L, holdings, LP positions |
| `GET /api/portfolio/:account/trades` | Trade history (paginated) |
| `GET /api/leaderboard/profit` | Top traders by realized P&L |
| `GET /api/leaderboard/burns` | Tokens ranked by burn percentage |
| `GET /api/overview` | Complete platform snapshot (~15KB) |
| `GET /api/events` | Graduation events |

**Rate Limits:** 120 req/min (general); 50 req/min (trades, holders).

---

## Reading On-Chain State

All reads use standard EOSIO `get_table_rows` RPC calls.

### Contract Tables

| Contract | Table | Scope | Description |
|----------|-------|-------|-------------|
| `simpledex` | `pools` | `simpledex` | Pool reserves, fee rates, LP supply |
| `simpledex` | `lp` | user account | LP token positions per pool |
| `simpledex` | `deposits` | user account | Pending deposits |
| `simplelaunch` | `curves` | `simplelaunch` | Bonding curves, graduation status |
| `simplelaunch` | `holdings` | user account | Pre-graduation token holdings |
| `simplelaunch` | `fees` | `simplelaunch` | Buy/sell fee config |
| `simplelaunch` | `antisnipe` | `simplelaunch` | Anti-snipe config |
| `simplelaunch` | `community` | `simplelaunch` | Token community profiles |

### Query Pool

```bash
curl -s -X POST https://api.protonnz.com/v1/chain/get_table_rows \
  -H 'Content-Type: application/json' \
  -d '{"code":"simpledex","scope":"simpledex","table":"pools","limit":50,"json":true}'
```

### Query LP Position

```bash
curl -s -X POST https://api.protonnz.com/v1/chain/get_table_rows \
  -H 'Content-Type: application/json' \
  -d '{"code":"simpledex","scope":"myaccount","table":"lp","limit":10,"json":true}'
```

---

## DEX Swaps

### Memo-Based Swap (Recommended)

Transfer input token to `simpledex` with memo format: `swap:POOL_ID:MIN_OUT:IS_TOKEN_A_IN`

```bash
# Swap XPR for a token on pool 1 (minimum 950000 output, tokenA=XPR is input)
proton action eosio.token transfer \
  '{"from":"myaccount","to":"simpledex","quantity":"1000.0000 XPR","memo":"swap:1:950000:true"}' \
  myaccount
```

### Output Calculation (Constant Product)

```
amountOut = (reserveOut * amountIn * (10000 - feeRate))
          / (reserveIn * 10000 + amountIn * (10000 - feeRate))
```

```typescript
function calculateSwapOutput(
  amountIn: number,
  reserveIn: number,
  reserveOut: number,
  feeRate: number = 30  // 0.3% = 30 bps
): number {
  const inputWithFee = amountIn * (10000 - feeRate);
  return Math.floor((reserveOut * inputWithFee) / (reserveIn * 10000 + inputWithFee));
}
```

### Multi-Hop Swaps

Route through up to 4 pools. Deposit tokens first, then call `multihopswap` with pool sequence.

### Swap Constraints

| Constraint | Value |
|-----------|-------|
| Max swap | 50% of input reserve |
| Cooldown | 1 second between swaps (per account) |
| Fee | 0.3% (30 bps) |
| Fee split | 50% LP reserves, 50% treasury |

---

## Liquidity Provision

### Add Liquidity

Deposit both tokens, then call `execaddliq`. First deposit locks 1,000 LP tokens permanently.

**LP Token Calculation:**
- Initial: `lpTokens = sqrt(amountA * amountB) - 1000`
- Subsequent: `lpTokens = min(amountA * totalLP / reserveA, amountB * totalLP / reserveB)`

### Remove Liquidity

Call `remliquidity` with poolId, LP amount, and minimum outputs for slippage protection.

LPs earn the full 0.3% fee through reserve growth. No separate claim action — earnings realize on withdrawal.

---

## Token Launch (Bonding Curve)

### Create Token

**Step 1:** Transfer 10,000 XPR with memo `create` to `simplelaunch`

**Step 2:** Call `createtoken`:

```bash
proton action simplelaunch createtoken \
  '{"account":"myaccount","symbol":"4,MYTOKEN","name":"My Token","description":"A token","image_url":"https://gateway.pinata.cloud/ipfs/QmHash"}' \
  myaccount
```

- Max 7 character symbol (uppercase A-Z only)
- Image must be IPFS URL
- Symbol format: `"PRECISION,NAME"` (e.g. `"4,MYTOKEN"`)

### Buy on Curve

```bash
# Buy tokens with 100 XPR (minimum 1 token out)
proton action eosio.token transfer \
  '{"from":"myaccount","to":"simplelaunch","quantity":"100.0000 XPR","memo":"buy:TOKEN_ID:1"}' \
  myaccount
```

### Sell on Curve

```bash
proton action simplelaunch sell \
  '{"seller":"myaccount","token_id":1,"quantity":10000000,"min_xpr_out":1}' \
  myaccount
```

### Bonding Curve Pricing

- Buy: `tokensOut = (virtualTokens * xprAfterFee) / (virtualXpr + xprAfterFee)`
- Sell: `xprOut = (virtualXpr * tokensIn) / (virtualTokens + tokensIn)` minus sell fee
- Fees: 1% buy, 1% sell — 50% to creator, 50% to treasury

### Anti-Snipe Protection

| Phase | Duration | Restriction |
|-------|----------|-------------|
| Creator-only | 0–60s | Only creator can buy |
| Early bird | 60–360s | Max 5,000 XPR per transaction |
| Open | 360s+ | No restrictions |

### Graduation

When `realXpr >= 50,000 XPR`, anyone calls `graduate`:

1. Creates DEX pool
2. Seeds with collected XPR + 20% of total supply (200M tokens)
3. Users call `claim` to mint real tokens

### Supply Model

| Allocation | Amount |
|-----------|--------|
| Max supply | 1,000,000,000 |
| Curve (virtual) | 800,000,000 (80%) |
| DEX pool (minted at graduation) | 200,000,000 (20%) |
| Typical circulating | 700–750M |

Unsold curve tokens never mint. Burns: send to `token.burn` account (tracked, not retired).

---

## Token Metadata

### Update Token Info (Creator Only)

```bash
proton action simplelaunch updatetoken \
  '{"account":"myaccount","token_id":1,"name":"New Name","description":"New desc","image_url":"https://..."}' \
  myaccount
```

### Community Profile (Graduated Tokens)

Creator sets for free via `setcommunit`. Non-creators pay 100,000 XPR via deposit + `updcommunit`.

Fields: description, website, telegram, twitter, discord, banner image URL.

---

## Protocol Parameters

| Parameter | Value |
|-----------|-------|
| DEX swap fee | 0.3% (30 bps) |
| Max swap per tx | 50% of reserves |
| Swap cooldown | 1 second |
| Minimum liquidity lock | 1,000 LP tokens |
| Deposit expiry | 24 hours |
| Max multi-hop | 4 pools |
| Launch buy/sell fee | 1% each |
| Creator fee share | 50% |
| Graduation threshold | 50,000 XPR |
| Token creation fee | 10,000 XPR |
| Creator-only window | 60 seconds |
| Early-bird cap | 5,000 XPR per tx |
| Token precision | 4 decimals |

---

## Error Handling

| Error | Cause | Resolution |
|-------|-------|-----------|
| Swap exceeds maximum | Input > 50% reserve | Split into smaller swaps |
| Slippage exceeded | Price moved past minAmountOut | Increase tolerance or retry |
| Pool paused | Admin action | Use alternate pool |
| Token not graduated | DEX operation on curve token | Use `simplelaunch` buy/sell |
| Swap cooldown active | < 1 second elapsed | Wait between calls |
| Deposit expired | > 24 hours old | Withdraw and re-deposit |
| Insufficient RAM | Account storage limit | Buy RAM via resources portal |

---

## Resources

- **Frontend**: https://dex.protonnz.com
- **Agent Guide**: https://dex.protonnz.com/llms.txt
- **Testnet**: https://testnet.dex.protonnz.com
- **Testnet Agent Guide**: https://testnet.dex.protonnz.com/llms-testnet.txt
- **Report Bugs**: https://protonnz.com
