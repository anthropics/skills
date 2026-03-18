# LOAN Protocol on XPR Network

This guide covers integration with the LOAN lending protocol on XPR Network.

## Overview

LOAN is the native lending protocol on XPR Network enabling:
- **Supply assets to earn interest** - Deposit tokens, receive L-tokens (shares)
- **Collateralized loans** - Borrow against supplied collateral
- **Variable interest rates** - Supply/demand-based APY
- **Liquidations** - Automated health factor monitoring
- **LOAN token rewards** - Earn LOAN governance tokens on supply/borrow
- **Governance** - LOAN token holders govern protocol

### Key Contracts

| Contract | Description |
|----------|-------------|
| `lending.loan` | Main lending/borrowing/redeem logic |
| `shares.loan` | L-token share receipts (LXPR, LUSDC, etc.) |
| `loan.token` | LOAN governance token |
| `oracles` | Price feeds for collateral |

> ⚠️ **Important:** The main contract is `lending.loan`, NOT `lending`. Using the wrong contract will cause transactions to fail.

---

## Core Concepts

### L-Tokens (Share Tokens)

When you supply assets, you receive L-tokens representing your share of the pool:

| Supplied | L-Token Received | Precision | Token Contract |
|----------|-----------------|-----------|----------------|
| XPR | LXPR | 4 | `shares.loan` |
| XUSDC | LUSDC | 6 | `shares.loan` |
| XBTC | LBTC | 8 | `shares.loan` |
| XETH | LETH | 8 | `shares.loan` |
| XMD | LXMD | 6 | `shares.loan` |
| XUSDT | LUSDT | 6 | `shares.loan` |
| METAL | LXMT | 8 | `shares.loan` |
| XRP | LXRP | 6 | `shares.loan` |
| DOGE | LDOGE | 6 | `shares.loan` |
| HBAR | LHBAR | 6 | `shares.loan` |
| ADA | LADA | 6 | `shares.loan` |
| XLM | LXLM | 6 | `shares.loan` |
| LTC | LLTC | 8 | `shares.loan` |
| SOL | LSOL | 6 | `shares.loan` |

L-token values increase over time as interest accrues, so you get back more than you deposited.

### Health Factor

Health factor measures loan safety:

```
Health Factor = (Collateral Value × Liquidation Threshold) / Debt Value
```

| Health Factor | Status |
|--------------|--------|
| > 1.5 | Safe |
| 1.0 - 1.5 | Warning |
| < 1.0 | Liquidatable |

### Collateral Factor

Maximum borrowing power as percentage of collateral:

| Asset | Collateral Factor |
|-------|-------------------|
| XPR | 75% |
| XUSDC | 85% |
| XBTC | 75% |
| XETH | 75% |

---

## Supply Assets (Mint L-Tokens)

### Step 1: Enter Markets

Before supplying, you must enter the markets for the assets you want to use:

```bash
# Enter XPR and XUSDC markets
proton action lending.loan entermarkets '{"account":"myaccount","markets":["4,LXPR","6,LUSDC"]}' myaccount
```

### Step 2: Deposit (Mint)

Transfer tokens to `lending.loan` with memo `mint`:

```bash
# Supply 40000 XPR
proton action eosio.token transfer '{"from":"myaccount","to":"lending.loan","quantity":"40000.0000 XPR","memo":"mint"}' myaccount

# Supply 100 XUSDC
proton action xtokens transfer '{"from":"myaccount","to":"lending.loan","quantity":"100.000000 XUSDC","memo":"mint"}' myaccount
```

```typescript
async function supply(
  session: any,
  quantity: string,
  tokenContract: string  // 'eosio.token' for XPR, 'xtokens' for wrapped tokens
): Promise<any> {
  return session.transact({
    actions: [{
      account: tokenContract,
      name: 'transfer',
      authorization: [session.auth],
      data: {
        from: session.auth.actor,
        to: 'lending.loan',
        quantity: quantity,
        memo: 'mint'
      }
    }]
  }, { broadcast: true });
}

// Example: Supply 1000 XUSDC
await supply(session, '1000.000000 XUSDC', 'xtokens');

// Example: Supply 10000 XPR
await supply(session, '10000.0000 XPR', 'eosio.token');
```

> **Note:** The `mint` memo triggers L-token minting. Your L-token shares appear in the `lending.loan` `shares` table scoped to `lending.loan`.

### Verify Shares

```bash
# Check your L-token shares
curl -s -X POST https://proton.eosusa.io/v1/chain/get_table_rows \
  -H 'Content-Type: application/json' \
  -d '{"code":"lending.loan","scope":"lending.loan","table":"shares","lower_bound":"myaccount","upper_bound":"myaccount","limit":1,"json":true}'
```

Response format:
```json
{
  "rows": [{
    "account": "myaccount",
    "tokens": [
      {
        "key": {"sym": "4,LXPR", "contract": "shares.loan"},
        "value": 390334875
      },
      {
        "key": {"sym": "6,LUSDC", "contract": "shares.loan"},
        "value": 71479562
      }
    ]
  }]
}
```

The `value` field is the raw integer. Divide by `10^precision` to get the human-readable amount:
- LXPR value `390334875` with precision 4 = `39033.4875 LXPR`
- LUSDC value `71479562` with precision 6 = `71.479562 LUSDC`

---

## Redeem (Withdraw Supplied Assets)

The `redeem` action burns your L-tokens and returns the underlying asset plus accrued interest.

### Redeem Action

The action takes an `extended_asset` parameter:

```bash
# Redeem all LXPR shares back to XPR
proton action lending.loan redeem '{"redeemer":"myaccount","token":{"quantity":"39033.4875 LXPR","contract":"shares.loan"}}' myaccount

# Redeem all LUSDC shares back to XUSDC
proton action lending.loan redeem '{"redeemer":"myaccount","token":{"quantity":"71.479562 LUSDC","contract":"shares.loan"}}' myaccount
```

```typescript
async function redeem(
  session: any,
  quantity: string,  // e.g. "39033.4875 LXPR"
): Promise<any> {
  return session.transact({
    actions: [{
      account: 'lending.loan',
      name: 'redeem',
      authorization: [session.auth],
      data: {
        redeemer: session.auth.actor,
        token: {
          quantity: quantity,
          contract: 'shares.loan'
        }
      }
    }]
  }, { broadcast: true });
}

// Example: Redeem all LXPR
await redeem(session, '39033.4875 LXPR');
```

> ⚠️ **Precision matters!** LXPR uses precision 4 (e.g., `39033.4875`), LUSDC uses precision 6 (e.g., `71.479562`). Using wrong precision will fail.

The redeem action will:
1. Burn your L-tokens via `shares.loan` `retire` action
2. Issue LOAN reward tokens
3. Transfer the underlying asset back to you (e.g., XPR via `eosio.token`)

---

## Borrow

### Take Loan

```typescript
async function borrow(
  session: any,
  quantity: string
): Promise<any> {
  const position = await getUserPosition(session.auth.actor);

  if (position && position.health_factor < 1.2) {
    throw new Error('Health factor too low to borrow');
  }

  return session.transact({
    actions: [{
      account: 'lending.loan',
      name: 'borrow',
      authorization: [session.auth],
      data: {
        account: session.auth.actor,
        quantity: quantity
      }
    }]
  }, { broadcast: true });
}
```

```bash
# Borrow 500 XPR against collateral
proton action lending.loan borrow '{"account":"myaccount","quantity":"500.0000 XPR"}' myaccount
```

---

## Repay Loan

Transfer tokens back with `repay` memo:

```bash
# Repay 500 XUSDC
proton action xtokens transfer '{"from":"myaccount","to":"lending.loan","quantity":"500.000000 XUSDC","memo":"repay"}' myaccount

# Repay 1000 XPR
proton action eosio.token transfer '{"from":"myaccount","to":"lending.loan","quantity":"1000.0000 XPR","memo":"repay"}' myaccount
```

---

## Claim LOAN Rewards

LOAN tokens are distributed as rewards for supplying and borrowing:

```bash
proton action lending.loan claimrewards '{"claimer":"myaccount","markets":["4,LXPR","6,LUSDC"]}' myaccount
```

> **Note:** Use the L-token symbol format (e.g., `4,LXPR` not `4,XPR`) for the markets parameter. You can only claim for markets you have active positions in.

---

## Query Protocol State

### Get User Shares (L-Token Balances)

```typescript
async function getUserShares(account: string): Promise<any> {
  const response = await fetch('https://proton.eosusa.io/v1/chain/get_table_rows', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      code: 'lending.loan',
      scope: 'lending.loan',
      table: 'shares',
      lower_bound: account,
      upper_bound: account,
      limit: 1,
      json: true
    })
  });
  const { rows } = await response.json();
  return rows[0] ?? null;
}
```

### Get Market Stats

```typescript
async function getMarkets(): Promise<any[]> {
  const response = await fetch('https://proton.eosusa.io/v1/chain/get_table_rows', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      code: 'lending.loan',
      scope: 'lending.loan',
      table: 'markets',
      limit: 100,
      json: true
    })
  });
  const { rows } = await response.json();
  return rows;
}
```

---

## Liquidations

### Check Liquidatable Positions

```typescript
async function getLiquidatablePositions(): Promise<any[]> {
  const response = await fetch('https://proton.eosusa.io/v1/chain/get_table_rows', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      code: 'lending.loan',
      scope: 'lending.loan',
      table: 'positions',
      limit: 1000,
      json: true
    })
  });
  const { rows } = await response.json();
  return rows.filter((p: any) => p.health_factor < 1.0);
}
```

### Execute Liquidation

```bash
# Liquidate an underwater position
proton action xtokens transfer '{"from":"myaccount","to":"lending.loan","quantity":"500.000000 XUSDC","memo":"liquidate:targetaccount:XPR"}' myaccount
```

### Liquidation Bonus

| Collateral | Liquidation Bonus |
|------------|-------------------|
| XPR | 10% |
| XUSDC | 5% |
| XBTC | 10% |
| XETH | 10% |

---

## LOAN Token

### Token Details

| Property | Value |
|----------|-------|
| Contract | `loan.token` |
| Symbol | LOAN |
| Precision | 4 |
| Max Supply | 100,000,000 LOAN |

### Staking LOAN

```bash
proton action loan.token transfer '{"from":"myaccount","to":"loan.staking","quantity":"1000.0000 LOAN","memo":"stake"}' myaccount
```

### Query Staking Rewards

```bash
proton table loan.staking stakers --lower myaccount --upper myaccount
```

---

## Price Oracle Integration

### Get Asset Prices

```bash
# XPR price (feed index 3)
curl -s -X POST https://proton.eosusa.io/v1/chain/get_table_rows \
  -H 'Content-Type: application/json' \
  -d '{"code":"oracles","scope":"oracles","table":"data","lower_bound":3,"upper_bound":3,"limit":1,"json":true}'
```

Known oracle feed indices:

| Feed | Asset |
|------|-------|
| 1 | BTC |
| 2 | ETH |
| 3 | XPR |
| 4 | METAL |
| 5 | USDC |
| 6 | USDT |

---

## Whitelist Note

The LOAN protocol has a whitelist (`updatewl` action) that controls which accounts can interact. However, as of February 2026, the `mint` (supply) action appears to work for accounts not on the whitelist. The whitelist may only restrict certain operations like borrowing.

To check the whitelist:

```bash
curl -s -X POST https://proton.eosusa.io/v1/chain/get_table_rows \
  -H 'Content-Type: application/json' \
  -d '{"code":"lending.loan","scope":"lending.loan","table":"whitelist","limit":100,"json":true}'
```

---

## Quick Reference

### Common Actions

```bash
# Enter markets (required before first supply)
proton action lending.loan entermarkets '{"account":"alice","markets":["4,LXPR","6,LUSDC"]}' alice

# Supply XPR (mint L-tokens)
proton action eosio.token transfer '{"from":"alice","to":"lending.loan","quantity":"1000.0000 XPR","memo":"mint"}' alice

# Supply XUSDC (mint L-tokens)
proton action xtokens transfer '{"from":"alice","to":"lending.loan","quantity":"100.000000 XUSDC","memo":"mint"}' alice

# Redeem LXPR back to XPR
proton action lending.loan redeem '{"redeemer":"alice","token":{"quantity":"975.1234 LXPR","contract":"shares.loan"}}' alice

# Redeem LUSDC back to XUSDC
proton action lending.loan redeem '{"redeemer":"alice","token":{"quantity":"71.479562 LUSDC","contract":"shares.loan"}}' alice

# Borrow
proton action lending.loan borrow '{"account":"alice","quantity":"500.0000 XPR"}' alice

# Repay
proton action xtokens transfer '{"from":"alice","to":"lending.loan","quantity":"500.000000 XUSDC","memo":"repay"}' alice

# Claim LOAN rewards
proton action lending.loan claimrewards '{"claimer":"alice","markets":["4,LXPR","6,LUSDC"]}' alice

# Check shares
# Use RPC: code=lending.loan, scope=lending.loan, table=shares, lower_bound=alice, upper_bound=alice
```

### Key Tables

| Contract | Table | Scope | Description |
|----------|-------|-------|-------------|
| `lending.loan` | `shares` | `lending.loan` | User L-token share balances |
| `lending.loan` | `markets` | `lending.loan` | Market stats, APYs, reserve ratios |
| `lending.loan` | `positions` | `lending.loan` | User borrow positions, health factors |
| `lending.loan` | `whitelist` | `lending.loan` | Whitelisted accounts |
| `loan.token` | (standard token tables) | | LOAN governance token |
| `loan.staking` | `stakers` | `loan.staking` | LOAN staking positions |
| `oracles` | `data` | `oracles` | Price feeds |

### RPC Endpoints

Use these endpoints for querying tables (in order of reliability):

1. `https://proton.eosusa.io` (recommended)
2. `https://proton.protonuk.io`
3. `https://proton.cryptolions.io`

### Important Notes

- **Contract is `lending.loan`** — not `lending`
- **Share tokens live on `shares.loan`** — not in your token balance
- **Memo `mint`** for deposits, **memo `repay`** for loan repayment
- **Redeem uses `extended_asset`** format: `{"quantity":"X LXPR","contract":"shares.loan"}`
- **Precision must match exactly** — LXPR=4, LUSDC=6, LBTC=8, etc.
- **Enter markets first** before supplying or borrowing
- **LOAN rewards** are issued during redeem and can also be claimed separately
