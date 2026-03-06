# LOAN Protocol on XPR Network

This guide covers integration with the LOAN lending protocol on XPR Network.

## Overview

LOAN is the native lending protocol on XPR Network enabling:
- **Collateralized loans** - Borrow against crypto collateral
- **Variable interest rates** - Supply/demand-based APY
- **Liquidations** - Automated health factor monitoring
- **Governance** - LOAN token holders govern protocol

### Key Contracts

| Contract | Description |
|----------|-------------|
| `loan.token` | LOAN governance token |
| `lending` | Main lending/borrowing logic |
| `oracle` | Price feeds for collateral |

---

## Core Concepts

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

## Query Protocol State

### Get User Position

```typescript
interface UserPosition {
  account: string;
  supplied: Asset[];      // Supplied collateral
  borrowed: Asset[];      // Outstanding loans
  health_factor: number;
}

async function getUserPosition(account: string): Promise<UserPosition | null> {
  const { rows } = await rpc.get_table_rows({
    code: 'lending',
    scope: 'lending',
    table: 'positions',
    lower_bound: account,
    upper_bound: account,
    limit: 1
  });

  return rows[0] ?? null;
}
```

### Get Market Stats

```typescript
interface Market {
  asset: string;
  total_supplied: string;
  total_borrowed: string;
  supply_apy: number;
  borrow_apy: number;
  utilization: number;
}

async function getMarkets(): Promise<Market[]> {
  const { rows } = await rpc.get_table_rows({
    code: 'lending',
    scope: 'lending',
    table: 'markets',
    limit: 100
  });

  return rows;
}
```

### Get Interest Rates

```typescript
async function getInterestRates(symbol: string): Promise<{
  supplyAPY: number;
  borrowAPY: number;
}> {
  const markets = await getMarkets();
  const market = markets.find(m => m.asset.includes(symbol));

  if (!market) {
    throw new Error(`Market ${symbol} not found`);
  }

  return {
    supplyAPY: market.supply_apy / 100,  // Convert basis points
    borrowAPY: market.borrow_apy / 100
  };
}
```

---

## Supply Collateral

### Deposit Assets

```typescript
async function supply(
  session: any,
  quantity: string,
  tokenContract: string
): Promise<any> {
  return session.transact({
    actions: [{
      account: tokenContract,
      name: 'transfer',
      authorization: [session.auth],
      data: {
        from: session.auth.actor,
        to: 'lending',
        quantity: quantity,
        memo: 'supply'
      }
    }]
  }, { broadcast: true });
}

// Example: Supply 1000 XUSDC
await supply(session, '1000.000000 XUSDC', 'xtokens');
```

### Withdraw Collateral

```typescript
async function withdraw(
  session: any,
  quantity: string
): Promise<any> {
  return session.transact({
    actions: [{
      account: 'lending',
      name: 'withdraw',
      authorization: [session.auth],
      data: {
        account: session.auth.actor,
        quantity: quantity
      }
    }]
  }, { broadcast: true });
}
```

---

## Borrow

### Take Loan

```typescript
async function borrow(
  session: any,
  quantity: string
): Promise<any> {
  // Check health factor first
  const position = await getUserPosition(session.auth.actor);

  if (position && position.health_factor < 1.2) {
    throw new Error('Health factor too low to borrow');
  }

  return session.transact({
    actions: [{
      account: 'lending',
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

### Calculate Max Borrow

```typescript
async function calculateMaxBorrow(
  account: string,
  borrowSymbol: string
): Promise<number> {
  const position = await getUserPosition(account);

  if (!position) return 0;

  // Get prices from oracle
  const collateralValue = await calculateCollateralValue(position.supplied);
  const debtValue = await calculateDebtValue(position.borrowed);

  // Available = (Collateral × Factor) - Current Debt
  const collateralFactor = 0.75;  // Example: 75%
  const availableToBorrow = (collateralValue * collateralFactor) - debtValue;

  const borrowPrice = await getAssetPrice(borrowSymbol);
  return availableToBorrow / borrowPrice;
}
```

---

## Repay Loan

### Full Repayment

```typescript
async function repay(
  session: any,
  quantity: string,
  tokenContract: string
): Promise<any> {
  return session.transact({
    actions: [{
      account: tokenContract,
      name: 'transfer',
      authorization: [session.auth],
      data: {
        from: session.auth.actor,
        to: 'lending',
        quantity: quantity,
        memo: 'repay'
      }
    }]
  }, { broadcast: true });
}

// Example: Repay 500 XUSDC
await repay(session, '500.000000 XUSDC', 'xtokens');
```

### Repay Max (Full Outstanding)

```typescript
async function repayMax(
  session: any,
  symbol: string,
  tokenContract: string
): Promise<any> {
  const position = await getUserPosition(session.auth.actor);
  const debt = position?.borrowed.find(b => b.includes(symbol));

  if (!debt) {
    throw new Error('No outstanding debt for ' + symbol);
  }

  return repay(session, debt, tokenContract);
}
```

---

## Liquidations

### Check Liquidatable Positions

```typescript
async function getLiquidatablePositions(): Promise<UserPosition[]> {
  const { rows } = await rpc.get_table_rows({
    code: 'lending',
    scope: 'lending',
    table: 'positions',
    limit: 1000
  });

  return rows.filter((p: UserPosition) => p.health_factor < 1.0);
}
```

### Execute Liquidation

```typescript
async function liquidate(
  session: any,
  targetAccount: string,
  debtToCover: string,
  collateralAsset: string,
  tokenContract: string
): Promise<any> {
  // Verify position is liquidatable
  const position = await getUserPosition(targetAccount);

  if (!position || position.health_factor >= 1.0) {
    throw new Error('Position not liquidatable');
  }

  return session.transact({
    actions: [
      // Send debt tokens to cover
      {
        account: tokenContract,
        name: 'transfer',
        authorization: [session.auth],
        data: {
          from: session.auth.actor,
          to: 'lending',
          quantity: debtToCover,
          memo: `liquidate:${targetAccount}:${collateralAsset}`
        }
      }
    ]
  }, { broadcast: true });
}
```

### Liquidation Bonus

Liquidators receive a bonus for helping maintain protocol health:

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

```typescript
async function stakeLoan(
  session: any,
  quantity: string
): Promise<any> {
  return session.transact({
    actions: [{
      account: 'loan.token',
      name: 'transfer',
      authorization: [session.auth],
      data: {
        from: session.auth.actor,
        to: 'loan.staking',
        quantity: quantity,
        memo: 'stake'
      }
    }]
  }, { broadcast: true });
}
```

### Query Staking Rewards

```typescript
async function getStakingRewards(account: string): Promise<string> {
  const { rows } = await rpc.get_table_rows({
    code: 'loan.staking',
    scope: 'loan.staking',
    table: 'stakers',
    lower_bound: account,
    upper_bound: account,
    limit: 1
  });

  return rows[0]?.pending_rewards ?? '0.0000 LOAN';
}
```

---

## Health Monitoring

### React Hook for Position Monitoring

```typescript
import { useState, useEffect } from 'react';

interface PositionStatus {
  position: UserPosition | null;
  healthStatus: 'safe' | 'warning' | 'danger';
  loading: boolean;
}

export function usePositionHealth(account: string): PositionStatus {
  const [state, setState] = useState<PositionStatus>({
    position: null,
    healthStatus: 'safe',
    loading: true
  });

  useEffect(() => {
    let mounted = true;

    async function fetchPosition() {
      try {
        const position = await getUserPosition(account);

        if (!mounted) return;

        let healthStatus: 'safe' | 'warning' | 'danger' = 'safe';
        if (position) {
          if (position.health_factor < 1.0) {
            healthStatus = 'danger';
          } else if (position.health_factor < 1.5) {
            healthStatus = 'warning';
          }
        }

        setState({ position, healthStatus, loading: false });
      } catch (error) {
        if (mounted) {
          setState(prev => ({ ...prev, loading: false }));
        }
      }
    }

    fetchPosition();

    // Poll every 30 seconds
    const interval = setInterval(fetchPosition, 30000);

    return () => {
      mounted = false;
      clearInterval(interval);
    };
  }, [account]);

  return state;
}
```

### Health Warning Component

```tsx
interface HealthWarningProps {
  healthFactor: number;
}

export function HealthWarning({ healthFactor }: HealthWarningProps) {
  if (healthFactor >= 1.5) return null;

  const isDanger = healthFactor < 1.0;

  return (
    <div style={{
      backgroundColor: isDanger ? '#ff4757' : '#ffa502',
      color: 'white',
      padding: '12px',
      borderRadius: '8px',
      marginBottom: '16px'
    }}>
      <strong>
        {isDanger
          ? '⚠️ Position at Risk of Liquidation!'
          : '⚠ Health Factor Low'}
      </strong>
      <p>
        Health Factor: {healthFactor.toFixed(2)}
        {isDanger
          ? ' - Add collateral or repay debt immediately'
          : ' - Consider adding collateral'}
      </p>
    </div>
  );
}
```

---

## Price Oracle Integration

### Get Asset Prices

```typescript
const ORACLE_FEEDS: Record<string, number> = {
  'XPR': 1,
  'BTC': 4,
  'ETH': 5,
  'USDC': 6
};

async function getAssetPrice(symbol: string): Promise<number> {
  const feedIndex = ORACLE_FEEDS[symbol];

  if (!feedIndex) {
    throw new Error(`No oracle feed for ${symbol}`);
  }

  const { rows } = await rpc.get_table_rows({
    code: 'oracles',
    scope: 'oracles',
    table: 'data',
    lower_bound: feedIndex,
    upper_bound: feedIndex,
    limit: 1
  });

  if (rows.length === 0) {
    throw new Error(`Oracle data not found for ${symbol}`);
  }

  // Price is stored as u64 with 4 decimals
  return rows[0].value / 10000;
}
```

### Calculate Collateral Value

```typescript
async function calculateCollateralValue(
  supplied: Asset[]
): Promise<number> {
  let totalValue = 0;

  for (const asset of supplied) {
    const [amount, symbol] = asset.split(' ');
    const price = await getAssetPrice(symbol);
    totalValue += parseFloat(amount) * price;
  }

  return totalValue;
}
```

---

## Quick Reference

### Common Actions

```bash
# Supply collateral
proton action xtokens transfer '{"from":"alice","to":"lending","quantity":"1000.000000 XUSDC","memo":"supply"}' alice

# Borrow
proton action lending borrow '{"account":"alice","quantity":"500.0000 XPR"}' alice

# Repay
proton action xtokens transfer '{"from":"alice","to":"lending","quantity":"500.000000 XUSDC","memo":"repay"}' alice

# Withdraw
proton action lending withdraw '{"account":"alice","quantity":"1000.000000 XUSDC"}' alice

# Check position
proton table lending positions -l alice -u alice
```

### Key Tables

| Contract | Table | Description |
|----------|-------|-------------|
| `lending` | `positions` | User supply/borrow positions |
| `lending` | `markets` | Market stats, APYs |
| `lending` | `config` | Protocol parameters |
| `loan.staking` | `stakers` | LOAN staking positions |
| `oracles` | `data` | Price feeds |

### Important Parameters

| Parameter | Description |
|-----------|-------------|
| Liquidation Threshold | Health factor below 1.0 |
| Close Factor | Max % of debt repayable per liquidation |
| Liquidation Bonus | Reward for liquidators |
| Reserve Factor | % of interest going to reserves |
