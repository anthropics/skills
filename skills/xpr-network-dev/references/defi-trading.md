# DeFi and Trading on XPR Network

This guide covers DEX interaction, trading patterns, and building blocks for advanced DeFi applications including perpetual futures.

## MetalX DEX Overview

MetalX is the primary decentralized exchange on XPR Network - an order book DEX for spot trading.

### Endpoints

| Network | RPC | DEX API |
|---------|-----|---------|
| Mainnet | `https://rpc.api.mainnet.metalx.com` | `https://dex.api.mainnet.metalx.com/dex` |

### Key Contracts

| Contract | Purpose |
|----------|---------|
| `dex` | Order book and matching engine |
| `eosio.token` | XPR and wrapped tokens |
| `xtokens` | Wrapped tokens (XUSDT, XBTC, etc.) |

---

## DEX API Queries

### Get All Markets

```typescript
async function getMarkets() {
  const response = await fetch('https://dex.api.mainnet.metalx.com/dex/v1/markets/all');
  const { data } = await response.json();
  return data;
}

// Response includes:
// - market_id
// - base_token (e.g., XPR)
// - quote_token (e.g., XUSDT)
// - base_precision, quote_precision
// - min_order_size
// - status
```

### Get Order Book

```typescript
async function getOrderBook(marketId: string) {
  const response = await fetch(
    `https://dex.api.mainnet.metalx.com/dex/v1/orders/depth?market_id=${marketId}`
  );
  const { data } = await response.json();
  return data;  // { bids: [...], asks: [...] }
}
```

### Get Latest Price

```typescript
async function getLatestPrice(marketId: string) {
  const response = await fetch(
    `https://dex.api.mainnet.metalx.com/dex/v1/trades/daily?market_id=${marketId}`
  );
  const { data } = await response.json();
  return data;  // { last_price, high_24h, low_24h, volume_24h, ... }
}
```

### Get Trade History

```typescript
async function getTradeHistory(marketId: string, limit: number = 50) {
  const response = await fetch(
    `https://dex.api.mainnet.metalx.com/dex/v1/trades/recent?market_id=${marketId}&limit=${limit}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get User's Open Orders

```typescript
async function getOpenOrders(account: string, marketId?: string) {
  let url = `https://dex.api.mainnet.metalx.com/dex/v1/orders/open?account=${account}`;
  if (marketId) {
    url += `&market_id=${marketId}`;
  }
  const response = await fetch(url);
  const { data } = await response.json();
  return data;
}
```

### Get User Balances

```typescript
async function getDexBalances(account: string) {
  const response = await fetch(
    `https://dex.api.mainnet.metalx.com/dex/v1/account/balances?account=${account}`
  );
  const { data } = await response.json();
  return data;
}
```

---

## DEX Trading Transactions

### Place Limit Order

```typescript
async function placeLimitOrder(
  account: string,
  marketId: string,
  side: 'buy' | 'sell',
  price: string,
  quantity: string
) {
  const actions = [{
    account: 'dex',
    name: 'placeorder',
    authorization: [{ actor: account, permission: 'active' }],
    data: {
      account,
      market_id: marketId,
      side: side === 'buy' ? 1 : 2,
      type: 1,  // 1 = limit
      price,
      quantity,
      post_only: false,
      client_order_id: Date.now()  // Optional tracking ID
    }
  }];

  return session.transact({ actions }, { broadcast: true });
}
```

### Place Market Order

```typescript
async function placeMarketOrder(
  account: string,
  marketId: string,
  side: 'buy' | 'sell',
  quantity: string
) {
  const actions = [{
    account: 'dex',
    name: 'placeorder',
    authorization: [{ actor: account, permission: 'active' }],
    data: {
      account,
      market_id: marketId,
      side: side === 'buy' ? 1 : 2,
      type: 2,  // 2 = market
      price: '0',  // Ignored for market orders
      quantity,
      post_only: false,
      client_order_id: Date.now()
    }
  }];

  return session.transact({ actions }, { broadcast: true });
}
```

### Cancel Order

```typescript
async function cancelOrder(account: string, orderId: string) {
  const actions = [{
    account: 'dex',
    name: 'cancelorder',
    authorization: [{ actor: account, permission: 'active' }],
    data: {
      account,
      order_id: orderId
    }
  }];

  return session.transact({ actions }, { broadcast: true });
}
```

### Cancel All Orders

```typescript
async function cancelAllOrders(account: string, marketId?: string) {
  const actions = [{
    account: 'dex',
    name: 'cancelall',
    authorization: [{ actor: account, permission: 'active' }],
    data: {
      account,
      market_id: marketId || ''  // Empty = all markets
    }
  }];

  return session.transact({ actions }, { broadcast: true });
}
```

### Deposit to DEX

```typescript
async function depositToDex(account: string, quantity: string, tokenContract: string) {
  const actions = [{
    account: tokenContract,
    name: 'transfer',
    authorization: [{ actor: account, permission: 'active' }],
    data: {
      from: account,
      to: 'dex',
      quantity,
      memo: 'deposit'
    }
  }];

  return session.transact({ actions }, { broadcast: true });
}
```

### Withdraw from DEX

```typescript
async function withdrawFromDex(account: string, quantity: string) {
  const actions = [{
    account: 'dex',
    name: 'withdraw',
    authorization: [{ actor: account, permission: 'active' }],
    data: {
      account,
      quantity
    }
  }];

  return session.transact({ actions }, { broadcast: true });
}
```

---

## Trading Bot Patterns

### Grid Bot Strategy

```typescript
interface GridConfig {
  marketId: string;
  lowerPrice: number;
  upperPrice: number;
  gridLevels: number;
  quantityPerGrid: string;
}

class GridBot {
  private config: GridConfig;
  private gridPrices: number[] = [];

  constructor(config: GridConfig) {
    this.config = config;
    this.calculateGridPrices();
  }

  private calculateGridPrices() {
    const { lowerPrice, upperPrice, gridLevels } = this.config;
    const step = (upperPrice - lowerPrice) / (gridLevels - 1);

    for (let i = 0; i < gridLevels; i++) {
      this.gridPrices.push(lowerPrice + step * i);
    }
  }

  async placeInitialOrders(currentPrice: number) {
    const orders: Promise<any>[] = [];

    for (const gridPrice of this.gridPrices) {
      if (gridPrice < currentPrice) {
        // Place buy order below current price
        orders.push(this.placeBuyOrder(gridPrice));
      } else if (gridPrice > currentPrice) {
        // Place sell order above current price
        orders.push(this.placeSellOrder(gridPrice));
      }
    }

    return Promise.all(orders);
  }

  private async placeBuyOrder(price: number) {
    return placeLimitOrder(
      this.account,
      this.config.marketId,
      'buy',
      price.toFixed(4),
      this.config.quantityPerGrid
    );
  }

  private async placeSellOrder(price: number) {
    return placeLimitOrder(
      this.account,
      this.config.marketId,
      'sell',
      price.toFixed(4),
      this.config.quantityPerGrid
    );
  }

  // Called when an order fills
  async onOrderFilled(filledOrder: Order) {
    const gridIndex = this.findGridIndex(parseFloat(filledOrder.price));

    if (filledOrder.side === 'buy') {
      // Buy filled - place sell at next grid up
      const sellPrice = this.gridPrices[gridIndex + 1];
      if (sellPrice) {
        await this.placeSellOrder(sellPrice);
      }
    } else {
      // Sell filled - place buy at next grid down
      const buyPrice = this.gridPrices[gridIndex - 1];
      if (buyPrice) {
        await this.placeBuyOrder(buyPrice);
      }
    }
  }
}
```

### Market Maker Strategy

```typescript
interface MarketMakerConfig {
  marketId: string;
  spread: number;      // e.g., 0.002 for 0.2%
  levels: number;      // Orders per side
  levelSpacing: number; // e.g., 0.001 for 0.1%
  quantityPerLevel: string;
}

class MarketMaker {
  private config: MarketMakerConfig;

  async updateQuotes(midPrice: number) {
    // Cancel existing orders
    await cancelAllOrders(this.account, this.config.marketId);

    const orders: Promise<any>[] = [];

    for (let i = 0; i < this.config.levels; i++) {
      const offset = this.config.spread / 2 + i * this.config.levelSpacing;

      // Bid (buy)
      const bidPrice = midPrice * (1 - offset);
      orders.push(placeLimitOrder(
        this.account,
        this.config.marketId,
        'buy',
        bidPrice.toFixed(4),
        this.config.quantityPerLevel
      ));

      // Ask (sell)
      const askPrice = midPrice * (1 + offset);
      orders.push(placeLimitOrder(
        this.account,
        this.config.marketId,
        'sell',
        askPrice.toFixed(4),
        this.config.quantityPerLevel
      ));
    }

    return Promise.all(orders);
  }
}
```

---

## Building a Perpetual Futures DEX

A perps DEX on XPR Network would require these components:

### 1. Core Tables

```typescript
// Positions table
@table("positions")
class Position extends Table {
  constructor(
    public id: u64 = 0,
    public trader: Name = new Name(),
    public market: string = "",         // e.g., "BTC-PERP"
    public side: u8 = 0,                // 1=long, 2=short
    public size: u64 = 0,               // Position size (base units)
    public entry_price: u64 = 0,        // Average entry (8 decimals)
    public leverage: u8 = 1,            // 1-100x
    public collateral: u64 = 0,         // Margin deposited
    public unrealized_pnl: i64 = 0,     // Current PnL
    public last_funding_time: u64 = 0,  // Last funding payment
    public liquidation_price: u64 = 0   // Auto-liquidation price
  ) { super(); }

  @primary
  get primary(): u64 { return this.id; }

  @secondary
  get byTrader(): u64 { return this.trader.N; }
}

// Markets configuration
@table("markets")
class Market extends Table {
  constructor(
    public market_id: string = "",
    public oracle_index: u8 = 0,         // Oracle feed index
    public max_leverage: u8 = 20,        // Max allowed leverage
    public maintenance_margin: u16 = 500, // 5% in basis points
    public initial_margin: u16 = 1000,    // 10% in basis points
    public funding_interval: u32 = 3600,  // 1 hour
    public maker_fee: u16 = 10,           // 0.1% in basis points
    public taker_fee: u16 = 50,           // 0.5% in basis points
    public open_interest_long: u64 = 0,
    public open_interest_short: u64 = 0
  ) { super(); }

  @primary
  get primary(): string { return this.market_id; }
}

// Funding rate history
@table("funding")
class FundingRate extends Table {
  constructor(
    public id: u64 = 0,
    public market_id: string = "",
    public timestamp: u64 = 0,
    public funding_rate: i64 = 0,  // Can be negative
    public mark_price: u64 = 0,
    public index_price: u64 = 0
  ) { super(); }

  @primary
  get primary(): u64 { return this.id; }
}

// Insurance fund
@table("insurance", singleton)
class InsuranceFund extends Table {
  constructor(
    public balance: u64 = 0,
    public last_contribution: u64 = 0
  ) { super(); }
}
```

### 2. Oracle Integration for Mark Price

```typescript
// Mark price = TWAP of oracle + funding premium
async function getMarkPrice(marketId: string): Promise<u64> {
  const market = await getMarket(marketId);

  // Get index price from oracle
  const indexPrice = await getOraclePrice(market.oracle_index);

  // Get order book mid price from DEX
  const orderBook = await getOrderBook(marketId);
  const midPrice = calculateMidPrice(orderBook);

  // Calculate funding premium
  const premium = calculatePremium(midPrice, indexPrice);

  // Mark price includes premium
  return indexPrice + premium;
}

function calculatePremium(midPrice: u64, indexPrice: u64): i64 {
  // Premium = (Mid Price - Index Price) / Index Price
  // Dampened over time
  return ((midPrice - indexPrice) * 10000) / indexPrice;
}
```

### 3. Margin and Leverage

```typescript
@action("openposition")
openPosition(
  trader: Name,
  market: string,
  side: u8,          // 1=long, 2=short
  size: u64,         // Position size
  leverage: u8,      // 1-100
  collateral: Asset  // Margin to deposit
): void {
  requireAuth(trader);

  const marketConfig = this.marketsTable.requireGet(market, "Market not found");

  // Validate leverage
  check(leverage >= 1 && leverage <= marketConfig.max_leverage, "Invalid leverage");

  // Calculate required margin
  const markPrice = this.getMarkPrice(market);
  const notionalValue = (size * markPrice) / PRICE_PRECISION;
  const requiredMargin = (notionalValue * marketConfig.initial_margin) / 10000;

  check(collateral.amount >= requiredMargin, "Insufficient margin");

  // Calculate liquidation price
  const liquidationPrice = this.calculateLiquidationPrice(
    side,
    markPrice,
    leverage,
    marketConfig.maintenance_margin
  );

  // Create position
  const position = new Position(
    this.getNextPositionId(),
    trader,
    market,
    side,
    size,
    markPrice,
    leverage,
    collateral.amount,
    0,  // unrealized PnL starts at 0
    currentTimeSec(),
    liquidationPrice
  );

  this.positionsTable.store(position, trader);

  // Update open interest
  if (side == 1) {
    marketConfig.open_interest_long += size;
  } else {
    marketConfig.open_interest_short += size;
  }
  this.marketsTable.update(marketConfig, this.receiver);
}

function calculateLiquidationPrice(
  side: u8,
  entryPrice: u64,
  leverage: u8,
  maintenanceMargin: u16
): u64 {
  // For longs: Liq Price = Entry * (1 - 1/leverage + maintenance_margin)
  // For shorts: Liq Price = Entry * (1 + 1/leverage - maintenance_margin)

  const leverageFactor = PRECISION / leverage;
  const marginFactor = (maintenanceMargin * PRECISION) / 10000;

  if (side == 1) {  // Long
    return (entryPrice * (PRECISION - leverageFactor + marginFactor)) / PRECISION;
  } else {  // Short
    return (entryPrice * (PRECISION + leverageFactor - marginFactor)) / PRECISION;
  }
}
```

### 4. Funding Rate Mechanism

```typescript
@action("applyfunding")
applyFunding(market: string): void {
  const marketConfig = this.marketsTable.requireGet(market, "Market not found");
  const now = currentTimeSec();

  // Check if funding interval has passed
  check(
    now >= this.lastFundingTime(market) + marketConfig.funding_interval,
    "Funding not due yet"
  );

  // Calculate funding rate
  const markPrice = this.getMarkPrice(market);
  const indexPrice = this.getOraclePrice(marketConfig.oracle_index);

  // Funding Rate = (Mark Price - Index Price) / Index Price * 0.01
  // Clamped to max ±0.1% per interval
  let fundingRate = ((markPrice - indexPrice) * 100) / indexPrice;
  fundingRate = clamp(fundingRate, -1000, 1000);  // ±0.1%

  // Apply to all positions
  let cursor = this.positionsTable.lowerBound(market);
  while (cursor && cursor.market == market) {
    const payment = this.calculateFundingPayment(cursor, fundingRate);

    if (cursor.side == 1) {
      // Longs pay when funding > 0
      cursor.collateral -= payment;
    } else {
      // Shorts receive when funding > 0
      cursor.collateral += payment;
    }

    cursor.last_funding_time = now;
    this.positionsTable.update(cursor, this.receiver);

    cursor = this.positionsTable.next(cursor);
  }

  // Record funding rate
  this.recordFunding(market, fundingRate, markPrice, indexPrice);
}
```

### 5. Liquidation System

```typescript
@action("liquidate")
liquidate(positionId: u64, liquidator: Name): void {
  requireAuth(liquidator);

  const position = this.positionsTable.requireGet(positionId, "Position not found");
  const markPrice = this.getMarkPrice(position.market);

  // Check if position is liquidatable
  const isLiquidatable = this.checkLiquidation(position, markPrice);
  check(isLiquidatable, "Position not liquidatable");

  // Calculate liquidation penalty
  const market = this.marketsTable.get(position.market);
  const penalty = (position.collateral * LIQUIDATION_PENALTY) / 10000;

  // Pay liquidator reward (portion of penalty)
  const liquidatorReward = (penalty * LIQUIDATOR_SHARE) / 100;
  this.transferReward(liquidator, liquidatorReward);

  // Send remainder to insurance fund
  const insuranceContribution = penalty - liquidatorReward;
  this.addToInsurance(insuranceContribution);

  // Close position
  this.closePosition(position, markPrice, true);  // true = liquidation
}

function checkLiquidation(position: Position, markPrice: u64): boolean {
  // Calculate unrealized PnL
  let pnl: i64;
  if (position.side == 1) {  // Long
    pnl = ((markPrice - position.entry_price) * position.size) / PRICE_PRECISION;
  } else {  // Short
    pnl = ((position.entry_price - markPrice) * position.size) / PRICE_PRECISION;
  }

  // Calculate margin ratio
  const equity = position.collateral + pnl;
  const notional = (position.size * markPrice) / PRICE_PRECISION;
  const marginRatio = (equity * 10000) / notional;

  // Liquidate if below maintenance margin
  const market = this.marketsTable.get(position.market);
  return marginRatio < market.maintenance_margin;
}
```

### 6. Order Matching (Limit Orders)

```typescript
@table("orders")
class Order extends Table {
  constructor(
    public id: u64 = 0,
    public trader: Name = new Name(),
    public market: string = "",
    public side: u8 = 0,        // 1=long, 2=short
    public price: u64 = 0,
    public size: u64 = 0,
    public filled: u64 = 0,
    public reduce_only: bool = false,
    public post_only: bool = false,
    public timestamp: u64 = 0
  ) { super(); }

  @primary
  get primary(): u64 { return this.id; }

  @secondary  // For order book sorting
  get byPrice(): u64 { return this.price; }
}

@action("placeorder")
placeOrder(
  trader: Name,
  market: string,
  side: u8,
  price: u64,
  size: u64,
  reduceOnly: bool,
  postOnly: bool
): void {
  requireAuth(trader);

  // Validate order
  // ...

  // Check for matching orders
  const matchingOrders = this.findMatchingOrders(market, side, price);

  for (const match of matchingOrders) {
    if (postOnly) {
      check(false, "Order would cross - post-only rejected");
    }

    // Execute match
    this.executeMatch(trader, match, size);
  }

  // Place remainder on book
  if (size > 0) {
    const order = new Order(
      this.getNextOrderId(),
      trader,
      market,
      side,
      price,
      size,
      0,
      reduceOnly,
      postOnly,
      currentTimeSec()
    );
    this.ordersTable.store(order, trader);
  }
}
```

---

## Required Infrastructure

To build a production perps DEX:

### Smart Contracts

| Contract | Purpose |
|----------|---------|
| `perps.core` | Positions, orders, matching |
| `perps.oracle` | Mark price calculation, TWAP |
| `perps.liquidation` | Liquidation bot rewards |
| `perps.insurance` | Insurance fund management |

### Backend Services

| Service | Purpose |
|---------|---------|
| Liquidation Bot | Monitor positions, trigger liquidations |
| Funding Bot | Apply funding rates on schedule |
| Oracle Aggregator | Fetch prices, calculate TWAP |
| Order Indexer | Fast order book queries |

### Frontend

- Real-time position tracking
- P&L calculations
- Order book visualization
- Leverage slider with liquidation price preview

---

## Security Considerations

### For Perps DEX

1. **Oracle Manipulation** - Use TWAP, multiple sources
2. **Flash Loan Attacks** - Require position to be held for min time
3. **Cascading Liquidations** - Insurance fund, position limits
4. **Front-Running** - Time-weighted execution, commit-reveal
5. **Smart Contract Risk** - Audits, bug bounties, gradual rollout

### Rate Limiting

```typescript
// Prevent spam orders
const MAX_ORDERS_PER_BLOCK = 10;

@action("placeorder")
placeOrder(...): void {
  const userOrdersThisBlock = this.countRecentOrders(trader);
  check(userOrdersThisBlock < MAX_ORDERS_PER_BLOCK, "Rate limit exceeded");
  // ...
}
```

---

## Resources

- **MetalX DEX**: https://metalx.com
- **XPR DEX Bot**: https://github.com/XPRNetwork/dex-bot
- **Oracle Feeds**: `oracles` contract on XPR Network
- **Perpetual Protocol Concepts**: https://docs.perp.com (reference for perps design)
