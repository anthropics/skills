# Contract Pattern Examples

This document contains common smart contract patterns illustrated through example contracts. These examples demonstrate real-world patterns you can adapt for your own dApps.

**Note**: The contracts shown here (PriceBattle, ProtonWall, ProtonRating) are community examples for educational purposes, not official XPR Network contracts.

---

## PriceBattle: PvP Price Prediction Game

A game where players bet against each other on BTC price movements.

### Game Flow

```
1. Player A creates challenge: "100 XPR on BTC UP in 10 min"
2. Player B accepts (takes DOWN side)
3. After 10 minutes, oracle price is checked
4. Winner takes 95% of pool (190 XPR)
```

### Tables

```typescript
// Configuration (Singleton)
@table("config", singleton)
class Config extends Table {
  constructor(
    public paused: boolean = false,
    public fee_percent: u8 = 5,           // 5% total fee
    public resolver_percent: u8 = 2,       // 2% to resolver
    public min_stake: u64 = 100000,        // 10.0000 XPR
    public max_stake: u64 = 1000000000,    // 100000.0000 XPR
    public min_duration: u32 = 300,        // 5 minutes
    public max_duration: u32 = 86400,      // 24 hours
    public challenge_expiry: u32 = 3600,   // 1 hour to accept
    public min_price_move_bps: u16 = 1,    // 0.01% minimum
    public treasury: Name = new Name()
  ) { super(); }
}

// PvP Challenges
@table("challenges")
class Challenge extends Table {
  constructor(
    public id: u64 = 0,
    public creator: Name = new Name(),
    public opponent: Name = new Name(),
    public amount: u64 = 0,               // Stake in smallest unit
    public direction: u8 = 0,             // 1=UP, 2=DOWN
    public oracle_index: u8 = 4,          // 4=BTC/USD
    public duration: u32 = 0,             // Seconds
    public start_price: u64 = 0,          // 8 decimals
    public end_price: u64 = 0,
    public created_at: u64 = 0,
    public started_at: u64 = 0,
    public status: u8 = 0,                // 0=open, 1=active, 2=resolved
    public winner: Name = new Name()
  ) { super(); }

  @primary
  get primary(): u64 { return this.id; }

  @secondary
  get byStatus(): u64 { return this.status; }

  @secondary
  get byCreator(): u64 { return this.creator.N; }
}

// Player Statistics
@table("stats")
class PlayerStats extends Table {
  constructor(
    public player: Name = new Name(),
    public total_wagered: u64 = 0,
    public total_won: u64 = 0,
    public wins: u32 = 0,
    public losses: u32 = 0,
    public ties: u32 = 0,
    public win_streak: u32 = 0,
    public best_streak: u32 = 0
  ) { super(); }

  @primary
  get primary(): u64 { return this.player.N; }
}
```

### Status Codes

| Code | Status | Description |
|------|--------|-------------|
| 0 | OPEN | Waiting for opponent |
| 1 | ACTIVE | In progress |
| 2 | RESOLVED | Winner determined |
| 3 | CANCELLED | Creator cancelled |
| 4 | EXPIRED | No opponent joined |
| 5 | TIE | Price didn't move enough |

### Oracle Integration

```typescript
// Reading oracle price (done in frontend, passed to contract)
async function getOraclePrice(): Promise<u64> {
  const { rows } = await rpc.get_table_rows({
    code: 'oracles',
    scope: 'oracles',
    table: 'data',
    lower_bound: 4,  // BTC/USD
    upper_bound: 4,
    limit: 1
  });

  // Convert to u64 with 8 decimals
  // $95,322.71 = 9532271000000
  const priceFloat = parseFloat(rows[0].aggregate.d_double);
  return Math.round(priceFloat * 100000000);
}
```

### Fee Distribution

```typescript
// In resolve action
function distributePrize(challenge: Challenge): void {
  const pool = challenge.amount * 2;
  const config = this.configSingleton.get();

  // Calculate fees
  const totalFee = (pool * config.fee_percent) / 100;
  const resolverFee = (pool * config.resolver_percent) / 100;
  const treasuryFee = totalFee - resolverFee;
  const winnerPrize = pool - totalFee;

  // Transfer to winner
  sendInline('eosio.token', 'transfer', {
    from: this.receiver,
    to: challenge.winner,
    quantity: `${formatAsset(winnerPrize)} XPR`,
    memo: `PriceBattle #${challenge.id} winnings`
  });

  // Transfer to treasury
  sendInline('eosio.token', 'transfer', {
    from: this.receiver,
    to: config.treasury,
    quantity: `${formatAsset(treasuryFee)} XPR`,
    memo: `PriceBattle #${challenge.id} treasury fee`
  });

  // Transfer to resolver
  sendInline('eosio.token', 'transfer', {
    from: this.receiver,
    to: resolver,
    quantity: `${formatAsset(resolverFee)} XPR`,
    memo: `PriceBattle #${challenge.id} resolver reward`
  });
}
```

### Resolution Logic

```typescript
function determineWinner(challenge: Challenge): Name {
  // Check for tie (price didn't move enough)
  const priceDiff = challenge.end_price > challenge.start_price
    ? challenge.end_price - challenge.start_price
    : challenge.start_price - challenge.end_price;

  const minMove = (challenge.start_price * config.min_price_move_bps) / 10000;

  if (priceDiff < minMove) {
    return EMPTY_NAME;  // Tie
  }

  const priceWentUp = challenge.end_price > challenge.start_price;
  const creatorPredictedUp = challenge.direction == 1;

  if (priceWentUp == creatorPredictedUp) {
    return challenge.creator;
  } else {
    return challenge.opponent;
  }
}
```

---

## ProtonWall: Social Feed

Twitter-style posting wall with memo-based content creation.

### Pricing

| Action | Cost | Description |
|--------|------|-------------|
| Text Post | 1 XPR | Max 140 characters |
| Image Post | 10 XPR | Post with image URL |
| Pin Post | 100 XPR | Pin to top for 24 hours |
| Reply | 1 XPR | Reply to existing post |

### Memo-Based Posting Pattern

Posts are created by sending XPR to the contract with a specific memo:

```typescript
@action("transfer", notify)
onTransfer(from: Name, to: Name, quantity: Asset, memo: string): void {
  // Only process transfers TO this contract
  if (to != this.receiver) return;

  // Only accept XPR
  if (quantity.symbol != XPR_SYMBOL) return;

  // Parse memo
  if (memo.startsWith("post:")) {
    this.handlePost(from, quantity, memo.substring(5));
  } else if (memo.startsWith("image:")) {
    this.handleImagePost(from, quantity, memo.substring(6));
  } else if (memo.startsWith("pin:")) {
    this.handlePin(from, quantity, memo.substring(4));
  } else if (memo.startsWith("reply:")) {
    this.handleReply(from, quantity, memo.substring(6));
  } else {
    // Invalid memo - refund
    this.refund(from, quantity, "Invalid memo format");
  }
}
```

### Soft Delete for Moderation

```typescript
@table("posts")
class Post extends Table {
  constructor(
    public id: u64 = 0,
    public author: Name = new Name(),
    public content: string = "",
    public image_url: string = "",
    public timestamp: u64 = 0,
    public is_pinned: bool = false,
    public pin_expires: u64 = 0,
    public is_deleted: bool = false  // Soft delete
  ) { super(); }
}

@action("moderate")
moderate(postId: u64, reason: string): void {
  const config = this.configSingleton.get();
  requireAuth(config.owner);  // Only owner can moderate

  const post = this.postTable.requireGet(postId, "Post not found");

  // Soft delete - data remains on chain
  post.is_deleted = true;
  this.postTable.update(post, this.receiver);
}
```

### Automatic Refunds

```typescript
private handlePost(from: Name, quantity: Asset, content: string): void {
  const config = this.configSingleton.get();
  const cost = config.post_cost;

  // Validate
  if (content.length == 0) {
    this.refund(from, quantity, "Content cannot be empty");
    return;
  }

  if (content.length > 140) {
    this.refund(from, quantity, "Content exceeds 140 characters");
    return;
  }

  if (quantity.amount < cost) {
    this.refund(from, quantity, `Insufficient payment. Required: ${cost}`);
    return;
  }

  // Create post
  const post = new Post(
    this.getNextId(),
    from,
    content,
    "",
    currentTimeSec(),
    false,
    0,
    false
  );
  this.postTable.store(post, this.receiver);

  // Refund overpayment
  if (quantity.amount > cost) {
    const refundAmount = quantity.amount - cost;
    this.refund(from, new Asset(refundAmount, XPR_SYMBOL), "Overpayment refund");
  }
}

private refund(to: Name, quantity: Asset, memo: string): void {
  const transfer = new InlineAction<TransferArgs>("eosio.token", "transfer");
  transfer.send(
    [new PermissionLevel(this.receiver, Name.fromString("active"))],
    new TransferArgs(this.receiver, to, quantity, memo)
  );
}
```

---

## Trust/Reputation System Pattern

Example pattern for an account rating system to protect users from bad actors.

### Trust Levels

| Level | Name | Blocks Payments |
|-------|------|-----------------|
| 1 | Scammer | YES |
| 2 | Suspicious | No |
| 3 | Unknown | No (default) |
| 4 | Verified | No |
| 5 | Highly Trusted | No |

### Tables

```typescript
@table("ratings")
class Rating extends Table {
  constructor(
    public account: Name = new Name(),
    public level: u8 = 3,
    public reason: string = "",
    public updated_by: Name = new Name(),
    public updated_at: u64 = 0
  ) { super(); }

  @primary
  get primary(): u64 { return this.account.N; }
}

@table("admins")
class Admin extends Table {
  constructor(
    public account: Name = new Name()
  ) { super(); }

  @primary
  get primary(): u64 { return this.account.N; }
}

@table("config", singleton)
class Config extends Table {
  constructor(
    public owner: Name = new Name()
  ) { super(); }
}
```

### Admin Pattern

```typescript
@action("setrating")
setRating(account: Name, level: u8, reason: string): void {
  // Get caller
  const caller = this.getCaller();

  // Check if caller is admin
  check(this.isAdmin(caller), "Only admins can set ratings");

  // Validate level
  check(level >= 1 && level <= 5, "Level must be 1-5");

  // Set or update rating
  let rating = this.ratingTable.get(account.N);
  if (!rating) {
    rating = new Rating(account, level, reason, caller, currentTimeSec());
    this.ratingTable.store(rating, this.receiver);
  } else {
    rating.level = level;
    rating.reason = reason;
    rating.updated_by = caller;
    rating.updated_at = currentTimeSec();
    this.ratingTable.update(rating, this.receiver);
  }
}

private isAdmin(account: Name): boolean {
  const config = this.configSingleton.get();
  if (account == config.owner) return true;
  return this.adminTable.exists(account.N);
}
```

### Frontend Integration

```typescript
// Fetch rating with KYC fallback
async function getAccountTrustLevel(account: string): Promise<number> {
  // Check explicit rating first
  const ratingRows = await rpc.get_table_rows({
    code: 'protonrating',
    scope: 'protonrating',
    table: 'ratings',
    lower_bound: account,
    upper_bound: account,
    limit: 1
  });

  if (ratingRows.rows.length > 0) {
    return ratingRows.rows[0].level;
  }

  // No explicit rating - check KYC status
  const userInfo = await rpc.get_table_rows({
    code: 'eosio.proton',
    scope: 'eosio.proton',
    table: 'usersinfo',
    lower_bound: account,
    upper_bound: account,
    limit: 1
  });

  if (userInfo.rows.length > 0 && userInfo.rows[0].kyc?.length > 0) {
    return 4;  // Verified (KYC'd)
  }

  return 3;  // Unknown (default)
}
```

---

## Common Patterns

### Auto-Increment ID

```typescript
private getNextId(): u64 {
  const config = this.configSingleton.get();
  const nextId = config.next_id;
  config.next_id = nextId + 1;
  this.configSingleton.set(config, this.receiver);
  return nextId;
}

// Or use TableStore's built-in
const id = this.myTable.availablePrimaryKey;
```

### Pause/Unpause Contract

```typescript
@action("pause")
pause(paused: boolean): void {
  requireAuth(this.receiver);
  const config = this.configSingleton.get();
  config.paused = paused;
  this.configSingleton.set(config, this.receiver);
}

@action("myaction")
myAction(): void {
  const config = this.configSingleton.get();
  check(!config.paused, "Contract is paused");
  // ... action logic
}
```

### Owner Transfer

```typescript
@action("setowner")
setOwner(newOwner: Name): void {
  const config = this.configSingleton.get();
  requireAuth(config.owner);  // Current owner must authorize

  check(isAccount(newOwner), "New owner account does not exist");

  config.owner = newOwner;
  this.configSingleton.set(config, this.receiver);
}
```

### Expiry Cleanup

```typescript
@action("cleanup")
cleanup(limit: u8): void {
  // Anyone can call to clean up expired entries
  const now = currentTimeSec();
  let count: u8 = 0;

  let cursor = this.challengeTable.first();
  while (cursor && count < limit) {
    const next = this.challengeTable.next(cursor);

    // Check if expired
    if (cursor.status == STATUS_OPEN &&
        cursor.created_at + EXPIRY_SECONDS < now) {

      // Refund creator
      this.refund(cursor.creator, cursor.amount);

      // Remove challenge
      this.challengeTable.remove(cursor);
      count++;
    }

    cursor = next;
  }
}
```

### Statistics Tracking

```typescript
private updateStats(player: Name, won: boolean, amount: u64): void {
  let stats = this.statsTable.get(player.N);

  if (!stats) {
    stats = new PlayerStats(player, 0, 0, 0, 0, 0, 0, 0);
  }

  stats.total_wagered += amount;

  if (won) {
    stats.total_won += amount;
    stats.wins++;
    stats.win_streak++;
    if (stats.win_streak > stats.best_streak) {
      stats.best_streak = stats.win_streak;
    }
  } else {
    stats.losses++;
    stats.win_streak = 0;
  }

  this.statsTable.set(stats, this.receiver);
}
```

---

## Frontend Queries for Examples

### Get Open Challenges

```typescript
const { rows } = await rpc.get_table_rows({
  code: 'pricebattle',
  scope: 'pricebattle',
  table: 'challenges',
  index_position: 'secondary',  // status index
  key_type: 'i64',
  lower_bound: 0,  // OPEN
  upper_bound: 0,
  limit: 100
});
```

### Get Latest Posts (Non-Deleted)

```typescript
const { rows } = await rpc.get_table_rows({
  code: 'protonwall',
  scope: 'protonwall',
  table: 'posts',
  reverse: true,
  limit: 50
});

// Filter out deleted in frontend
const visiblePosts = rows.filter(p => !p.is_deleted);
```

### Get Leaderboard

```typescript
const { rows } = await rpc.get_table_rows({
  code: 'pricebattle',
  scope: 'pricebattle',
  table: 'stats',
  limit: 100
});

// Sort by wins in frontend
const leaderboard = rows.sort((a, b) => b.wins - a.wins);
```
