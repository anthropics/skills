# Token Creation on XPR Network

This guide covers creating and managing fungible tokens on XPR Network.

## Token Basics

### Token Structure

Tokens on XPR Network consist of:
- **Symbol**: 1-7 uppercase letters (e.g., `XPR`, `MYTOKEN`)
- **Precision**: Decimal places (0-18, typically 4-8)
- **Contract**: Account that hosts the token (e.g., `eosio.token`)
- **Supply**: Maximum and current circulating supply

### Common Token Contracts

| Token | Contract | Precision |
|-------|----------|-----------|
| XPR | `eosio.token` | 4 |
| XUSDT | `xtokens` | 6 |
| XUSDC | `xtokens` | 6 |
| XBTC | `xtokens` | 8 |
| LOAN | `loan.token` | 4 |

---

## Creating a Token

To create a custom token, you need to deploy your own token contract. The `xtokens` contract listed above is a system contract for official wrapped tokens (XUSDT, XUSDC, XBTC) and is not available for public use.

### Deploy Your Own Token Contract

#### 1. Create Token Contract

```typescript
// assembly/token.ts
import {
  Contract, Table, TableStore, Name, Asset, Symbol,
  check, requireAuth, isAccount, hasAuth
} from 'proton-tsc';

// Currency stats table
@table("stat")
class CurrencyStats extends Table {
  constructor(
    public supply: Asset = new Asset(),
    public max_supply: Asset = new Asset(),
    public issuer: Name = new Name()
  ) { super(); }

  @primary
  get primary(): u64 { return this.supply.symbol.code(); }
}

// Account balances table
@table("accounts")
class Account extends Table {
  constructor(
    public balance: Asset = new Asset()
  ) { super(); }

  @primary
  get primary(): u64 { return this.balance.symbol.code(); }
}

@contract
class Token extends Contract {
  // Create a new token
  @action("create")
  create(issuer: Name, maximum_supply: Asset): void {
    requireAuth(this.receiver);

    const sym = maximum_supply.symbol;
    check(sym.isValid(), "Invalid symbol");
    check(maximum_supply.isValid(), "Invalid supply");
    check(maximum_supply.amount > 0, "Max supply must be positive");

    const statsTable = new TableStore<CurrencyStats>(this.receiver, sym.code());
    check(!statsTable.exists(sym.code()), "Token already exists");

    const stats = new CurrencyStats(
      new Asset(0, sym),
      maximum_supply,
      issuer
    );
    statsTable.store(stats, this.receiver);
  }

  // Issue tokens to account
  @action("issue")
  issue(to: Name, quantity: Asset, memo: string): void {
    const sym = quantity.symbol;
    check(sym.isValid(), "Invalid symbol");
    check(memo.length <= 256, "Memo too long");

    const statsTable = new TableStore<CurrencyStats>(this.receiver, sym.code());
    const stats = statsTable.requireGet(sym.code(), "Token does not exist");

    requireAuth(stats.issuer);

    check(quantity.isValid(), "Invalid quantity");
    check(quantity.amount > 0, "Must issue positive quantity");
    check(quantity.symbol == stats.max_supply.symbol, "Symbol mismatch");
    check(quantity.amount <= stats.max_supply.amount - stats.supply.amount, "Exceeds max supply");

    stats.supply.amount += quantity.amount;
    statsTable.update(stats, stats.issuer);

    this.addBalance(to, quantity, stats.issuer);
  }

  // Retire (burn) tokens
  @action("retire")
  retire(quantity: Asset, memo: string): void {
    const sym = quantity.symbol;
    check(sym.isValid(), "Invalid symbol");
    check(memo.length <= 256, "Memo too long");

    const statsTable = new TableStore<CurrencyStats>(this.receiver, sym.code());
    const stats = statsTable.requireGet(sym.code(), "Token does not exist");

    requireAuth(stats.issuer);

    check(quantity.isValid(), "Invalid quantity");
    check(quantity.amount > 0, "Must retire positive quantity");
    check(quantity.symbol == stats.supply.symbol, "Symbol mismatch");

    stats.supply.amount -= quantity.amount;
    statsTable.update(stats, stats.issuer);

    this.subBalance(stats.issuer, quantity);
  }

  // Transfer tokens
  @action("transfer")
  transfer(from: Name, to: Name, quantity: Asset, memo: string): void {
    check(from != to, "Cannot transfer to self");
    requireAuth(from);
    check(isAccount(to), "Recipient does not exist");

    const sym = quantity.symbol;
    const statsTable = new TableStore<CurrencyStats>(this.receiver, sym.code());
    const stats = statsTable.requireGet(sym.code(), "Token does not exist");

    // Notify sender and receiver
    this.requireRecipient(from);
    this.requireRecipient(to);

    check(quantity.isValid(), "Invalid quantity");
    check(quantity.amount > 0, "Must transfer positive quantity");
    check(quantity.symbol == stats.supply.symbol, "Symbol mismatch");
    check(memo.length <= 256, "Memo too long");

    const payer = hasAuth(to) ? to : from;

    this.subBalance(from, quantity);
    this.addBalance(to, quantity, payer);
  }

  // Open balance (allows receiving without sender paying RAM)
  @action("open")
  open(owner: Name, symbol: Symbol, ram_payer: Name): void {
    requireAuth(ram_payer);

    const statsTable = new TableStore<CurrencyStats>(this.receiver, symbol.code());
    check(statsTable.exists(symbol.code()), "Token does not exist");

    const accountsTable = new TableStore<Account>(this.receiver, owner.N);
    if (!accountsTable.exists(symbol.code())) {
      const account = new Account(new Asset(0, symbol));
      accountsTable.store(account, ram_payer);
    }
  }

  // Close zero balance
  @action("close")
  close(owner: Name, symbol: Symbol): void {
    requireAuth(owner);

    const accountsTable = new TableStore<Account>(this.receiver, owner.N);
    const account = accountsTable.requireGet(symbol.code(), "Balance not found");
    check(account.balance.amount == 0, "Cannot close non-zero balance");
    accountsTable.remove(account);
  }

  // Helper: subtract from balance
  private subBalance(owner: Name, value: Asset): void {
    const accountsTable = new TableStore<Account>(this.receiver, owner.N);
    const from = accountsTable.requireGet(value.symbol.code(), "No balance");
    check(from.balance.amount >= value.amount, "Insufficient balance");

    from.balance.amount -= value.amount;
    accountsTable.update(from, owner);
  }

  // Helper: add to balance
  private addBalance(owner: Name, value: Asset, ram_payer: Name): void {
    const accountsTable = new TableStore<Account>(this.receiver, owner.N);
    let to = accountsTable.get(value.symbol.code());

    if (!to) {
      to = new Account(value);
      accountsTable.store(to, ram_payer);
    } else {
      to.balance.amount += value.amount;
      accountsTable.update(to, ram_payer);
    }
  }
}
```

#### 2. Build and Deploy

```bash
# Build
npm run build

# Deploy
proton contract:set mytokencontract ./assembly/target

# Create token (1 billion max supply, 4 decimals)
proton action mytokencontract create \
  '{"issuer":"mytokencontract","maximum_supply":"1000000000.0000 MYTKN"}' \
  mytokencontract
```

#### 3. Issue Tokens

```bash
# Issue to yourself
proton action mytokencontract issue \
  '{"to":"mytokencontract","quantity":"1000000.0000 MYTKN","memo":"Initial issuance"}' \
  mytokencontract

# Transfer to users
proton action mytokencontract transfer \
  '{"from":"mytokencontract","to":"alice","quantity":"1000.0000 MYTKN","memo":"Airdrop"}' \
  mytokencontract
```

---

## Token Operations

### Check Token Supply

```bash
proton table mytokencontract stat
```

### Check Balance

```bash
proton table mytokencontract accounts alice
```

### Transfer Tokens (Frontend)

```typescript
async function transferToken(
  session: any,
  tokenContract: string,
  to: string,
  quantity: string,
  memo: string = ''
) {
  return session.transact({
    actions: [{
      account: tokenContract,
      name: 'transfer',
      authorization: [session.auth],
      data: {
        from: session.auth.actor,
        to,
        quantity,
        memo
      }
    }]
  }, { broadcast: true });
}

// Usage
await transferToken(session, 'mytokencontract', 'bob', '100.0000 MYTKN', 'Payment');
```

### Query Balance (Frontend)

```typescript
async function getTokenBalance(
  account: string,
  tokenContract: string,
  symbol: string
): Promise<string> {
  const { rows } = await rpc.get_table_rows({
    code: tokenContract,
    scope: account,
    table: 'accounts',
    limit: 100
  });

  const balance = rows.find((r: any) => r.balance.includes(symbol));
  return balance?.balance ?? `0.0000 ${symbol}`;
}
```

---

## Token with Extended Features

### Pausable Token

```typescript
@table("config", singleton)
class Config extends Table {
  constructor(
    public paused: boolean = false,
    public owner: Name = new Name()
  ) { super(); }
}

@action("transfer")
transfer(from: Name, to: Name, quantity: Asset, memo: string): void {
  const config = this.configSingleton.get();
  check(!config.paused, "Token transfers are paused");

  // ... standard transfer logic
}

@action("pause")
pause(paused: boolean): void {
  const config = this.configSingleton.get();
  requireAuth(config.owner);
  config.paused = paused;
  this.configSingleton.set(config, this.receiver);
}
```

### Mintable Token (with cap)

```typescript
@action("mint")
mint(to: Name, quantity: Asset): void {
  const config = this.configSingleton.get();
  requireAuth(config.owner);

  // Check against max supply
  const statsTable = new TableStore<CurrencyStats>(this.receiver, quantity.symbol.code());
  const stats = statsTable.requireGet(quantity.symbol.code(), "Token not found");

  check(
    stats.supply.amount + quantity.amount <= stats.max_supply.amount,
    "Would exceed max supply"
  );

  stats.supply.amount += quantity.amount;
  statsTable.update(stats, this.receiver);

  this.addBalance(to, quantity, this.receiver);
}
```

### Burnable Token

```typescript
@action("burn")
burn(from: Name, quantity: Asset, memo: string): void {
  requireAuth(from);

  const statsTable = new TableStore<CurrencyStats>(this.receiver, quantity.symbol.code());
  const stats = statsTable.requireGet(quantity.symbol.code(), "Token not found");

  this.subBalance(from, quantity);

  stats.supply.amount -= quantity.amount;
  statsTable.update(stats, from);
}
```

### Transfer Fee Token

```typescript
@table("config", singleton)
class Config extends Table {
  constructor(
    public fee_percent: u16 = 100,  // 1% = 100 basis points
    public fee_receiver: Name = new Name()
  ) { super(); }
}

@action("transfer")
transfer(from: Name, to: Name, quantity: Asset, memo: string): void {
  check(from != to, "Cannot transfer to self");
  requireAuth(from);

  const config = this.configSingleton.get();

  // Calculate fee
  const feeAmount = (quantity.amount * config.fee_percent) / 10000;
  const netAmount = quantity.amount - feeAmount;

  // Transfer net amount to recipient
  this.subBalance(from, quantity);
  this.addBalance(to, new Asset(netAmount, quantity.symbol), from);

  // Transfer fee to fee receiver
  if (feeAmount > 0) {
    this.addBalance(config.fee_receiver, new Asset(feeAmount, quantity.symbol), from);
  }
}
```

---

## Wrapped Tokens

Wrapped tokens represent assets from other chains:

### Wrap Pattern

```typescript
@action("wrap")
wrap(account: Name, amount: u64, txHash: string): void {
  // Only bridge contract can wrap
  requireAuth(this.receiver);

  // Verify tx hash hasn't been used
  check(!this.usedHashes.exists(txHash), "Already wrapped");

  // Record hash
  this.usedHashes.store(new UsedHash(txHash), this.receiver);

  // Mint wrapped tokens
  const quantity = new Asset(amount, WRAPPED_SYMBOL);
  this.addBalance(account, quantity, this.receiver);
}

@action("unwrap")
unwrap(account: Name, quantity: Asset, destinationAddress: string): void {
  requireAuth(account);

  // Burn wrapped tokens
  this.subBalance(account, quantity);

  // Emit event for bridge to process
  // (Bridge monitors this and releases original tokens)
}
```

---

## List Token on DEX

### Add to MetalX

1. Ensure token contract is deployed
2. Create liquidity pool:

```typescript
// Add liquidity to XPR/MYTKN pool
const actions = [
  {
    account: 'eosio.token',
    name: 'transfer',
    authorization: [{ actor: account, permission: 'active' }],
    data: {
      from: account,
      to: 'swap.mtl',
      quantity: '10000.0000 XPR',
      memo: 'addliq:MYTKN'
    }
  },
  {
    account: 'mytokencontract',
    name: 'transfer',
    authorization: [{ actor: account, permission: 'active' }],
    data: {
      from: account,
      to: 'swap.mtl',
      quantity: '1000000.0000 MYTKN',
      memo: 'addliq:XPR'
    }
  }
];
```

---

## Airdrop Tokens

### Batch Transfer Script

```typescript
async function airdrop(
  recipients: Array<{ account: string; amount: string }>,
  tokenContract: string,
  batchSize: number = 50
) {
  for (let i = 0; i < recipients.length; i += batchSize) {
    const batch = recipients.slice(i, i + batchSize);

    const actions = batch.map(r => ({
      account: tokenContract,
      name: 'transfer',
      authorization: [{ actor: issuer, permission: 'active' }],
      data: {
        from: issuer,
        to: r.account,
        quantity: r.amount,
        memo: 'Airdrop'
      }
    }));

    await api.transact({ actions }, { blocksBehind: 3, expireSeconds: 30 });

    // Rate limit
    await new Promise(r => setTimeout(r, 500));
  }
}
```

---

## Token Vesting

```typescript
@table("vesting")
class VestingSchedule extends Table {
  constructor(
    public id: u64 = 0,
    public beneficiary: Name = new Name(),
    public total_amount: u64 = 0,
    public claimed_amount: u64 = 0,
    public start_time: u64 = 0,
    public cliff_duration: u64 = 0,
    public vesting_duration: u64 = 0
  ) { super(); }

  @primary
  get primary(): u64 { return this.id; }

  @secondary
  get byBeneficiary(): u64 { return this.beneficiary.N; }
}

@action("createvest")
createVesting(
  beneficiary: Name,
  amount: Asset,
  cliffDays: u32,
  vestingDays: u32
): void {
  requireAuth(this.receiver);

  const schedule = new VestingSchedule(
    this.vestingTable.availablePrimaryKey,
    beneficiary,
    amount.amount,
    0,
    currentTimeSec(),
    cliffDays * 86400,
    vestingDays * 86400
  );

  this.vestingTable.store(schedule, this.receiver);
}

@action("claim")
claim(vestingId: u64): void {
  const schedule = this.vestingTable.requireGet(vestingId, "Vesting not found");
  requireAuth(schedule.beneficiary);

  const now = currentTimeSec();
  const elapsed = now - schedule.start_time;

  // Check cliff
  check(elapsed >= schedule.cliff_duration, "Still in cliff period");

  // Calculate vested amount
  let vestedAmount: u64;
  if (elapsed >= schedule.vesting_duration) {
    vestedAmount = schedule.total_amount;
  } else {
    vestedAmount = (schedule.total_amount * elapsed) / schedule.vesting_duration;
  }

  const claimable = vestedAmount - schedule.claimed_amount;
  check(claimable > 0, "Nothing to claim");

  // Update claimed
  schedule.claimed_amount += claimable;
  this.vestingTable.update(schedule, this.receiver);

  // Transfer tokens
  this.transferTokens(schedule.beneficiary, claimable);
}
```

---

## Quick Reference

### Token Creation Commands

```bash
# Create token (via CLI)
proton action TOKEN_CONTRACT create '{"issuer":"ISSUER","maximum_supply":"AMOUNT SYMBOL"}' TOKEN_CONTRACT

# Issue tokens
proton action TOKEN_CONTRACT issue '{"to":"RECIPIENT","quantity":"AMOUNT SYMBOL","memo":""}' ISSUER

# Transfer
proton action TOKEN_CONTRACT transfer '{"from":"FROM","to":"TO","quantity":"AMOUNT SYMBOL","memo":""}' FROM

# Check supply
proton table TOKEN_CONTRACT stat

# Check balance
proton table TOKEN_CONTRACT accounts ACCOUNT
```

### Symbol Format

```
"1000.0000 XPR"    # 4 decimals
"1.000000 XUSDT"   # 6 decimals
"0.00000001 XBTC"  # 8 decimals
```

Always match the precision defined when token was created.
