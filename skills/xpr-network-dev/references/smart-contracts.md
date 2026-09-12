# Smart Contract Development on XPR Network

This guide covers AssemblyScript/TypeScript smart contract development using `@proton/ts-contracts` (proton-tsc).

> **Before deploying to mainnet**: Always review AI-generated code, test thoroughly on testnet, and consider having experienced developers review critical contracts. See `safety-guidelines.md` for essential deployment safety rules.

## Overview

XPR Network smart contracts are written in AssemblyScript (a TypeScript-like language that compiles to WebAssembly). The SDK provides decorators and utilities for defining tables, actions, and interacting with the blockchain.

## Project Setup

### Create New Contract

```bash
# Using CLI boilerplate
proton boilerplate myproject

# Or manually
mkdir mycontract && cd mycontract
npm init -y
npm install proton-tsc
```

### Project Structure

```
mycontract/
├── assembly/
│   ├── mycontract.contract.ts   # Main contract file (must end in .contract.ts)
│   └── target/                   # Build output (WASM + ABI)
├── package.json
└── tsconfig.json
```

**Important**: Contract files must be named `*.contract.ts` for the compiler to recognize them.

### package.json Scripts

```json
{
  "scripts": {
    "build": "npx proton-asc ./assembly/mycontract.contract.ts"
  }
}
```

**Note**: The build command is `proton-asc` (AssemblyScript compiler), not `proton-tsc`. The `proton-tsc` package provides the TypeScript types and decorators, while `proton-asc` handles compilation.

---

## Tables (Storage)

Tables are like database tables - define columns (fields) and rows are stored with a primary key.

### Basic Table

```typescript
import { Table, Name } from 'proton-tsc';

@table("users")
export class User extends Table {
  constructor(
    public id: u64 = 0,
    public account: Name = new Name(),
    public balance: u64 = 0,
    public created_at: u64 = 0
  ) {
    super();
  }

  @primary
  get primary(): u64 {
    return this.id;
  }
}
```

### Table Naming Rules

- 1-12 characters
- Lowercase a-z and digits 1-5 only
- No dots, dashes, or uppercase

### Singleton Table (Single Row)

Singletons store a single configuration/state row without needing a primary key.

```typescript
import { Singleton } from 'proton-tsc';

@table("config", singleton)
export class Config extends Table {
  constructor(
    public owner: Name = new Name(),
    public paused: boolean = false,
    public fee_percent: u8 = 5
  ) {
    super();
  }
}

@contract
class MyContract extends Contract {
  // Initialize singleton with contract receiver
  configSingleton: Singleton<Config> = new Singleton<Config>(this.receiver);

  @action("init")
  init(owner: Name): void {
    // Check if already initialized
    const existing = this.configSingleton.get();
    if (existing !== null) {
      check(false, "Already initialized");
    }

    // Set initial config
    const config = new Config(owner, false, 5);
    this.configSingleton.set(config, this.receiver);
  }

  @action("setpaused")
  setPaused(paused: boolean): void {
    const config = this.configSingleton.get();
    check(config !== null, "Not initialized");
    requireAuth(config!.owner);

    config!.paused = paused;
    this.configSingleton.set(config!, this.receiver);
  }

  @action("myaction")
  myAction(): void {
    const config = this.configSingleton.get();
    check(config !== null, "Not initialized");
    check(!config!.paused, "Contract is paused");
    // ... action logic
  }
}
```

**Singleton Methods:**
- `get()` - Returns the singleton value or `null` if not set
- `set(value, payer)` - Sets or updates the singleton value
- `remove()` - Removes the singleton value

### Secondary Indexes

```typescript
@table("posts")
export class Post extends Table {
  constructor(
    public id: u64 = 0,
    public author: Name = new Name(),
    public content: string = "",
    public timestamp: u64 = 0
  ) {
    super();
  }

  @primary
  get primary(): u64 { return this.id; }

  @secondary
  get byAuthor(): u64 { return this.author.N; }

  @secondary
  get byTimestamp(): u64 { return this.timestamp; }
}
```

---

## TableStore Operations

### Initialize TableStore

```typescript
import { Contract, TableStore } from 'proton-tsc';

@contract
class MyContract extends Contract {
  userTable: TableStore<User> = new TableStore<User>(this.receiver);
}
```

### Store (Insert New Row)

```typescript
@action("adduser")
addUser(account: Name): void {
  const user = new User(
    this.userTable.availablePrimaryKey,  // Auto-increment ID
    account,
    0,
    currentTimeSec()
  );
  this.userTable.store(user, this.receiver);  // Throws if exists
}
```

### Set (Upsert)

```typescript
@action("setuser")
setUser(id: u64, account: Name, balance: u64): void {
  const user = new User(id, account, balance, currentTimeSec());
  this.userTable.set(user, this.receiver);  // Insert or update
}
```

### Get (Read)

```typescript
@action("getuser")
getUser(id: u64): void {
  const user = this.userTable.get(id);
  if (!user) {
    check(false, "User not found");
    return;
  }
  print(`User: ${user.account}`);
}
```

### Update

```typescript
@action("updatebal")
updateBalance(id: u64, newBalance: u64): void {
  const user = this.userTable.requireGet(id, "User not found");
  user.balance = newBalance;
  this.userTable.update(user, this.receiver);  // Throws if not exists
}
```

### Delete

```typescript
@action("deluser")
deleteUser(id: u64): void {
  const user = this.userTable.requireGet(id, "User not found");
  this.userTable.remove(user);
}
```

### Check Existence

```typescript
if (this.userTable.exists(id)) {
  // Row exists
}
```

### Iteration

```typescript
// Get all rows
const users = this.userTable.getAll();

// Iterate with cursor
let cursor = this.userTable.first();
while (cursor) {
  print(`User: ${cursor.account}`);
  cursor = this.userTable.next(cursor);
}
```

---

## Actions

### Basic Action

```typescript
@action("transfer")
transfer(from: Name, to: Name, amount: u64, memo: string): void {
  requireAuth(from);  // Require signature from 'from' account

  check(amount > 0, "Amount must be positive");

  // ... transfer logic
}
```

### Action with Authorization

```typescript
@action("adminonly")
adminAction(admin: Name): void {
  requireAuth(admin);
  requireAuth(this.receiver);  // Also require contract's auth
}
```

### Notify Handler (for incoming transfers)

Notify handlers let your contract react to actions on other contracts (e.g., token transfers).

```typescript
@action("transfer", notify)
onTransfer(from: Name, to: Name, quantity: Asset, memo: string): void {
  // Only process transfers TO this contract (not from)
  if (to != this.receiver) return;

  // Only accept transfers from eosio.token
  if (this.firstReceiver != Name.fromString("eosio.token")) return;

  // Parse memo and process payment
  if (memo.startsWith("deposit:")) {
    // Handle deposit
  }
}
```

**Important Contract Properties:**
- `this.receiver` - The contract that contains this code (your contract)
- `this.firstReceiver` - The contract where the action originated (e.g., `eosio.token` for transfers)

**Security Note**: Always check `this.firstReceiver` in notify handlers to prevent spoofed notifications from malicious contracts pretending to be token contracts.

```typescript
// SECURE: Check the token contract
if (this.firstReceiver != Name.fromString("eosio.token")) return;

// INSECURE: Anyone could call your contract with fake transfer data
// @action("transfer", notify)  // Without firstReceiver check = vulnerable
```

---

## Data Types

### Primitive Types

| Type | Description | Range |
|------|-------------|-------|
| `u8` | Unsigned 8-bit | 0 to 255 |
| `u16` | Unsigned 16-bit | 0 to 65,535 |
| `u32` | Unsigned 32-bit | 0 to 4,294,967,295 |
| `u64` | Unsigned 64-bit | 0 to 18,446,744,073,709,551,615 |
| `i8`, `i16`, `i32`, `i64` | Signed integers | |
| `f32`, `f64` | Floating point | Avoid in financial calculations |
| `bool` | Boolean | true/false |
| `string` | UTF-8 string | Variable length |

### XPR Network Types

```typescript
import { Name, Asset, Symbol, ExtendedAsset } from 'proton-tsc';

// Name (account names)
const account = Name.fromString("alice");
const accountU64 = account.N;  // u64 representation

// Symbol (token symbols)
const xprSymbol = new Symbol("XPR", 4);  // 4 decimals

// Asset (amount + symbol)
const amount = new Asset(10000, xprSymbol);  // 1.0000 XPR
const amountStr = amount.toString();  // "1.0000 XPR"

// Parse from string
const parsed = Asset.fromString("100.0000 XPR");
```

### Price Storage (Fixed Point)

For financial data, use u64 with fixed decimal places:

```typescript
// Store $95,322.71 as u64 with 8 decimals
const price: u64 = 9532271000000;  // 95322.71 * 10^8

// Convert back
const priceFloat = <f64>price / 100000000.0;
```

---

## Authentication

### requireAuth

```typescript
import { requireAuth, hasAuth, isAccount } from 'proton-tsc';

@action("myaction")
myAction(user: Name): void {
  requireAuth(user);  // Throws if user didn't sign

  if (hasAuth(user)) {
    // User signed (non-throwing check)
  }

  if (isAccount(user)) {
    // Account exists on chain
  }
}
```

### Contract Self-Auth

```typescript
// Check if action is called by the contract itself
if (hasAuth(this.receiver)) {
  // Called internally
}
```

---

## Inline Actions

Call other contracts from within your contract:

```typescript
import { InlineAction, PermissionLevel, Name, Asset } from 'proton-tsc';

@action("paywinner")
payWinner(winner: Name, amount: Asset): void {
  // Transfer tokens using inline action
  const transfer = new InlineAction<TransferArgs>("eosio.token", "transfer");
  transfer.send(
    [new PermissionLevel(this.receiver, Name.fromString("active"))],
    new TransferArgs(this.receiver, winner, amount, "Prize payout")
  );
}

// Define the action arguments class
@packer
class TransferArgs {
  constructor(
    public from: Name = new Name(),
    public to: Name = new Name(),
    public quantity: Asset = new Asset(),
    public memo: string = ""
  ) {}
}
```

### Enable Inline Actions

Before using inline actions, enable them on the contract account:

```bash
proton contract:enableinline mycontract
```

---

## Time Functions

```typescript
import { currentTimeSec, currentTimeMs, currentTimePoint } from 'proton-tsc';

@action("checktime")
checkTime(): void {
  const nowSec = currentTimeSec();      // Unix timestamp in seconds
  const nowMs = currentTimeMs();        // Unix timestamp in milliseconds
  const timePoint = currentTimePoint(); // TimePoint object

  // Calculate expiry (1 hour from now)
  const expiresAt = nowSec + 3600;
}
```

---

## Assertions

```typescript
import { check } from 'proton-tsc';

@action("validate")
validate(amount: u64, recipient: Name): void {
  check(amount > 0, "Amount must be positive");
  check(amount <= 1000000, "Amount exceeds maximum");
  check(isAccount(recipient), "Recipient account does not exist");
}
```

---

## Build and Deploy

### Build

```bash
npm run build
# Output: assembly/target/mycontract.wasm and mycontract.abi
```

### Deploy

```bash
# Set network
proton chain:set proton

# Add key (do NOT store in files)
proton key:add

# Deploy WASM + ABI
proton contract:set mycontract ./assembly/target

# Initialize contract
proton action mycontract init '{"owner":"mycontract"}' mycontract
```

---

## AssemblyScript Gotchas

### No `any` or `undefined`

```typescript
// Wrong
function foo(a?) {}
function foo(a: any) {}

// Correct
function foo(a: u64 = 0): void {}
```

### No Union Types (except nullable)

```typescript
// Wrong
function foo(a: u32 | string): void {}

// Correct - use generics or separate functions
function foo<T>(a: T): void {}
```

### Objects Must Be Typed

```typescript
// Wrong
const a = {};
a.prop = "value";

// Correct - use Map or class
const a = new Map<string, string>();
a.set("prop", "value");
```

### String Comparison

```typescript
// Use == for string content comparison
const a = "abc";
const b = "abc";
check(a == b, "strings match");  // Correct

// === checks reference equality (usually not what you want)
```

### No try/catch

Throwing aborts the entire transaction. Use `check()` for validation.

### No Closures

```typescript
// Wrong - closures not supported
const items: u64[] = [];
const filtered = items.filter(x => x > 5);

// Correct - use for loops
const filtered: u64[] = [];
for (let i = 0; i < items.length; i++) {
  if (items[i] > 5) filtered.push(items[i]);
}
```

---

## Complete Example

```typescript
import {
  Contract, Table, TableStore, Name, Asset, Symbol,
  check, requireAuth, currentTimeSec, print
} from 'proton-tsc';

@table("balances")
export class Balance extends Table {
  constructor(
    public account: Name = new Name(),
    public amount: u64 = 0,
    public lastUpdate: u64 = 0
  ) { super(); }

  @primary
  get primary(): u64 { return this.account.N; }
}

@table("config", singleton)
export class Config extends Table {
  constructor(
    public owner: Name = new Name(),
    public paused: boolean = false
  ) { super(); }
}

@contract
export class MyToken extends Contract {
  balanceTable: TableStore<Balance> = new TableStore<Balance>(this.receiver);
  configSingleton: Singleton<Config> = new Singleton<Config>(this.receiver);

  @action("init")
  init(owner: Name): void {
    requireAuth(this.receiver);
    const config = new Config(owner, false);
    this.configSingleton.set(config, this.receiver);
  }

  @action("deposit")
  deposit(account: Name, amount: u64): void {
    requireAuth(account);

    const config = this.configSingleton.get();
    check(!config.paused, "Contract is paused");
    check(amount > 0, "Amount must be positive");

    let balance = this.balanceTable.get(account.N);
    if (!balance) {
      balance = new Balance(account, 0, 0);
    }

    balance.amount += amount;
    balance.lastUpdate = currentTimeSec();
    this.balanceTable.set(balance, this.receiver);
  }

  @action("withdraw")
  withdraw(account: Name, amount: u64): void {
    requireAuth(account);

    const balance = this.balanceTable.requireGet(
      account.N,
      "No balance found"
    );

    check(balance.amount >= amount, "Insufficient balance");

    balance.amount -= amount;
    balance.lastUpdate = currentTimeSec();

    if (balance.amount == 0) {
      this.balanceTable.remove(balance);
    } else {
      this.balanceTable.update(balance, this.receiver);
    }
  }
}
```

---

## Next Steps

- Read `safety-guidelines.md` before deploying (CRITICAL)
- See `examples.md` for production contract patterns
- Use `cli-reference.md` for deployment commands
