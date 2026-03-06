# RPC Queries and Table Reading

This guide covers reading blockchain data from XPR Network using RPC calls and the `@proton/js` library.

## RPC Endpoints

### Mainnet

| Endpoint | Provider |
|----------|----------|
| `https://proton.eosusa.io` | EOSUSA |
| `https://proton.cryptolions.io` | CryptoLions |

### Testnet

| Endpoint | Provider |
|----------|----------|
| `https://tn1.protonnz.com` | protonnz |

### Hyperion (History API)

| Network | Endpoint |
|---------|----------|
| Mainnet | `https://api-xprnetwork-main.saltant.io` |
| Testnet | `https://api-xprnetwork-test.saltant.io` |

Base path: `/v2/history/` or `/v2/state/`

### Light API

| Network | Endpoint |
|---------|----------|
| Mainnet | `https://lightapi.eosamsterdam.net/api` |

Fast, lightweight API for common queries like token balances.

### Block Explorers

| Explorer | URL |
|----------|-----|
| XPR Network Explorer | `https://explorer.xprnetwork.org` |

---

## Setup

### Using @proton/js

```bash
npm install @proton/js
```

```typescript
import { JsonRpc } from '@proton/js';

const rpc = new JsonRpc('https://proton.eosusa.io');
```

### Using fetch directly

```typescript
async function queryTable(code: string, table: string, scope?: string) {
  const response = await fetch('https://proton.eosusa.io/v1/chain/get_table_rows', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({
      code,
      scope: scope ?? code,
      table,
      json: true,
      limit: 100
    })
  });
  return response.json();
}
```

---

## get_table_rows

The primary method for reading table data.

### Basic Query

```typescript
const { rows } = await rpc.get_table_rows({
  code: 'eosio.proton',      // Contract account
  scope: 'eosio.proton',     // Table scope (usually same as code)
  table: 'usersinfo',        // Table name
  json: true,                // Return JSON (not binary)
  limit: 100                 // Max rows to return
});
```

### Query Parameters

| Parameter | Type | Description |
|-----------|------|-------------|
| `code` | string | Contract account name |
| `scope` | string | Table scope (often same as code) |
| `table` | string | Table name |
| `json` | boolean | Return JSON instead of binary (usually true) |
| `limit` | number | Max rows to return (default 10) |
| `lower_bound` | string/number | Start at this key |
| `upper_bound` | string/number | End at this key |
| `index_position` | string | Index to use: `primary`, `secondary`, `tertiary`, etc. |
| `key_type` | string | Key type: `i64`, `i128`, `name`, `float64`, etc. |
| `reverse` | boolean | Reverse order |

### Exact Match Query

```typescript
// Get specific user profile
const { rows } = await rpc.get_table_rows({
  code: 'eosio.proton',
  scope: 'eosio.proton',
  table: 'usersinfo',
  lower_bound: 'alice',
  upper_bound: 'alice',
  limit: 1
});

const userProfile = rows.length > 0 ? rows[0] : null;
```

### Range Query

```typescript
// Get challenges with ID 10-50
const { rows } = await rpc.get_table_rows({
  code: 'pricebattle',
  scope: 'pricebattle',
  table: 'challenges',
  lower_bound: 10,
  upper_bound: 50,
  limit: 100
});
```

### Secondary Index Query

```typescript
// Query by secondary index (e.g., by author)
const { rows } = await rpc.get_table_rows({
  code: 'protonwall',
  scope: 'protonwall',
  table: 'posts',
  index_position: 'secondary',  // or '2'
  key_type: 'name',
  lower_bound: 'alice',
  upper_bound: 'alice',
  limit: 100
});
```

### Pagination

```typescript
async function getAllRows(code: string, table: string) {
  const allRows: any[] = [];
  let more = true;
  let nextKey = '';

  while (more) {
    const { rows, more: hasMore, next_key } = await rpc.get_table_rows({
      code,
      scope: code,
      table,
      limit: 100,
      lower_bound: nextKey || undefined
    });

    allRows.push(...rows);
    more = hasMore;
    nextKey = next_key;
  }

  return allRows;
}
```

### Reverse Order

```typescript
// Get latest entries first
const { rows } = await rpc.get_table_rows({
  code: 'protonwall',
  scope: 'protonwall',
  table: 'posts',
  reverse: true,
  limit: 10
});
```

---

## Common Tables

### User Profile (eosio.proton)

```typescript
// Get user profile info
const { rows } = await rpc.get_table_rows({
  code: 'eosio.proton',
  scope: 'eosio.proton',
  table: 'usersinfo',
  lower_bound: 'alice',
  upper_bound: 'alice',
  limit: 1
});

// Response includes:
// - acc: account name
// - name: display name
// - avatar: avatar URL or base64
// - verified: boolean
// - verifiedon: timestamp
// - kyc: array of KYC providers
```

### Token Balances

```typescript
// Get XPR balance
const { rows } = await rpc.get_table_rows({
  code: 'eosio.token',
  scope: 'alice',          // User's account as scope!
  table: 'accounts',
  limit: 100
});

// Returns array of balances: [{ balance: "123.0000 XPR" }, ...]
```

### Oracle Prices

```typescript
// Get BTC/USD price (index 4)
const { rows } = await rpc.get_table_rows({
  code: 'oracles',
  scope: 'oracles',
  table: 'data',
  lower_bound: 4,
  upper_bound: 4,
  limit: 1
});

// Response:
// {
//   feed_index: 4,
//   aggregate: { d_double: "95322.71000000000640284" }
// }
const btcPrice = parseFloat(rows[0].aggregate.d_double);
```

### Oracle Feed Indexes

| Index | Pair |
|-------|------|
| 4 | BTC/USD |
| 5 | ETH/USD |
| 13 | XPR/USD |

### Singleton Tables

For singleton tables, there's only one row with no primary key:

```typescript
// Get contract config
const { rows } = await rpc.get_table_rows({
  code: 'pricebattle',
  scope: 'pricebattle',
  table: 'config',
  limit: 1
});

const config = rows[0];  // Single row
```

---

## RPC Service Class

```typescript
import { JsonRpc } from '@proton/js';

class ProtonRPC {
  private rpc: JsonRpc;

  constructor(endpoint: string = 'https://proton.eosusa.io') {
    this.rpc = new JsonRpc(endpoint);
  }

  // Generic table query
  async getTable<T>(
    code: string,
    table: string,
    options: Partial<{
      scope: string;
      limit: number;
      lowerBound: string | number;
      upperBound: string | number;
      indexPosition: string;
      keyType: string;
      reverse: boolean;
    }> = {}
  ): Promise<T[]> {
    const { rows } = await this.rpc.get_table_rows({
      code,
      scope: options.scope ?? code,
      table,
      json: true,
      limit: options.limit ?? 100,
      lower_bound: options.lowerBound,
      upper_bound: options.upperBound,
      index_position: options.indexPosition,
      key_type: options.keyType,
      reverse: options.reverse
    });
    return rows as T[];
  }

  // User profile
  async getUserInfo(account: string) {
    const rows = await this.getTable('eosio.proton', 'usersinfo', {
      lowerBound: account,
      upperBound: account,
      limit: 1
    });
    return rows[0] ?? null;
  }

  // Token balance
  async getBalance(account: string, symbol: string = 'XPR'): Promise<string> {
    const rows = await this.getTable('eosio.token', 'accounts', {
      scope: account
    });
    const balance = rows.find((r: any) => r.balance.includes(symbol));
    return balance?.balance ?? `0.0000 ${symbol}`;
  }

  // Oracle price
  async getOraclePrice(feedIndex: number): Promise<number> {
    const rows = await this.getTable('oracles', 'data', {
      lowerBound: feedIndex,
      upperBound: feedIndex,
      limit: 1
    });
    return parseFloat(rows[0]?.aggregate?.d_double ?? '0');
  }

  // Open challenges
  async getOpenChallenges() {
    return this.getTable('pricebattle', 'challenges', {
      indexPosition: 'secondary',  // status index
      keyType: 'i64',
      lowerBound: 0,  // OPEN status
      upperBound: 0,
      limit: 100
    });
  }
}

export const protonRPC = new ProtonRPC();
```

---

## Hyperion History API

Hyperion provides full history and state APIs. Base URL: `https://proton.eosusa.io`

### History Endpoints

| Endpoint | Description |
|----------|-------------|
| `/v2/history/get_actions` | Query action history |
| `/v2/history/get_transaction` | Get transaction by ID |
| `/v2/history/get_deltas` | Table delta history |
| `/v2/history/get_abi_snapshot` | Historical ABI |
| `/v2/history/get_created_accounts` | Accounts created by account |
| `/v2/history/get_creator` | Get account creator |
| `/v2/history/get_transfers` | Token transfer history |

### State Endpoints

| Endpoint | Description |
|----------|-------------|
| `/v2/state/get_account` | Account info with resources |
| `/v2/state/get_key_accounts` | Accounts by public key |
| `/v2/state/get_tokens` | All token balances for account |
| `/v2/state/get_voters` | Voter information |
| `/v2/state/get_proposals` | Multisig proposals |

### Get Account Actions

```typescript
interface HyperionAction {
  '@timestamp': string;
  trx_id: string;
  act: {
    account: string;
    name: string;
    authorization: Array<{ actor: string; permission: string }>;
    data: Record<string, any>;
  };
  block_num: number;
  producer: string;
}

async function getAccountActions(
  account: string,
  options: {
    limit?: number;
    skip?: number;
    filter?: string;
    sort?: 'asc' | 'desc';
    after?: string;
    before?: string;
  } = {}
): Promise<{ actions: HyperionAction[]; total: number }> {
  const url = new URL('https://proton.eosusa.io/v2/history/get_actions');
  url.searchParams.set('account', account);
  url.searchParams.set('limit', String(options.limit ?? 100));

  if (options.skip) url.searchParams.set('skip', String(options.skip));
  if (options.filter) url.searchParams.set('filter', options.filter);
  if (options.sort) url.searchParams.set('sort', options.sort);
  if (options.after) url.searchParams.set('after', options.after);
  if (options.before) url.searchParams.set('before', options.before);

  const response = await fetch(url);
  return response.json();
}

// Examples:
// Get all actions
await getAccountActions('alice');

// Get only transfer actions
await getAccountActions('alice', { filter: 'eosio.token:transfer' });

// Get actions from last 24 hours
await getAccountActions('alice', {
  after: new Date(Date.now() - 86400000).toISOString()
});

// Paginate through all actions
await getAccountActions('alice', { skip: 100, limit: 100 });
```

### Filter by Contract and Action

```typescript
// Filter format: "contract:action" or "contract:*" for all actions
const filters = {
  allTransfers: 'eosio.token:transfer',
  allFromContract: 'pricebattle:*',
  specificAction: 'atomicassets:mintasset',
  multipleFilters: 'eosio.token:transfer,atomicassets:transfer'  // comma-separated
};

// Get only battle-related actions
const { actions } = await getAccountActions('alice', {
  filter: 'pricebattle:*',
  limit: 50
});
```

### Get Token Transfers

```typescript
interface Transfer {
  from: string;
  to: string;
  quantity: string;
  memo: string;
  block_num: number;
  '@timestamp': string;
  trx_id: string;
}

async function getTransfers(
  account: string,
  symbol?: string
): Promise<{ transfers: Transfer[] }> {
  const url = new URL('https://proton.eosusa.io/v2/history/get_transfers');
  url.searchParams.set('account', account);
  if (symbol) url.searchParams.set('symbol', symbol);
  url.searchParams.set('limit', '100');

  const response = await fetch(url);
  return response.json();
}

// Get XPR transfers only
const { transfers } = await getTransfers('alice', 'XPR');
```

### Get Transaction by ID

```typescript
interface HyperionTransaction {
  trx_id: string;
  lib: number;
  actions: HyperionAction[];
  block_num: number;
  block_time: string;
  irreversible: boolean;
}

async function getTransaction(txId: string): Promise<HyperionTransaction> {
  const response = await fetch(
    `https://proton.eosusa.io/v2/history/get_transaction?id=${txId}`
  );
  return response.json();
}
```

### Get Account State

```typescript
interface AccountState {
  account_name: string;
  total_resources: {
    net_weight: string;
    cpu_weight: string;
    ram_bytes: number;
  };
  tokens: Array<{
    symbol: string;
    amount: number;
    contract: string;
  }>;
}

async function getAccountState(account: string): Promise<AccountState> {
  const response = await fetch(
    `https://proton.eosusa.io/v2/state/get_account?account=${account}`
  );
  return response.json();
}
```

### Get All Token Balances

```typescript
interface TokenBalance {
  symbol: string;
  amount: string;
  contract: string;
  precision: number;
}

async function getAllBalances(account: string): Promise<TokenBalance[]> {
  const response = await fetch(
    `https://proton.eosusa.io/v2/state/get_tokens?account=${account}`
  );
  const data = await response.json();
  return data.tokens;
}

// Returns all tokens the account holds
const balances = await getAllBalances('alice');
// [{ symbol: 'XPR', amount: '1000.0000', contract: 'eosio.token', precision: 4 }, ...]
```

### Get Accounts by Public Key

```typescript
async function getKeyAccounts(publicKey: string): Promise<string[]> {
  const response = await fetch(
    `https://proton.eosusa.io/v2/state/get_key_accounts?public_key=${publicKey}`
  );
  const data = await response.json();
  return data.account_names;
}

// Find all accounts controlled by a key
const accounts = await getKeyAccounts('PUB_K1_6MRy...');
```

### Get Table Deltas (Change History)

```typescript
async function getTableDeltas(
  code: string,
  table: string,
  scope?: string
): Promise<any[]> {
  const url = new URL('https://proton.eosusa.io/v2/history/get_deltas');
  url.searchParams.set('code', code);
  url.searchParams.set('table', table);
  if (scope) url.searchParams.set('scope', scope);
  url.searchParams.set('limit', '100');

  const response = await fetch(url);
  const data = await response.json();
  return data.deltas;
}

// Track changes to a specific table
const deltas = await getTableDeltas('pricebattle', 'challenges');
```

---

## Light API

Light API provides fast, lightweight queries optimized for common operations.

Base URL: `https://lightapi.eosamsterdam.net`

### Endpoints

| Endpoint | Description |
|----------|-------------|
| `/api/account/proton/{account}` | Account info |
| `/api/balances/proton/{account}` | All token balances |
| `/api/tokenbalance/proton/{account}/{contract}/{symbol}` | Specific token balance |
| `/api/key/proton/{public_key}` | Accounts by key |
| `/api/topholders/proton/{contract}/{symbol}/{limit}` | Top token holders |
| `/api/accinfo/proton/{account}` | Detailed account info |
| `/api/usercount/proton` | Total registered users |

### Get Account Balances

```typescript
interface LightAPIBalance {
  contract: string;
  currency: string;
  amount: string;
  decimals: number;
}

async function getLightAPIBalances(account: string): Promise<LightAPIBalance[]> {
  const response = await fetch(
    `https://lightapi.eosamsterdam.net/api/balances/proton/${account}`
  );
  const data = await response.json();
  return data.balances;
}

// Fast way to get all balances
const balances = await getLightAPIBalances('alice');
```

### Get Specific Token Balance

```typescript
async function getTokenBalance(
  account: string,
  contract: string,
  symbol: string
): Promise<string> {
  const response = await fetch(
    `https://lightapi.eosamsterdam.net/api/tokenbalance/proton/${account}/${contract}/${symbol}`
  );
  const data = await response.json();
  return data.balance ?? '0';
}

// Get XPR balance
const xprBalance = await getTokenBalance('alice', 'eosio.token', 'XPR');

// Get XUSDC balance
const usdcBalance = await getTokenBalance('alice', 'xtokens', 'XUSDC');
```

### Get Accounts by Public Key

```typescript
async function getAccountsByKey(publicKey: string): Promise<string[]> {
  const response = await fetch(
    `https://lightapi.eosamsterdam.net/api/key/proton/${publicKey}`
  );
  const data = await response.json();
  return data.accounts?.map((a: any) => a.account_name) ?? [];
}
```

### Get Top Token Holders

```typescript
interface TokenHolder {
  account: string;
  amount: string;
}

async function getTopHolders(
  contract: string,
  symbol: string,
  limit: number = 100
): Promise<TokenHolder[]> {
  const response = await fetch(
    `https://lightapi.eosamsterdam.net/api/topholders/proton/${contract}/${symbol}/${limit}`
  );
  const data = await response.json();
  return data.accounts;
}

// Get top 100 XPR holders
const topHolders = await getTopHolders('eosio.token', 'XPR', 100);
```

### Get Total User Count

```typescript
async function getTotalUsers(): Promise<number> {
  const response = await fetch(
    'https://lightapi.eosamsterdam.net/api/usercount/proton'
  );
  const data = await response.json();
  return data.count;
}
```

---

## Block Explorer APIs

### XPR Network Explorer

The official XPR Network Explorer provides a web interface for viewing accounts, transactions, and contracts.

```typescript
// Link to transaction
const txLink = `https://explorer.xprnetwork.org/transaction/${txId}`;

// Link to account
const accountLink = `https://explorer.xprnetwork.org/account/${account}`;

// Link to contract
const contractLink = `https://explorer.xprnetwork.org/account/${contract}?tab=contract`;
```

---

## Combined Query Service

```typescript
import { JsonRpc } from '@proton/js';

class XPRQueryService {
  private rpc: JsonRpc;
  private hyperionBase = 'https://proton.eosusa.io';
  private lightApiBase = 'https://lightapi.eosamsterdam.net';

  constructor(endpoint: string = 'https://proton.eosusa.io') {
    this.rpc = new JsonRpc(endpoint);
  }

  // === Table Queries (via RPC) ===

  async getTableRows<T>(
    code: string,
    table: string,
    options: {
      scope?: string;
      limit?: number;
      lowerBound?: string | number;
      upperBound?: string | number;
      indexPosition?: string;
      keyType?: string;
      reverse?: boolean;
    } = {}
  ): Promise<T[]> {
    const { rows } = await this.rpc.get_table_rows({
      code,
      scope: options.scope ?? code,
      table,
      json: true,
      limit: options.limit ?? 100,
      lower_bound: options.lowerBound,
      upper_bound: options.upperBound,
      index_position: options.indexPosition,
      key_type: options.keyType,
      reverse: options.reverse
    });
    return rows as T[];
  }

  // === Hyperion History ===

  async getActions(account: string, filter?: string, limit = 100) {
    const url = new URL(`${this.hyperionBase}/v2/history/get_actions`);
    url.searchParams.set('account', account);
    url.searchParams.set('limit', String(limit));
    if (filter) url.searchParams.set('filter', filter);

    const response = await fetch(url);
    return response.json();
  }

  async getTransaction(txId: string) {
    const response = await fetch(
      `${this.hyperionBase}/v2/history/get_transaction?id=${txId}`
    );
    return response.json();
  }

  async getTransfers(account: string, symbol?: string) {
    const url = new URL(`${this.hyperionBase}/v2/history/get_transfers`);
    url.searchParams.set('account', account);
    if (symbol) url.searchParams.set('symbol', symbol);

    const response = await fetch(url);
    return response.json();
  }

  // === Light API (fast queries) ===

  async getAllBalances(account: string) {
    const response = await fetch(
      `${this.lightApiBase}/api/balances/proton/${account}`
    );
    return response.json();
  }

  async getTokenBalance(account: string, contract: string, symbol: string) {
    const response = await fetch(
      `${this.lightApiBase}/api/tokenbalance/proton/${account}/${contract}/${symbol}`
    );
    return response.json();
  }

  // === Common Queries ===

  async getUserProfile(account: string) {
    const rows = await this.getTableRows('eosio.proton', 'usersinfo', {
      lowerBound: account,
      upperBound: account,
      limit: 1
    });
    return rows[0] ?? null;
  }

  async getOraclePrice(feedIndex: number): Promise<number> {
    const rows = await this.getTableRows('oracles', 'data', {
      lowerBound: feedIndex,
      upperBound: feedIndex,
      limit: 1
    });
    return parseFloat(rows[0]?.aggregate?.d_double ?? '0');
  }

}

export const xprQuery = new XPRQueryService();
```

---

## cURL Examples

```bash
# Basic table query - get user profiles
curl -s -X POST https://proton.eosusa.io/v1/chain/get_table_rows \
  -H "Content-Type: application/json" \
  -d '{
    "code": "eosio.proton",
    "scope": "eosio.proton",
    "table": "usersinfo",
    "json": true,
    "limit": 10
  }'

# Specific account
curl -s -X POST https://proton.eosusa.io/v1/chain/get_table_rows \
  -H "Content-Type: application/json" \
  -d '{
    "code": "eosio.proton",
    "scope": "eosio.proton",
    "table": "usersinfo",
    "lower_bound": "alice",
    "upper_bound": "alice",
    "limit": 1
  }'

# Oracle price
curl -s -X POST https://proton.eosusa.io/v1/chain/get_table_rows \
  -H "Content-Type: application/json" \
  -d '{
    "code": "oracles",
    "scope": "oracles",
    "table": "data",
    "lower_bound": 4,
    "upper_bound": 4,
    "limit": 1
  }'

# Account actions (Hyperion)
curl -s "https://proton.eosusa.io/v2/history/get_actions?account=alice&limit=10"
```

---

## Error Handling

```typescript
async function safeQuery<T>(queryFn: () => Promise<T>, defaultValue: T): Promise<T> {
  try {
    return await queryFn();
  } catch (error: any) {
    if (error.message?.includes('table not found')) {
      // Table doesn't exist or has no data
      return defaultValue;
    }
    if (error.message?.includes('ECONNREFUSED')) {
      // Endpoint down - try backup
      console.error('Primary endpoint down');
    }
    throw error;
  }
}

// Usage
const rating = await safeQuery(
  () => protonRPC.getAccountRating('alice'),
  3  // Default rating
);
```

---

## Performance Tips

1. **Use specific bounds** - Don't query entire tables when you need specific rows
2. **Paginate large results** - Use `limit` and `next_key` for large tables
3. **Cache when possible** - Oracle prices, user profiles don't change frequently
4. **Use secondary indexes** - Query by indexed fields when primary key isn't suitable
5. **Multiple endpoints** - Implement fallback endpoints for reliability

```typescript
const ENDPOINTS = [
  'https://proton.eosusa.io',
  'https://proton.greymass.com'
];

async function queryWithFallback(query: (rpc: JsonRpc) => Promise<any>) {
  for (const endpoint of ENDPOINTS) {
    try {
      const rpc = new JsonRpc(endpoint);
      return await query(rpc);
    } catch (error) {
      console.error(`Endpoint ${endpoint} failed:`, error);
      continue;
    }
  }
  throw new Error('All endpoints failed');
}
```
