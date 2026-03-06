# Backend Development Patterns

This guide covers server-side integration with XPR Network - signing transactions programmatically, automated operations, and production patterns.

## Overview

Backend integration differs from frontend (wallet) integration:

| Aspect | Frontend (web-sdk) | Backend |
|--------|-------------------|---------|
| Key storage | User's wallet | Server environment |
| Signing | Wallet prompts user | Automatic with private key |
| Use case | User-initiated actions | Automated/scheduled tasks |
| Security | Wallet handles keys | You manage key security |

---

## Setup

### Dependencies

```bash
npm install @proton/js eosjs
```

### Basic Configuration

```typescript
import { JsonRpc, Api } from '@proton/js';
import { JsSignatureProvider } from 'eosjs/dist/eosjs-jssig';

// NEVER hardcode keys - use environment variables
const PRIVATE_KEY = process.env.XPR_PRIVATE_KEY;
const RPC_ENDPOINT = process.env.XPR_RPC_ENDPOINT || 'https://proton.eosusa.io';

const rpc = new JsonRpc(RPC_ENDPOINT);
const signatureProvider = new JsSignatureProvider([PRIVATE_KEY]);

const api = new Api({
  rpc,
  signatureProvider,
  textDecoder: new TextDecoder(),
  textEncoder: new TextEncoder()
});
```

---

## Transaction Signing

### Basic Transaction

```typescript
async function sendTransaction(actions: any[]) {
  try {
    const result = await api.transact(
      { actions },
      {
        blocksBehind: 3,
        expireSeconds: 30
      }
    );
    return { success: true, transaction_id: result.transaction_id };
  } catch (error: any) {
    return { success: false, error: error.message };
  }
}
```

### Token Transfer

```typescript
async function transferTokens(
  from: string,
  to: string,
  quantity: string,
  memo: string = ''
) {
  const actions = [{
    account: 'eosio.token',
    name: 'transfer',
    authorization: [{ actor: from, permission: 'active' }],
    data: { from, to, quantity, memo }
  }];

  return sendTransaction(actions);
}

// Usage
await transferTokens('myaccount', 'recipient', '10.0000 XPR', 'Payment');
```

### Multiple Actions in One Transaction

```typescript
async function batchTransfer(
  from: string,
  transfers: Array<{ to: string; quantity: string; memo: string }>
) {
  const actions = transfers.map(t => ({
    account: 'eosio.token',
    name: 'transfer',
    authorization: [{ actor: from, permission: 'active' }],
    data: {
      from,
      to: t.to,
      quantity: t.quantity,
      memo: t.memo
    }
  }));

  return sendTransaction(actions);
}
```

---

## Service Class Pattern

```typescript
import { JsonRpc, Api } from '@proton/js';
import { JsSignatureProvider } from 'eosjs/dist/eosjs-jssig';

interface TransactionResult {
  success: boolean;
  transaction_id?: string;
  error?: string;
}

class XPRBackendService {
  private rpc: JsonRpc;
  private api: Api;
  private account: string;

  constructor(privateKey: string, account: string, endpoint?: string) {
    this.account = account;
    this.rpc = new JsonRpc(endpoint || 'https://proton.eosusa.io');

    const signatureProvider = new JsSignatureProvider([privateKey]);
    this.api = new Api({
      rpc: this.rpc,
      signatureProvider,
      textDecoder: new TextDecoder(),
      textEncoder: new TextEncoder()
    });
  }

  // Execute transaction with retry logic
  async transact(actions: any[], retries: number = 3): Promise<TransactionResult> {
    for (let attempt = 1; attempt <= retries; attempt++) {
      try {
        const result = await this.api.transact(
          { actions },
          { blocksBehind: 3, expireSeconds: 30 }
        );
        return { success: true, transaction_id: result.transaction_id };
      } catch (error: any) {
        const isRetryable = this.isRetryableError(error);

        if (attempt === retries || !isRetryable) {
          return { success: false, error: error.message };
        }

        // Wait before retry (exponential backoff)
        await this.sleep(Math.pow(2, attempt) * 1000);
      }
    }
    return { success: false, error: 'Max retries exceeded' };
  }

  private isRetryableError(error: any): boolean {
    const message = error.message || '';
    // Retry on network errors, not on validation errors
    return message.includes('ECONNREFUSED') ||
           message.includes('timeout') ||
           message.includes('Too Many Requests');
  }

  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  // Query table data
  async getTable<T>(
    code: string,
    table: string,
    options: {
      scope?: string;
      lowerBound?: string | number;
      upperBound?: string | number;
      limit?: number;
    } = {}
  ): Promise<T[]> {
    const { rows } = await this.rpc.get_table_rows({
      code,
      scope: options.scope || code,
      table,
      lower_bound: options.lowerBound,
      upper_bound: options.upperBound,
      limit: options.limit || 100,
      json: true
    });
    return rows as T[];
  }

  // Token operations
  async transfer(to: string, quantity: string, memo: string = ''): Promise<TransactionResult> {
    return this.transact([{
      account: 'eosio.token',
      name: 'transfer',
      authorization: [{ actor: this.account, permission: 'active' }],
      data: {
        from: this.account,
        to,
        quantity,
        memo
      }
    }]);
  }

  async getBalance(account: string, symbol: string = 'XPR'): Promise<string> {
    const rows = await this.getTable<{ balance: string }>('eosio.token', 'accounts', {
      scope: account
    });
    const balance = rows.find(r => r.balance.includes(symbol));
    return balance?.balance || `0.0000 ${symbol}`;
  }

  // Custom contract action
  async callContract(
    contract: string,
    action: string,
    data: Record<string, any>
  ): Promise<TransactionResult> {
    return this.transact([{
      account: contract,
      name: action,
      authorization: [{ actor: this.account, permission: 'active' }],
      data
    }]);
  }
}

// Usage
const xpr = new XPRBackendService(
  process.env.XPR_PRIVATE_KEY!,
  'myaccount'
);

await xpr.transfer('recipient', '10.0000 XPR', 'Payment');
await xpr.callContract('mycontract', 'myaction', { param1: 'value' });
```

---

## Token Operations

### Deploy a Token

```typescript
async function deployToken(
  issuer: string,
  maxSupply: string  // e.g., "1000000.0000 MYTOKEN"
) {
  // Create token
  await sendTransaction([{
    account: 'eosio.token',
    name: 'create',
    authorization: [{ actor: issuer, permission: 'active' }],
    data: {
      issuer,
      maximum_supply: maxSupply
    }
  }]);
}
```

### Issue Tokens

```typescript
async function issueTokens(
  issuer: string,
  to: string,
  quantity: string,
  memo: string = 'Token issuance'
) {
  await sendTransaction([{
    account: 'eosio.token',
    name: 'issue',
    authorization: [{ actor: issuer, permission: 'active' }],
    data: {
      to,
      quantity,
      memo
    }
  }]);
}
```

### Check Balance

```typescript
async function getTokenBalance(account: string, tokenContract: string = 'eosio.token') {
  const { rows } = await rpc.get_table_rows({
    code: tokenContract,
    scope: account,
    table: 'accounts',
    json: true
  });
  return rows;
}
```

---

## NFT Operations (Backend)

### Mint NFT from Backend

```typescript
async function mintNFT(
  minter: string,
  collection: string,
  schema: string,
  templateId: number,
  recipient: string
) {
  return sendTransaction([{
    account: 'atomicassets',
    name: 'mintasset',
    authorization: [{ actor: minter, permission: 'active' }],
    data: {
      authorized_minter: minter,
      collection_name: collection,
      schema_name: schema,
      template_id: templateId,
      new_asset_owner: recipient,
      immutable_data: [],
      mutable_data: [],
      tokens_to_back: []
    }
  }]);
}
```

### Batch Mint with Rate Limiting

```typescript
async function batchMintWithLimit(
  minter: string,
  collection: string,
  schema: string,
  templateId: number,
  recipients: string[],
  batchSize: number = 50
) {
  const results: TransactionResult[] = [];

  for (let i = 0; i < recipients.length; i += batchSize) {
    const batch = recipients.slice(i, i + batchSize);

    const actions = batch.map(recipient => ({
      account: 'atomicassets',
      name: 'mintasset',
      authorization: [{ actor: minter, permission: 'active' }],
      data: {
        authorized_minter: minter,
        collection_name: collection,
        schema_name: schema,
        template_id: templateId,
        new_asset_owner: recipient,
        immutable_data: [],
        mutable_data: [],
        tokens_to_back: []
      }
    }));

    const result = await sendTransaction(actions);
    results.push(result);

    // Rate limit: wait between batches
    if (i + batchSize < recipients.length) {
      await new Promise(r => setTimeout(r, 1000));
    }
  }

  return results;
}
```

---

## Scheduled/Automated Tasks

### Resolve Expired Game Challenges

```typescript
import cron from 'node-cron';

async function resolveExpiredChallenges() {
  // Get active challenges that have ended
  const { rows } = await rpc.get_table_rows({
    code: 'pricebattle',
    scope: 'pricebattle',
    table: 'challenges',
    index_position: 'secondary',
    key_type: 'i64',
    lower_bound: 1,  // ACTIVE status
    upper_bound: 1,
    limit: 100
  });

  const now = Math.floor(Date.now() / 1000);

  for (const challenge of rows) {
    const endTime = challenge.started_at + challenge.duration;

    if (now >= endTime) {
      // Get current oracle price
      const price = await getOraclePrice(challenge.oracle_index);

      // Resolve the challenge
      await sendTransaction([{
        account: 'pricebattle',
        name: 'resolve',
        authorization: [{ actor: 'resolver', permission: 'active' }],
        data: {
          challenge_id: challenge.id,
          resolver: 'resolver',
          end_price: price
        }
      }]);

      console.log(`Resolved challenge ${challenge.id}`);
    }
  }
}

// Run every minute
cron.schedule('* * * * *', resolveExpiredChallenges);
```

### Cleanup Expired Entries

```typescript
async function cleanupExpired() {
  await sendTransaction([{
    account: 'mycontract',
    name: 'cleanup',
    authorization: [{ actor: 'myaccount', permission: 'active' }],
    data: { limit: 100 }
  }]);
}

// Run every hour
cron.schedule('0 * * * *', cleanupExpired);
```

---

## Security Best Practices

### Key Management

```typescript
// NEVER do this:
const PRIVATE_KEY = 'PVT_K1_xxxxx';  // ❌ Hardcoded

// DO this:
const PRIVATE_KEY = process.env.XPR_PRIVATE_KEY;  // ✅ Environment variable

// Or use a secrets manager:
import { SecretsManager } from '@aws-sdk/client-secrets-manager';

async function getPrivateKey(): Promise<string> {
  const client = new SecretsManager({ region: 'us-east-1' });
  const response = await client.getSecretValue({ SecretId: 'xpr/private-key' });
  return response.SecretString!;
}
```

### Use Dedicated Accounts

Create separate accounts for different purposes:

| Account | Purpose | Permissions |
|---------|---------|-------------|
| `myapp.ops` | Automated operations | Limited to specific actions |
| `myapp.mint` | NFT minting only | Only atomicassets::mintasset |
| `myapp.pay` | Payments only | Only eosio.token::transfer |

### Permission Linking

Link custom permissions to specific actions:

```bash
# Create custom permission
proton action eosio updateauth '{
  "account": "myapp",
  "permission": "minter",
  "parent": "active",
  "auth": {
    "threshold": 1,
    "keys": [{"key": "PUB_K1_xxx", "weight": 1}],
    "accounts": [],
    "waits": []
  }
}' myapp@owner

# Link permission to specific action
proton action eosio linkauth '{
  "account": "myapp",
  "code": "atomicassets",
  "type": "mintasset",
  "requirement": "minter"
}' myapp@owner
```

Now you can sign mintasset with the limited `minter` key.

### Rate Limiting

```typescript
class RateLimiter {
  private timestamps: number[] = [];
  private maxRequests: number;
  private windowMs: number;

  constructor(maxRequests: number, windowMs: number) {
    this.maxRequests = maxRequests;
    this.windowMs = windowMs;
  }

  async acquire(): Promise<void> {
    const now = Date.now();
    this.timestamps = this.timestamps.filter(t => now - t < this.windowMs);

    if (this.timestamps.length >= this.maxRequests) {
      const waitTime = this.timestamps[0] + this.windowMs - now;
      await new Promise(r => setTimeout(r, waitTime));
      return this.acquire();
    }

    this.timestamps.push(now);
  }
}

// Usage: Max 10 transactions per second
const limiter = new RateLimiter(10, 1000);

async function rateLimitedTransfer(to: string, amount: string) {
  await limiter.acquire();
  return transfer(to, amount);
}
```

---

## Error Handling

### Common Errors

| Error | Cause | Solution |
|-------|-------|----------|
| `missing authority` | Wrong key or permission | Check authorization matches key |
| `expired transaction` | Transaction took too long | Increase `expireSeconds` |
| `duplicate transaction` | Same tx submitted twice | Add unique data or wait |
| `cpu usage exceeded` | Not enough CPU staked | Stake more CPU or wait |
| `assertion failure` | Contract validation failed | Check action parameters |

### Robust Error Handling

```typescript
async function safeTransact(actions: any[]): Promise<TransactionResult> {
  try {
    const result = await api.transact(
      { actions },
      { blocksBehind: 3, expireSeconds: 30 }
    );
    return { success: true, transaction_id: result.transaction_id };

  } catch (error: any) {
    const message = error.message || String(error);

    // Parse assertion failures
    if (message.includes('assertion failure')) {
      const match = message.match(/assertion failure with message: (.+)/);
      return {
        success: false,
        error: match ? match[1] : 'Contract assertion failed'
      };
    }

    // Resource errors
    if (message.includes('cpu usage exceeded')) {
      return { success: false, error: 'Insufficient CPU resources' };
    }

    if (message.includes('ram usage exceeded')) {
      return { success: false, error: 'Insufficient RAM' };
    }

    // Auth errors
    if (message.includes('missing authority')) {
      return { success: false, error: 'Authorization failed - check key permissions' };
    }

    return { success: false, error: message };
  }
}
```

---

## Monitoring and Logging

### Transaction Logging

```typescript
interface TransactionLog {
  timestamp: Date;
  action: string;
  data: any;
  result: TransactionResult;
}

class LoggedXPRService extends XPRBackendService {
  private logs: TransactionLog[] = [];

  async transact(actions: any[]): Promise<TransactionResult> {
    const result = await super.transact(actions);

    for (const action of actions) {
      this.logs.push({
        timestamp: new Date(),
        action: `${action.account}::${action.name}`,
        data: action.data,
        result
      });
    }

    // Also log to external service
    await this.sendToLoggingService(actions, result);

    return result;
  }

  private async sendToLoggingService(actions: any[], result: TransactionResult) {
    // Send to your logging service (Datadog, CloudWatch, etc.)
    console.log(JSON.stringify({
      service: 'xpr-backend',
      actions: actions.map(a => `${a.account}::${a.name}`),
      success: result.success,
      tx_id: result.transaction_id,
      error: result.error
    }));
  }
}
```

### Health Check Endpoint

```typescript
import express from 'express';

const app = express();

app.get('/health', async (req, res) => {
  try {
    // Check RPC connection
    const info = await rpc.get_info();

    // Check account balance
    const balance = await xpr.getBalance(xpr.account);

    res.json({
      status: 'healthy',
      chain: {
        head_block: info.head_block_num,
        chain_id: info.chain_id
      },
      account: {
        name: xpr.account,
        balance
      }
    });
  } catch (error: any) {
    res.status(500).json({
      status: 'unhealthy',
      error: error.message
    });
  }
});
```

---

## Environment Configuration

### .env Template

```bash
# XPR Network Configuration
XPR_PRIVATE_KEY=PVT_K1_xxxxx
XPR_ACCOUNT=myaccount
XPR_RPC_ENDPOINT=https://proton.eosusa.io
XPR_CHAIN_ID=384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0

# For testnet
# XPR_RPC_ENDPOINT=https://tn1.protonnz.com
# XPR_CHAIN_ID=71ee83bcf52142d61019d95f9cc5427ba6a0d7ff8accd9e2088ae2abeaf3d3dd

# Optional: AtomicAssets
ATOMIC_API=https://proton.api.atomicassets.io

# Optional: Rate limiting
MAX_TPS=10
```

### Config Loader

```typescript
interface Config {
  privateKey: string;
  account: string;
  rpcEndpoint: string;
  chainId: string;
  atomicApi: string;
  maxTps: number;
}

function loadConfig(): Config {
  const required = ['XPR_PRIVATE_KEY', 'XPR_ACCOUNT'];

  for (const key of required) {
    if (!process.env[key]) {
      throw new Error(`Missing required environment variable: ${key}`);
    }
  }

  return {
    privateKey: process.env.XPR_PRIVATE_KEY!,
    account: process.env.XPR_ACCOUNT!,
    rpcEndpoint: process.env.XPR_RPC_ENDPOINT || 'https://proton.eosusa.io',
    chainId: process.env.XPR_CHAIN_ID || '384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0',
    atomicApi: process.env.ATOMIC_API || 'https://proton.api.atomicassets.io',
    maxTps: parseInt(process.env.MAX_TPS || '10')
  };
}
```

---

## Testing

### Test with Testnet

```typescript
// Use testnet for development
const TESTNET_CONFIG = {
  endpoint: 'https://tn1.protonnz.com',
  chainId: '71ee83bcf52142d61019d95f9cc5427ba6a0d7ff8accd9e2088ae2abeaf3d3dd'
};

// Get testnet tokens
// proton faucet:claim XPR myaccount
```

### Mock Transactions for Unit Tests

```typescript
import { jest } from '@jest/globals';

const mockApi = {
  transact: jest.fn().mockResolvedValue({
    transaction_id: 'mock_tx_id_123'
  })
};

// In tests
test('transfer succeeds', async () => {
  const result = await service.transfer('recipient', '10.0000 XPR');
  expect(result.success).toBe(true);
  expect(mockApi.transact).toHaveBeenCalled();
});
```
