# Troubleshooting Guide

Common issues and solutions for XPR Network development.

## Transaction Errors

### "missing authority of X"

**Cause**: Transaction not signed by required account.

**Solutions**:
```typescript
// Check authorization matches signer
{
  authorization: [{ actor: 'alice', permission: 'active' }],  // Must be alice signing
  // ...
}

// Verify session has correct account
console.log('Signing as:', session.auth.actor);
```

### "assertion failure with message: ..."

**Cause**: Contract `check()` condition failed.

**Solutions**:
- Read the error message - it's from your contract
- Check the condition in your contract code
- Verify input parameters match expected format

```typescript
// Contract code
check(amount > 0, "Amount must be positive");

// Error: "assertion failure with message: Amount must be positive"
// Solution: Ensure amount > 0
```

### "expired transaction"

**Cause**: Transaction took too long to broadcast.

**Solutions**:
```typescript
// Increase expire time
await session.transact(
  { actions },
  { broadcast: true, expireSeconds: 120 }  // Increase from 30
);
```

### "duplicate transaction"

**Cause**: Same transaction submitted twice within expire window.

**Solutions**:
- Wait for previous transaction to complete
- Add unique data (timestamp, nonce) to transaction

```typescript
data: {
  // Add unique element
  nonce: Date.now()
}
```

### "cpu usage exceeded"

**Cause**: Account doesn't have enough CPU staked.

**Solutions**:
```bash
# Check account resources
proton account myaccount

# Stake more CPU (requires XPR)
proton action eosio delegatebw '{
  "from": "myaccount",
  "receiver": "myaccount",
  "stake_net_quantity": "1.0000 XPR",
  "stake_cpu_quantity": "10.0000 XPR",
  "transfer": false
}' myaccount
```

### "ram usage exceeded"

**Cause**: Not enough RAM to store data.

**Solutions**:
```bash
# Check RAM usage
proton account myaccount

# Buy more RAM
proton ram:buy myaccount myaccount 50000 -p myaccount@active
```

### "account does not exist"

**Cause**: Target account not found on chain.

**Solutions**:
```bash
# Verify account exists
proton account targetaccount

# Check spelling (must be 1-12 chars, a-z, 1-5)
```

---

## RPC/Query Errors

### "table not found"

**Cause**: Table doesn't exist or wrong parameters.

**Solutions**:
```typescript
// Check contract is deployed
const abi = await rpc.get_abi('mycontract');
console.log('Tables:', abi.abi?.tables);

// Verify table name matches ABI
const { rows } = await rpc.get_table_rows({
  code: 'mycontract',
  scope: 'mycontract',  // Usually same as code
  table: 'tablename',   // Must match @table decorator
});
```

### Empty rows returned

**Causes**:
1. Wrong scope
2. No data in table
3. Wrong bounds

**Solutions**:
```typescript
// Check scope - often account name for user data
const { rows } = await rpc.get_table_rows({
  code: 'eosio.token',
  scope: 'alice',  // User's account as scope for balances
  table: 'accounts',
});

// Try without bounds first
const { rows } = await rpc.get_table_rows({
  code: 'mycontract',
  scope: 'mycontract',
  table: 'mytable',
  limit: 1000  // Get all to verify data exists
});
```

### "ECONNREFUSED" / Network errors

**Cause**: RPC endpoint down or unreachable.

**Solutions**:
```typescript
// Use multiple endpoints with fallback
const ENDPOINTS = [
  'https://proton.eosusa.io',
  'https://proton.greymass.com',
  'https://proton.cryptolions.io'
];

async function queryWithFallback(query: Function) {
  for (const endpoint of ENDPOINTS) {
    try {
      const rpc = new JsonRpc(endpoint);
      return await query(rpc);
    } catch (e) {
      console.warn(`Endpoint ${endpoint} failed, trying next...`);
    }
  }
  throw new Error('All endpoints failed');
}
```

---

## Frontend/Wallet Errors

### "User cancelled request"

**Cause**: User rejected transaction in wallet.

**Solution**: Handle gracefully
```typescript
try {
  await session.transact({ actions }, { broadcast: true });
} catch (error) {
  if (error.message.includes('cancelled')) {
    showMessage('Transaction cancelled');
    return;
  }
  throw error;
}
```

### Session not restoring

**Cause**: Session data corrupted or cleared.

**Solutions**:
```typescript
// Clear and re-login
localStorage.removeItem('proton-storage-actor');
localStorage.removeItem('proton-storage-session');
await login();
```

### WebAuth iOS caching issue

**Symptom**: After logout/login with different account, transactions fail with wrong account signature.

**Cause**: iOS app caches session.

**Workaround**:
- Force quit WebAuth iOS app before switching accounts
- Use webauth.com web wallet instead

### Mobile signing stuck on "Processing"

**Symptom**: Transaction signing works on desktop but hangs indefinitely on mobile. WebAuth app doesn't open.

**Cause**: Missing `@proton/link` package which provides mobile transport.

**Solution**:
```bash
npm install @proton/link
```

Then add the import (no need to use it directly):
```typescript
import ProtonWebSDK from '@proton/web-sdk';
import '@proton/link'; // Required for mobile
```

### Safari iOS: WebAuth popup blocked

**Symptom**: On Safari iOS, clicking actions that require wallet signing shows "Processing..." forever. The WebAuth popup never opens.

**Cause**: Safari iOS blocks popups by default, and WebAuth browser wallet uses popups for signing.

**Solution**:
1. Go to **Settings** > **Safari** on iOS device
2. Turn **OFF** "Block Pop-ups"

Alternatively, users can:
- Use the WebAuth mobile app (deep links work without popups)
- Use a different browser like Chrome on iOS

**Developer tip**: Show a help message after several seconds of stuck "processing" to guide users.

### "Cannot read property of null"

**Cause**: Session not initialized.

**Solution**:
```typescript
// Always check session before transact
if (!session) {
  showError('Please connect wallet first');
  return;
}

await session.transact({ actions }, { broadcast: true });
```

---

## Contract Deployment Errors

### "WASM file too large"

**Cause**: Contract exceeds size limits.

**Solutions**:
- Optimize code (remove unused imports)
- Split into multiple contracts
- Use release build optimizations

```bash
# Check WASM size
ls -lh assembly/target/mycontract.wasm
```

### "ABI mismatch"

**Cause**: Action parameters don't match deployed ABI.

**Solutions**:
```bash
# Check deployed ABI
proton contract:abi mycontract

# Redeploy with updated ABI
proton contract:set mycontract ./assembly/target -a
```

### "Contract already deployed"

Not actually an error - deployment updates the existing contract.

### "Invalid ABI"

**Cause**: ABI generation failed during build.

**Solutions**:
```bash
# Clean and rebuild
rm -rf assembly/target
npm run build

# Check for TypeScript errors
npx tsc --noEmit
```

---

## CLI Errors

### "Key not found"

**Cause**: Private key not in CLI storage.

**Solutions**:
```bash
# List stored keys
proton key:list

# Add the key
proton key:add PVT_K1_xxxxx
```

### "Permission denied"

**Cause**: Key doesn't match account's permission.

**Solutions**:
```bash
# Check account permissions
proton account myaccount

# Verify key matches
proton key:list
```

### "Command not found: proton"

**Cause**: CLI not installed or not in PATH.

**Solutions**:
```bash
# Install globally
npm install -g @proton/cli

# Or check PATH
which proton
```

---

## Contract Logic Errors

### Infinite loop / Transaction timeout

**Cause**: Loop without bounds or inefficient algorithm.

**Solutions**:
```typescript
// BAD - unbounded
while (cursor) {
  // process
  cursor = table.next(cursor);
}

// GOOD - limit iterations
let count = 0;
const MAX = 100;
while (cursor && count < MAX) {
  // process
  cursor = table.next(cursor);
  count++;
}
```

### Table data corruption

**Cause**: Modified table structure after deployment.

**Solutions**:
See `safety-guidelines.md` - NEVER modify existing table schemas.

Recovery:
```bash
# Rollback to old ABI
# Remove new field from code
npm run build
proton contract:set mycontract ./assembly/target
```

### Inline action not executing

**Cause**: Missing `eosio.code` permission.

**Solutions**:
```bash
# Enable inline actions
proton contract:enableinline mycontract

# Or manually add eosio.code
proton action eosio updateauth '{
  "account": "mycontract",
  "permission": "active",
  "parent": "owner",
  "auth": {
    "threshold": 1,
    "keys": [{"key": "PUB_K1_xxx", "weight": 1}],
    "accounts": [
      {"permission": {"actor": "mycontract", "permission": "eosio.code"}, "weight": 1}
    ],
    "waits": []
  }
}' mycontract@owner
```

---

## NFT Errors

### "Collection not found"

**Cause**: Collection doesn't exist or wrong name.

**Solutions**:
```bash
# Check collection exists
curl "https://proton.api.atomicassets.io/atomicassets/v1/collections/COLLECTION_NAME"
```

### "Not authorized to mint"

**Cause**: Account not in collection's `authorized_accounts`.

**Solutions**:
```typescript
// Add authorized account
await session.transact({
  actions: [{
    account: 'atomicassets',
    name: 'addcolauth',
    authorization: [{ actor: collectionOwner, permission: 'active' }],
    data: {
      collection_name: 'mycollection',
      account_to_add: 'minter'
    }
  }]
});
```

### "Template max supply reached"

**Cause**: Tried to mint beyond template's max_supply.

**Solution**: Create new template or use template with higher/unlimited supply.

---

## DEX Errors

### "Insufficient balance"

**Cause**: DEX balance too low.

**Solutions**:
```typescript
// Check DEX balance
const balances = await fetch(`https://dex.api.mainnet.metalx.com/dex/v1/account/balances?account=${account}`);

// Deposit more
await depositToDex(account, '100.0000 XPR', 'eosio.token');
```

### "Order would cross"

**Cause**: Post-only order would match immediately.

**Solution**: Adjust price or use regular limit order.

---

## Quick Diagnostic Commands

```bash
# Check chain status
proton chain:info

# Check account
proton account ACCOUNT -t

# Check contract ABI
proton contract:abi CONTRACT

# Check table data
proton table CONTRACT TABLE

# Check transaction
proton transaction:get TX_ID

# Check recent actions
curl "https://proton.eosusa.io/v2/history/get_actions?account=ACCOUNT&limit=10"
```

---

## Getting Help

### Resources

1. **Block Explorer**: https://explorer.xprnetwork.org - Check transactions and errors
2. **Discord**: https://discord.gg/xprnetwork - Community help
3. **GitHub Issues**: https://github.com/XPRNetwork - Report bugs
4. **Hyperion**: Check transaction history for debugging

### Information to Include When Asking for Help

- Error message (exact text)
- Transaction ID (if applicable)
- Account name
- Action being attempted
- Code snippet (if relevant)
- Network (mainnet/testnet)
