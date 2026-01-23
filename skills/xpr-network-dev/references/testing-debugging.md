# Testing and Debugging on XPR Network

This guide covers testing smart contracts, debugging failed transactions, and resolving common issues.

## Contract Testing

### Local Testing Setup

```bash
# Install test dependencies
npm install --save-dev proton-tsc @proton/vert jest @types/jest ts-jest
```

**Note**: `proton-tsc` provides types and includes `proton-asc` compiler. Tests use `@proton/vert` for blockchain simulation.

### Test Configuration

```json
// jest.config.js
module.exports = {
  preset: 'ts-jest',
  testEnvironment: 'node',
  testMatch: ['**/tests/**/*.test.ts'],
  moduleFileExtensions: ['ts', 'js'],
};
```

### Basic Contract Test

```typescript
// tests/mycontract.test.ts
import { Blockchain, nameToBigInt, expectToThrow } from '@proton/vert';

describe('MyContract', () => {
  let blockchain: Blockchain;
  let contract: any;
  let user1: any;
  let user2: any;

  beforeAll(async () => {
    // Initialize blockchain
    blockchain = new Blockchain();

    // Create accounts
    [contract, user1, user2] = blockchain.createAccounts('mycontract', 'user1', 'user2');

    // Deploy contract (loads .wasm and .abi from target dir)
    contract.setContract(blockchain.loadContract('assembly/target/mycontract.contract'));
  });

  beforeEach(async () => {
    // Reset state between tests
    blockchain.resetTables();
  });

  test('should store value', async () => {
    await contract.actions.store(['user1', 'Hello World']).send('user1@active');

    // Check table
    const rows = contract.tables.mydata().getTableRows();
    expect(rows.length).toBe(1);
    expect(rows[0].value).toBe('Hello World');
  });

  test('should fail without auth', async () => {
    await expectToThrow(
      contract.actions.store(['user1', 'Hello']).send('user2@active'),
      'missing authority of user1'
    );
  });

  test('should validate input', async () => {
    await expectToThrow(
      contract.actions.store(['user1', '']).send('user1@active'),
      'Value cannot be empty'
    );
  });
});
```

### Testing Token Transfers

```typescript
test('should handle incoming transfer', async () => {
  // Setup token contract
  const eosioToken = blockchain.createAccount('eosio.token');
  eosioToken.setContract(blockchain.loadContract('eosio.token'));

  // Create and issue tokens
  await eosioToken.actions.create(['eosio.token', '1000000.0000 XPR']).send();
  await eosioToken.actions.issue(['user1', '1000.0000 XPR', 'initial']).send();

  // Transfer to contract
  await eosioToken.actions.transfer([
    'user1', 'mycontract', '100.0000 XPR', 'deposit'
  ]).send('user1@active');

  // Verify contract received and processed it
  const deposits = contract.tables.deposits().getTableRows();
  expect(deposits[0].amount).toBe('100.0000 XPR');
});
```

### Testing Time-Dependent Logic

```typescript
test('should expire after duration', async () => {
  // Create challenge
  await contract.actions.create(['user1', '100.0000 XPR', 1, 300]).send('user1@active');

  // Advance blockchain time by 5 minutes
  blockchain.addTime(300);

  // Now it should be resolvable
  await contract.actions.resolve([1]).send('resolver@active');

  const challenge = contract.tables.challenges().getTableRow(1n);
  expect(challenge.status).toBe(2); // RESOLVED
});
```

---

## Testnet Testing

### Setup Testnet Account

```bash
# Switch to testnet
proton chain:set proton-test

# Create testnet account (if needed)
proton account:create mytestaccount

# Get test tokens
proton faucet:claim XPR mytestaccount
```

### Deploy to Testnet

```bash
# Build
npm run build

# Deploy
proton contract:set mytestaccount ./assembly/target

# Initialize
proton action mytestaccount init '{"owner":"mytestaccount"}' mytestaccount
```

### Testnet Verification Checklist

- [ ] Contract deploys without errors
- [ ] Init action succeeds
- [ ] All actions work as expected
- [ ] Table data persists correctly
- [ ] Inline actions execute
- [ ] Notifications fire to other contracts
- [ ] Error messages are clear

---

## Debugging Failed Transactions

### Reading Error Messages

When a transaction fails, the error message contains clues:

```
Error: assertion failure with message: Insufficient balance
```

The message after "with message:" is from your contract's `check()` calls.

### Common Error Patterns

| Error | Cause | Solution |
|-------|-------|----------|
| `missing authority of X` | Wrong authorization | Use correct account in `authorization` |
| `assertion failure with message: ...` | Contract validation failed | Check the condition in your contract |
| `account does not exist` | Invalid account name | Verify account exists on chain |
| `table not found` | Querying non-existent table | Check contract is deployed, table name correct |
| `unable to find key` | Row doesn't exist | Use `get()` with null check instead of `requireGet()` |
| `expired transaction` | Transaction took too long | Increase `expireSeconds` |
| `duplicate transaction` | Same tx submitted twice | Add unique data or wait |
| `cpu usage exceeded` | Not enough CPU | Stake more CPU or optimize contract |
| `ram usage exceeded` | Not enough RAM | Buy more RAM |

### Debugging with Proton CLI

```bash
# Check transaction details
proton transaction:get TRANSACTION_ID

# Check account resources
proton account myaccount

# Check table data
proton table mycontract mytable

# Verbose action execution
proton action mycontract myaction '{}' myaccount --verbose
```

### Debugging with Hyperion

```bash
# Get recent actions for account
curl "https://proton.eosusa.io/v2/history/get_actions?account=mycontract&limit=10"

# Get specific transaction
curl "https://proton.eosusa.io/v2/history/get_transaction?id=TX_ID"

# Filter by action name
curl "https://proton.eosusa.io/v2/history/get_actions?account=mycontract&filter=mycontract:myaction"
```

### Using Console Logs

In contracts, use `print()` for debugging (visible in local tests, not on mainnet):

```typescript
import { print, printI, printU } from 'proton-tsc';

@action("debug")
debugAction(value: u64): void {
  print("Starting debug action\n");
  printU(value);
  print("\n");

  // Your logic here
  const result = value * 2;
  print("Result: ");
  printU(result);
  print("\n");
}
```

---

## Debugging Frontend Issues

### Transaction Errors

```typescript
try {
  const result = await session.transact({
    actions: [/* ... */]
  }, { broadcast: true });
} catch (error: any) {
  console.error('Transaction failed:', error);

  // Parse the error
  if (error.message.includes('assertion failure')) {
    const match = error.message.match(/assertion failure with message: (.+)/);
    const contractError = match ? match[1] : 'Unknown contract error';
    showUserError(contractError);
  } else if (error.message.includes('User cancelled')) {
    // User rejected in wallet
    showUserError('Transaction cancelled');
  } else if (error.message.includes('expired')) {
    showUserError('Transaction expired, please try again');
  } else {
    showUserError('Transaction failed: ' + error.message);
  }
}
```

### RPC Query Debugging

```typescript
async function debugTableQuery(code: string, table: string, scope: string) {
  console.log(`Querying: ${code}::${table} (scope: ${scope})`);

  try {
    const result = await rpc.get_table_rows({
      code,
      scope,
      table,
      json: true,
      limit: 10
    });

    console.log('Result:', JSON.stringify(result, null, 2));
    console.log(`Found ${result.rows.length} rows, more: ${result.more}`);

    return result.rows;
  } catch (error) {
    console.error('Query failed:', error);

    // Check if table exists
    const abi = await rpc.get_abi(code);
    const tableExists = abi.abi?.tables?.some(t => t.name === table);
    console.log(`Table "${table}" exists in ABI: ${tableExists}`);

    throw error;
  }
}
```

### Session Debugging

```typescript
// Debug session state
function debugSession(session: any) {
  console.log('Session debug:');
  console.log('  Actor:', session?.auth?.actor);
  console.log('  Permission:', session?.auth?.permission);
  console.log('  Chain ID:', session?.chainId);
  console.log('  Link type:', session?.link?.walletType);

  // Check if session is valid
  if (!session) {
    console.error('Session is null/undefined');
  } else if (!session.auth) {
    console.error('Session has no auth');
  } else if (!session.transact) {
    console.error('Session missing transact method');
  }
}
```

---

## Block Explorer Debugging

### Proton Scan

For any transaction, check the block explorer:

```
https://explorer.xprnetwork.org/tx/TRANSACTION_ID
```

This shows:
- All actions in the transaction
- Inline actions triggered
- Table deltas (data changes)
- CPU/NET/RAM usage
- Error messages (if failed)

### Useful Explorer Views

```bash
# Account overview
https://explorer.xprnetwork.org/account/ACCOUNT_NAME

# Contract ABI
https://explorer.xprnetwork.org/account/ACCOUNT_NAME?tab=contract

# Recent transactions
https://explorer.xprnetwork.org/account/ACCOUNT_NAME?tab=transactions

# Table data
https://explorer.xprnetwork.org/account/ACCOUNT_NAME?tab=tables
```

---

## Automated Testing Script

```bash
#!/bin/bash
# test-contract.sh

set -e

CONTRACT="mycontract"
TESTNET_ACCOUNT="mytest"

echo "=== Building contract ==="
npm run build

echo "=== Deploying to testnet ==="
proton chain:set proton-test
proton contract:set $TESTNET_ACCOUNT ./assembly/target

echo "=== Running tests ==="

# Test 1: Initialize
echo "Test 1: Init"
proton action $CONTRACT init '{"owner":"'$TESTNET_ACCOUNT'"}' $TESTNET_ACCOUNT

# Test 2: Store value
echo "Test 2: Store"
proton action $CONTRACT store '{"owner":"'$TESTNET_ACCOUNT'","value":"test123"}' $TESTNET_ACCOUNT

# Test 3: Verify table
echo "Test 3: Verify"
RESULT=$(proton table $CONTRACT mydata)
if echo "$RESULT" | grep -q "test123"; then
  echo "✓ Value stored correctly"
else
  echo "✗ Value not found in table"
  exit 1
fi

# Test 4: Error case (should fail)
echo "Test 4: Error handling"
if proton action $CONTRACT store '{"owner":"'$TESTNET_ACCOUNT'","value":""}' $TESTNET_ACCOUNT 2>&1 | grep -q "assertion failure"; then
  echo "✓ Empty value correctly rejected"
else
  echo "✗ Should have rejected empty value"
  exit 1
fi

echo "=== All tests passed ==="
```

---

## Performance Profiling

### Measure CPU Usage

```typescript
// In contract, time-intensive operations
const startTime = currentTimeMs();

// ... expensive operation ...

const elapsed = currentTimeMs() - startTime;
print(`Operation took ${elapsed}ms\n`);
```

### Optimize Table Queries

```typescript
// BAD: Iterating entire table
let total: u64 = 0;
let cursor = this.dataTable.first();
while (cursor) {
  total += cursor.value;
  cursor = this.dataTable.next(cursor);
}

// GOOD: Use secondary index for filtered queries
const filtered = this.dataTable.getBySecondaryIndex(owner.N);
let total: u64 = 0;
for (let i = 0; i < filtered.length; i++) {
  total += filtered[i].value;
}
```

### RAM Optimization

```typescript
// Check RAM before operations
const ramBefore = this.getRamUsage();

// ... operation ...

const ramAfter = this.getRamUsage();
print(`RAM used: ${ramAfter - ramBefore} bytes\n`);
```

---

## CI/CD Integration

### GitHub Actions Example

```yaml
# .github/workflows/test.yml
name: Test Contract

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest

    steps:
      - uses: actions/checkout@v3

      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: '18'

      - name: Install dependencies
        run: npm install

      - name: Build contract
        run: npm run build

      - name: Run tests
        run: npm test

      - name: Upload artifacts
        uses: actions/upload-artifact@v3
        with:
          name: contract-build
          path: assembly/target/
```

---

## Quick Debug Checklist

When something doesn't work:

1. **Check the error message** - Read it carefully
2. **Verify authorization** - Is the right account signing?
3. **Check table state** - Is the data what you expect?
4. **Test on testnet first** - Never debug on mainnet
5. **Check ABI** - Is the contract deployed with current ABI?
6. **Check resources** - Does account have RAM/CPU/NET?
7. **Check block explorer** - What does the transaction show?
8. **Add logging** - Use `print()` in tests
9. **Isolate the issue** - Test one thing at a time
10. **Check timestamps** - Is time-dependent logic correct?
