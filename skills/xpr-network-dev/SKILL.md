---
name: xpr-network-dev
description: Comprehensive knowledge for XPR Network blockchain development. Use this skill when users ask about XPR Network (formerly Proton), including smart contracts with proton-tsc/AssemblyScript, @proton/cli commands, @proton/web-sdk wallet integration, RPC/Hyperion API queries, MetalX DEX trading, LOAN protocol DeFi, AtomicAssets NFTs, node operation, or Block Producer setup. Triggers on mentions of XPR, Proton blockchain, WebAuth wallet, proton-tsc, or XPR Network ecosystem tools.
license: MIT
metadata:
  author: XPRNetwork
  version: "1.0.0"
  repository: https://github.com/XPRNetwork/xpr-network-dev-skill
---

# XPR Network Developer Skill

Build on XPR Network - a fast, gas-free blockchain with 0.5s blocks, WebAuthn wallet support, and human-readable account names.

> **IMPORTANT**: AI-generated smart contract code should always be reviewed by experienced developers before mainnet deployment. Test thoroughly on testnet, understand the code, and consider professional audits for contracts handling significant value.

## Quick Reference

### Chain IDs

| Network | Chain ID |
|---------|----------|
| Mainnet | `384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0` |
| Testnet | `71ee83bcf52142d61019d95f9cc5427ba6a0d7ff8accd9e2088ae2abeaf3d3dd` |

### CLI Commands

```bash
# Install
npm i -g @proton/cli

# Set network
proton chain:set proton          # Mainnet
proton chain:set proton-test     # Testnet

# Account info
proton account myaccount -t      # With token balances

# Query table
proton table CONTRACT TABLE

# Execute action
proton action CONTRACT ACTION 'JSON_DATA' AUTHORIZATION

# Deploy contract
proton contract:set ACCOUNT ./assembly/target
```

### RPC Query

```javascript
const { JsonRpc } = require('@proton/js');
const rpc = new JsonRpc('https://proton.eosusa.io');

const { rows } = await rpc.get_table_rows({
  code: 'CONTRACT',
  scope: 'CONTRACT',
  table: 'TABLE',
  limit: 100
});
```

### Basic Contract

```typescript
import { Contract, Table, TableStore, Name, requireAuth } from 'proton-tsc';

@table("mydata")
class MyData extends Table {
  constructor(
    public id: u64 = 0,
    public owner: Name = new Name(),
    public value: string = ""
  ) { super(); }

  @primary
  get primary(): u64 { return this.id; }
}

@contract
class MyContract extends Contract {
  dataTable: TableStore<MyData> = new TableStore<MyData>(this.receiver);

  @action("store")
  store(owner: Name, value: string): void {
    requireAuth(owner);
    const row = new MyData(this.dataTable.availablePrimaryKey, owner, value);
    this.dataTable.store(row, this.receiver);
  }
}
```

### Frontend Wallet Login

```typescript
import ProtonWebSDK from '@proton/web-sdk';

const { link, session } = await ProtonWebSDK({
  linkOptions: {
    chainId: '384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0',
    endpoints: ['https://proton.eosusa.io']
  },
  selectorOptions: { appName: 'My App' }
});

// session.auth contains { actor, permission }
// Use session.transact() for transactions
```

## Key Packages

| Package | Purpose |
|---------|---------|
| `@proton/cli` | CLI tools (`npm i -g @proton/cli`) |
| `proton-tsc` | Contract SDK (`npm i proton-tsc`) |
| `@proton/web-sdk` | Frontend wallet (`npm i @proton/web-sdk`) |
| `@proton/js` | RPC queries (`npm i @proton/js`) |

## RPC Endpoints

| Network | Endpoint |
|---------|----------|
| Mainnet | `https://proton.eosusa.io` |
| Mainnet | `https://api.protonnz.com` |
| Testnet | `https://tn1.protonnz.com` |

## Detailed Reference Guides

Load these references based on the task:

### Core Development
- **[smart-contracts.md](references/smart-contracts.md)** - Tables, actions, auth, inline actions, build/deploy
- **[cli-reference.md](references/cli-reference.md)** - Full CLI command reference
- **[web-sdk.md](references/web-sdk.md)** - Frontend wallet integration, sessions, transactions
- **[rpc-queries.md](references/rpc-queries.md)** - RPC API, Hyperion history, pagination
- **[backend-patterns.md](references/backend-patterns.md)** - Server-side signing, bots, security
- **[testing-debugging.md](references/testing-debugging.md)** - Unit tests, testnet testing, debugging

### Accounts & Identity
- **[accounts-permissions.md](references/accounts-permissions.md)** - Account creation, permissions, multisig
- **[webauth-identity.md](references/webauth-identity.md)** - WebAuth wallets, KYC, user profiles

### Tokens & NFTs
- **[token-creation.md](references/token-creation.md)** - Fungible tokens, issuance, vesting
- **[nfts-atomicassets.md](references/nfts-atomicassets.md)** - Collections, schemas, minting, marketplace

### DeFi & Trading
- **[metalx-dex.md](references/metalx-dex.md)** - Complete MetalX DEX API, order book, swaps
- **[defi-trading.md](references/defi-trading.md)** - Trading bots, grid strategies, market making
- **[loan-protocol.md](references/loan-protocol.md)** - LOAN lending protocol, supply, borrow, liquidations
- **[oracles-randomness.md](references/oracles-randomness.md)** - Price feeds, verifiable random numbers

### Integration
- **[real-time-events.md](references/real-time-events.md)** - Hyperion streaming, WebSockets
- **[payment-patterns.md](references/payment-patterns.md)** - Payment links, invoicing, subscriptions

### Infrastructure
- **[node-operation.md](references/node-operation.md)** - Running nodes, Block Producer setup

### Safety & Troubleshooting
- **[safety-guidelines.md](references/safety-guidelines.md)** - CRITICAL: Read before modifying contracts
- **[troubleshooting.md](references/troubleshooting.md)** - Common errors and solutions
- **[resources.md](references/resources.md)** - Endpoints, explorers, community links

## Critical Safety Rules

**NEVER modify existing table structures** once deployed with data - this breaks deserialization and makes data unreadable. Always create NEW tables for new features.

Before deploying contract updates:
1. Check if tables have data
2. Back up current ABI
3. Test on testnet first
4. Verify target account twice

## Name Change Note

XPR Network was rebranded from "Proton" in 2024. Legacy package names (`@proton/*`, `proton-tsc`) remain unchanged. The token symbol is XPR.

## Resources

- **Docs**: https://docs.xprnetwork.org
- **Explorer**: https://explorer.xprnetwork.org
- **GitHub**: https://github.com/XPRNetwork
- **Testnet Faucet**: https://resources.xprnetwork.org/faucet
