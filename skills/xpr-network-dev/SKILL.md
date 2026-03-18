---
name: xpr-network-dev
description: Comprehensive knowledge for XPR Network blockchain development - smart contracts, CLI, web SDK, DeFi, NFTs, and infrastructure
version: 1.0.0
author: XPR Network Community
repository: https://github.com/XPRNetwork/xpr-network-dev-skill
---

# XPR Network Developer Skill

This skill provides comprehensive knowledge for developing on XPR Network, a fast, gas-free blockchain with WebAuthn wallet support.

> **IMPORTANT DISCLAIMER: AI-Generated Smart Contract Code**
>
> Smart contracts handle real assets and are immutable once deployed. AI-generated code, including code produced with this skill, should **always be reviewed by an experienced developer** before deployment to mainnet.
>
> - **Test thoroughly on testnet** before any mainnet deployment
> - **Have code reviewed** by someone familiar with XPR Network/EOSIO smart contracts
> - **Audit critical contracts** - consider professional security audits for contracts handling significant value
> - **Understand the code** - don't deploy code you don't fully understand
>
> Claude can accelerate development and help with patterns, but it does not replace proper code review, testing, and auditing practices.

## XPR Network Overview

XPR Network is an EOS-based blockchain optimized for payments and identity:

| Feature | Description |
|---------|-------------|
| **Speed** | 0.5 second block times, 4000+ TPS |
| **Fees** | Zero gas fees for end users |
| **Accounts** | Human-readable names (1-12 chars, a-z, 1-5) |
| **Wallets** | WebAuthn support (Face ID, fingerprint, security keys) |
| **Contracts** | AssemblyScript/TypeScript with @proton/ts-contracts |
| **Storage** | On-chain tables with RAM-based pricing |

### Name Change: Proton → XPR Network

The blockchain was rebranded from **Proton** to **XPR Network** in 2024. You may see legacy references to "Proton" in:
- Package names (`@proton/cli`, `@proton/web-sdk`, `proton-tsc`)
- GitHub organization (`XPRNetwork`, formerly `ProtonProtocol`)
- Documentation and code comments
- Explorer (now `explorer.xprnetwork.org`, formerly `protonscan.io` and `proton.bloks.io`)

The token symbol remains **XPR** and all functionality is unchanged.

### Chain IDs

| Network | Chain ID |
|---------|----------|
| Mainnet | `384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0` |
| Testnet | `71ee83bcf52142d61019d95f9cc5427ba6a0d7ff8accd9e2088ae2abeaf3d3dd` |

## Progressive Disclosure

Load specialized modules based on your task:

### Core Development

| Module | Read When | Key Topics |
|--------|-----------|------------|
| `smart-contracts.md` | Building contracts | Tables, actions, auth, build/deploy |
| `cli-reference.md` | Using CLI tools | Network, keys, deploy, queries |
| `web-sdk.md` | Building dApps | Wallet connect, transactions, sessions |
| `backend-patterns.md` | Server-side dev | Programmatic signing, bots, security |
| `rpc-queries.md` | Reading chain data | RPC, Hyperion API, Light API, pagination |
| `testing-debugging.md` | Testing contracts | Unit tests, testnet, debugging, logs |
| `accounts-permissions.md` | Account management | Create accounts, permissions, multisig |
| `staking-governance.md` | Staking & voting | XPR staking, BPs, DPoS, resource model |

### Token & Identity

| Module | Read When | Key Topics |
|--------|-----------|------------|
| `token-creation.md` | Creating tokens | Fungible tokens, issuance, vesting |
| `webauth-identity.md` | User identity | WebAuth wallets, KYC, profiles, trust |
| `nfts-atomicassets.md` | NFT development | Collections, schemas, minting, marketplace |

### DeFi & Trading

| Module | Read When | Key Topics |
|--------|-----------|------------|
| `metalx-dex.md` | DEX integration | Complete MetalX API, orders, swaps |
| `defi-trading.md` | Trading bots/DeFi | Grid bots, market makers, perps architecture |
| `loan-protocol.md` | Lending protocol | LOAN protocol, supply, borrow, liquidations |
| `oracles-randomness.md` | Price feeds & RNG | Oracle prices, verifiable random numbers |

### Integration Patterns

| Module | Read When | Key Topics |
|--------|-----------|------------|
| `real-time-events.md` | Live updates | Hyperion streaming, WebSockets, notifications |
| `payment-patterns.md` | Commerce/payments | Payment links, invoicing, POS, subscriptions |

### Infrastructure

| Module | Read When | Key Topics |
|--------|-----------|------------|
| `node-operation.md` | Running nodes | API nodes, Block Producers, validators |

### Safety & Reference

| Module | Read When | Key Topics |
|--------|-----------|------------|
| `safety-guidelines.md` | **BEFORE modifying contracts** | Table rules, deployment safety, recovery |
| `troubleshooting.md` | Debugging errors | Common errors, solutions, diagnostics |
| `examples.md` | Learning patterns | PriceBattle, ProtonWall, ProtonRating |
| `resources.md` | Finding endpoints | RPC URLs, docs, explorers, community |

### CRITICAL: Before Modifying Contracts
**Read: `safety-guidelines.md`**
- **NEVER modify existing table structures with data**
- Pre-deployment checklist
- Recovery procedures

---

## Quick Reference

### Common CLI Commands

```bash
# Install CLI
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

### Common RPC Query

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

### Basic Contract Structure

```typescript
import { Contract, Table, TableStore, Name } from 'proton-tsc';

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

### Basic Frontend Login

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

---

## Key Packages

| Package | Purpose | Install |
|---------|---------|---------|
| `@proton/cli` | Command-line tools | `npm i -g @proton/cli` |
| `proton-tsc` | Contract development | `npm i proton-tsc` |
| `@proton/web-sdk` | Frontend wallet integration | `npm i @proton/web-sdk` |
| `@proton/link` | Mobile wallet transport (required with web-sdk) | `npm i @proton/link` |
| `@proton/js` | RPC queries | `npm i @proton/js` |

## Official Resources

- **Documentation**: https://docs.xprnetwork.org
- **GitHub**: https://github.com/XPRNetwork
- **Block Explorer**: https://explorer.xprnetwork.org
- **Resources Portal**: https://resources.xprnetwork.org (buy RAM, etc.)

---

## Safety Reminders

1. **NEVER modify existing table structures** once deployed with data - this breaks deserialization
2. **Always test on testnet** before mainnet deployment
3. **Verify the target account** before deploying - wrong account = overwrite existing contract
4. **Back up ABIs** before deploying changes
5. **Use new tables** for new features instead of modifying existing ones
