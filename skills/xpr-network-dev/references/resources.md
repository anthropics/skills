# XPR Network Resources

Comprehensive list of endpoints, tools, documentation, and community resources for XPR Network development.

---

## Chain Information

### Chain IDs

| Network | Chain ID |
|---------|----------|
| **Mainnet** | `384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0` |
| **Testnet** | `71ee83bcf52142d61019d95f9cc5427ba6a0d7ff8accd9e2088ae2abeaf3d3dd` |

### Network Parameters

| Parameter | Value |
|-----------|-------|
| Block time | 0.5 seconds |
| Block producers | 21 active |
| Token symbol | XPR |
| Token precision | 4 decimals |
| Account names | 1-12 characters (a-z, 1-5) |

---

## RPC Endpoints

### Mainnet

| Endpoint | Provider | Notes |
|----------|----------|-------|
| `https://proton.eosusa.io` | EOSUSA | Primary, reliable |
| `https://api.protonnz.com` | ProtonNZ | Good backup |
| `https://api-xprnetwork-main.saltant.io` | Saltant | v1 + v2 (Hyperion) |
| `https://proton.greymass.com` | Greymass | Alternative |
| `https://proton.cryptolions.io` | CryptoLions | Alternative |

**P2P Peer:** `p2p-protonmain.saltant.io:9876`

### Testnet

| Endpoint | Provider |
|----------|----------|
| `https://tn1.protonnz.com` | ProtonNZ |
| `https://api-xprnetwork-test.saltant.io` | Saltant |

**P2P Peer:** `p2p-protontest.saltant.io:9879`

### Health Check

```bash
curl -s https://proton.eosusa.io/v1/chain/get_info | jq '.head_block_num'
```

---

## History API (Hyperion)

### Mainnet

| Endpoint |
|----------|
| `https://proton.eosusa.io/v2/history/get_actions` |
| `https://proton.eosusa.io/v2/history/get_transaction` |

### Common Queries

```bash
# Get account actions
curl "https://proton.eosusa.io/v2/history/get_actions?account=myaccount&limit=50"

# Get specific transaction
curl "https://proton.eosusa.io/v2/history/get_transaction?id=TX_ID"

# Filter by action
curl "https://proton.eosusa.io/v2/history/get_actions?account=myaccount&filter=eosio.token:transfer"
```

---

## Block Explorers

| Explorer | URL | Features |
|----------|-----|----------|
| **XPR Network Explorer (Mainnet)** | https://explorer.xprnetwork.org | Official explorer, wallet features |
| **XPR Network Explorer (Testnet)** | https://testnet.explorer.xprnetwork.org | Testnet explorer |

### Explorer Features

The XPR Network Explorer provides:
- View accounts, transactions, blocks
- Transfer tokens (single, multi, batch)
- Stake/unstake XPR
- Vote for Block Producers
- Manage account permissions and keys
- Create multi-signature (MSIG) transactions
- NFT transfers

### Direct Links

```
# Account
https://explorer.xprnetwork.org/account/ACCOUNT_NAME

# Transaction
https://explorer.xprnetwork.org/transaction/TRANSACTION_ID

# Contract
https://explorer.xprnetwork.org/account/CONTRACT_NAME?tab=contract
```

---

## Official Documentation

| Resource | URL |
|----------|-----|
| **Developer Docs** | https://docs.xprnetwork.org |
| **TypeScript Contracts** | https://docs.xprnetwork.org/contract-sdk/storage |
| **CLI Reference** | https://docs.xprnetwork.org/cli/usage |
| **Web SDK** | https://docs.xprnetwork.org/client-sdks/web |

---

## GitHub Repositories

### Official XPR Network

| Repository | Description |
|------------|-------------|
| [XPRNetwork/ts-smart-contracts](https://github.com/XPRNetwork/ts-smart-contracts) | Contract SDK (proton-tsc) |
| [XPRNetwork/proton-web-sdk](https://github.com/XPRNetwork/proton-web-sdk) | Frontend wallet integration |
| [XPRNetwork/proton-cli](https://github.com/XPRNetwork/proton-cli) | Command-line tools |
| [XPRNetwork/protonjs](https://github.com/XPRNetwork/protonjs) | JavaScript RPC library |

### Example Contracts

| Repository | Description |
|------------|-------------|
| [XPRNetwork/proton-ts-sc-examples](https://github.com/XPRNetwork/proton-ts-sc-examples) | Official example contracts |

### Node Infrastructure

| Repository | Description |
|------------|-------------|
| [XPRNetwork/xpr.start](https://github.com/XPRNetwork/xpr.start) | Mainnet node setup scripts and configs |
| [XPRNetwork/xpr-testnet.start](https://github.com/XPRNetwork/xpr-testnet.start) | Testnet node setup scripts and configs |
| [XPRNetwork/dex-bot](https://github.com/XPRNetwork/dex-bot) | MetalX DEX trading bot |

---

## NPM Packages

| Package | Description | Install |
|---------|-------------|---------|
| `@proton/cli` | CLI tools | `npm i -g @proton/cli` |
| `proton-tsc` | Contract compiler | `npm i proton-tsc` |
| `@proton/web-sdk` | Frontend SDK | `npm i @proton/web-sdk` |
| `@proton/js` | RPC library | `npm i @proton/js` |
| `@proton/link` | Session management | `npm i @proton/link` |

---

## Useful Tools

### Resources Portal

https://resources.xprnetwork.org

| Page | URL | Purpose |
|------|-----|---------|
| Main | https://resources.xprnetwork.org | Buy CPU/NET plans |
| Storage | https://resources.xprnetwork.org/storage | Buy/sell RAM |
| Create Account | https://resources.xprnetwork.org/create-account | Create new accounts |
| Faucet | https://resources.xprnetwork.org/faucet | Get testnet tokens |

### Resource Pricing

| Resource | Cost |
|----------|------|
| RAM Storage | 0.0022 XPR per byte |
| Free RAM (WebAuth) | 12,000 bytes per account |
| CPU/NET Basic | 100 XPR/month (~500 tx/day) |
| CPU/NET Plus | 1,000 XPR/month (~5,000 tx/day) |
| CPU/NET Pro | 10,000 XPR/month (~50,000 tx/day) |
| CPU/NET Enterprise | 100,000 XPR/month (~500,000 tx/day) |

### Faucets

| Network | Token | URL/Command |
|---------|-------|-------------|
| Testnet | XPR | `proton faucet:claim XPR myaccount` |
| Testnet | Web | https://resources.xprnetwork.org/faucet |

### Token Contracts

| Token | Contract | Decimals |
|-------|----------|----------|
| XPR | `eosio.token` | 4 |
| XUSDT | `xtokens` | 6 |
| XUSDC | `xtokens` | 6 |
| FOOBAR | `xtokens` | 6 |
| LOAN | `loan.token` | 4 |

---

## Wallets

| Wallet | Type | Platforms | Best For |
|--------|------|-----------|----------|
| **WebAuth** | Mobile/Web | iOS, Android, Web | General users (recommended) |
| **Anchor** | Mobile/Desktop | iOS, Android, Mac, Win, Linux | Advanced users, owner key access |
| **Ledger** | Hardware | Nano X, Nano S | Maximum security |
| **TokenPocket** | Mobile | iOS (TestFlight), Android | Multi-chain users |
| **Scatter** | Desktop | Mac, Windows, Linux | Desktop multi-chain |

### Wallet URLs

| Wallet | URL |
|--------|-----|
| WebAuth Web | https://webauth.com |
| WebAuth iOS | App Store |
| WebAuth Android | Play Store |
| Anchor | https://greymass.com/anchor |

### WebAuth Features

- Non-custodial (you control keys)
- WebAuthn support (Face ID, fingerprint, security keys)
- Account creation
- Staking and NFTs
- Fiat on-ramp (US, Australia, New Zealand)

---

## System Contracts

| Contract | Account | Purpose |
|----------|---------|---------|
| Token | `eosio.token` | Native XPR transfers |
| System | `eosio` | Account creation, resources |
| User profiles | `eosio.proton` | KYC, user info |
| Oracles | `oracles` | Price feeds |
| Wrapped tokens | `xtokens` | XUSDT, XUSDC, etc. |

---

## Oracle Price Feeds

| Index | Pair | Description |
|-------|------|-------------|
| 4 | BTC/USD | Bitcoin price |
| 5 | ETH/USD | Ethereum price |
| 13 | XPR/USD | XPR price |

### Query Oracle

```bash
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
```

---

## Governance & Staking

| Resource | URL | Description |
|----------|-----|-------------|
| **Governance Portal** | https://gov.xprnetwork.org | Proposals and voting |
| **Resources Portal** | https://resources.xprnetwork.org | Buy RAM, manage resources |
| **Identity Verification** | https://identity.metalx.com | KYC verification |
| **Help Desk** | https://help.xprnetwork.org | Support and FAQs |

---

## Community

| Platform | Link |
|----------|------|
| **Discord** | https://discord.gg/xprnetwork |
| **Telegram** | https://t.me/XPRNetwork |
| **Twitter/X** | https://twitter.com/XPRNetwork |

---

## Development Environment

### Recommended Setup

1. **Node.js**: v16+ (v18 LTS recommended)
2. **Editor**: VS Code with TypeScript extension
3. **CLI**: `@proton/cli` installed globally

### VS Code Extensions

- TypeScript (built-in)
- ESLint
- Prettier

### .vscode/settings.json

```json
{
  "typescript.tsdk": "node_modules/typescript/lib",
  "editor.formatOnSave": true
}
```

---

## Quick Start Commands

```bash
# Install CLI
npm i -g @proton/cli

# Set to testnet for development
proton chain:set proton-test

# Generate new key pair
proton key:generate

# Create boilerplate project
proton boilerplate myproject

# Build contract
cd myproject
npm run build

# Deploy to testnet
proton contract:set mycontract ./assembly/target

# Query contract table
proton table mycontract mytable
```

---

## Testnet vs Mainnet Checklist

| Step | Testnet | Mainnet |
|------|---------|---------|
| Set network | `proton chain:set proton-test` | `proton chain:set proton` |
| Get test tokens | `proton faucet:claim XPR account` | Purchase XPR |
| Deploy | Test thoroughly | After testnet verification |
| Test transactions | Use FOOBAR/test tokens | Real tokens |

---

## Support

- **Documentation issues**: https://github.com/XPRNetwork/ts-smart-contracts/issues
- **CLI issues**: https://github.com/XPRNetwork/proton-cli/issues
- **General questions**: Discord #developers channel

---

## License

Most XPR Network tools and SDKs are released under the MIT License.
