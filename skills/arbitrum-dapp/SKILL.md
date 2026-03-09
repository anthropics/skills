---
name: arbitrum-dapp-skill
description: Opinionated guide for building dApps on Arbitrum using Stylus (Rust) and/or Solidity. Covers local devnode setup, contract development, testing, deployment, and React frontend integration with viem. Use when starting a new Arbitrum project, writing Stylus or Solidity contracts, deploying to Arbitrum, or building a frontend that interacts with Arbitrum contracts.
---

# Arbitrum dApp Development

## Stack

| Layer | Tool | Notes |
|-------|------|-------|
| Smart contracts (Rust) | `stylus-sdk` v0.10+ | Compiled to WASM, runs on Stylus VM |
| Smart contracts (Solidity) | Solidity 0.8.x + Foundry | Standard EVM path on Arbitrum |
| Local node | `nitro-devnode` | Docker-based local Arbitrum chain |
| Contract CLI | `cargo-stylus` | Check, deploy, export-abi for Stylus |
| Contract toolchain | Foundry (`forge`, `cast`, `anvil`) | Build, test, deploy, interact for Solidity |
| Frontend | React / Next.js + viem + wagmi | viem for all chain interaction |
| Package manager | pnpm | Workspace-friendly, fast |

## Decision Flow

When starting a new contract:

1. **Need max performance / lower gas?** → Stylus Rust. See `references/stylus-rust-contracts.md`.
2. **Need broad tooling compatibility / rapid prototyping?** → Solidity. See `references/solidity-contracts.md`.
3. **Hybrid?** → Use both. Stylus and Solidity contracts are fully interoperable on Arbitrum.

## Project Scaffolding

### Monorepo layout (recommended)

```
my-arbitrum-dapp/
├── apps/
│   ├── frontend/            # React / Next.js app
│   ├── contracts-stylus/    # Rust Stylus contracts
│   ├── contracts-solidity/  # Foundry Solidity contracts
│   └── nitro-devnode/       # Local dev chain (git submodule)
├── pnpm-workspace.yaml
└── package.json
```

### Bootstrap steps

```bash
# 1. Create workspace
mkdir my-arbitrum-dapp && cd my-arbitrum-dapp
pnpm init
printf "packages:\n  - 'apps/*'\n" > pnpm-workspace.yaml

# 2. Local devnode
git clone https://github.com/OffchainLabs/nitro-devnode.git apps/nitro-devnode
cd apps/nitro-devnode && ./run-dev-node.sh && cd ../..

# 3a. Stylus contract
cargo stylus new apps/contracts-stylus

# 3b. Solidity contract
cd apps && forge init contracts-solidity && cd ..

# 4. Frontend
pnpm create next-app apps/frontend --typescript
cd apps/frontend
pnpm add viem wagmi @tanstack/react-query
```

## Core Workflow

### Stylus Rust

```bash
# Validate
cargo stylus check --endpoint http://localhost:8547

# Deploy (uses the nitro-devnode pre-funded deployer account)
cargo stylus deploy \
  --endpoint http://localhost:8547 \
  --private-key $PRIVATE_KEY

# Export ABI for frontend consumption
cargo stylus export-abi
```

### Solidity (Foundry)

```bash
# Build
forge build

# Test
forge test

# Deploy locally (uses the nitro-devnode pre-funded deployer account)
forge script script/Deploy.s.sol --rpc-url http://localhost:8547 --broadcast \
  --private-key $PRIVATE_KEY
```

> **Note:** The nitro-devnode ships with a pre-funded deployer account. See `references/local-devnode.md` for the default private key and address. For testnet/mainnet, use your own key via environment variables — never hardcode secrets.

### Frontend (viem + wagmi)

```typescript
import { createPublicClient, http } from "viem";
import { arbitrumSepolia } from "viem/chains";

const client = createPublicClient({
  chain: arbitrumSepolia,
  transport: http(),
});

// Read from contract
const result = await client.readContract({
  address: "0x...",
  abi: contractAbi,
  functionName: "myFunction",
});
```

See `references/frontend-integration.md` for full patterns with wagmi hooks, wallet connection, and write transactions.

## Principles

- **Always use viem** for chain interaction.
- **Test locally first** against nitro-devnode before deploying to testnet.
- **Export ABIs** from both Stylus (`cargo stylus export-abi`) and Solidity (`forge inspect`) and keep them in a shared location the frontend can import.
- **Use environment variables** for RPC URLs, contract addresses, and private keys. Never hardcode secrets.
- **Stylus contracts are EVM-compatible** — they share the same address space, storage model, and ABI encoding as Solidity contracts. Cross-contract calls work seamlessly.

## References

Load these as needed for deeper guidance:

- `references/stylus-rust-contracts.md` — Stylus SDK patterns, storage, macros, entrypoints
- `references/solidity-contracts.md` — Solidity on Arbitrum specifics and Foundry workflow
- `references/frontend-integration.md` — React + viem + wagmi patterns
- `references/local-devnode.md` — Nitro devnode setup, accounts, and debugging
- `references/deployment.md` — Deploying to testnet and mainnet
- `references/testing.md` — Testing strategies for both Stylus and Solidity
