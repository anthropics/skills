# Solana Anchor Project - Technical Reference

Complete templates and configuration details for generating Solana blockchain projects.

## Contents

1. **Version Requirements** - Exact versions for all dependencies
2. **Project Directory Structure** - Complete file tree
3. **Configuration Files** - Anchor.toml, Cargo.toml, package.json, tsconfig.json
4. **Rust Program Templates** - lib.rs, state.rs, errors.rs, instruction handlers
5. **Test Templates** - TypeScript test file structure
6. **Frontend Templates** - Next.js app configuration, wallet setup, components
7. **Build & Deploy Commands** - Complete workflow from install to deploy
8. **Generated Files** - Target directory structure after build

---

## Project Template Configuration

Based on the solana-voting-system template:

### Version Requirements
- **Anchor**: 0.32.1
- **anchor-lang (Rust)**: 0.32.1
- **@coral-xyz/anchor (JS)**: ^0.32.1
- **@solana/web3.js**: ^1.87.6
- **Next.js**: 14.0.4
- **React**: ^18.2.0
- **TypeScript**: ^5.0.0

### Wallet Adapters
- @solana/wallet-adapter-base: ^0.9.23
- @solana/wallet-adapter-react: ^0.15.35
- @solana/wallet-adapter-react-ui: ^0.9.35
- @solana/wallet-adapter-wallets: ^0.19.32

---

## Instructions

When user requests to create a new Solana project, follow this template structure:

### 1. Project Directory Structure

```
{project-name}/
├── .anchor/
├── .gitignore
├── Anchor.toml
├── package.json
├── tsconfig.json
├── README.md
├── programs/
│   └── {program-name}/
│       ├── Cargo.toml
│       ├── Cargo.lock
│       └── src/
│           ├── lib.rs
│           ├── state.rs
│           ├── errors.rs
│           └── instructions/
│               ├── mod.rs
│               └── {instruction_files}.rs
├── tests/
│   └── {program-name}.ts
├── target/
│   ├── deploy/
│   ├── idl/
│   └── types/
└── app/
    ├── .gitignore
    ├── package.json
    ├── tsconfig.json
    ├── next.config.js
    └── src/
        ├── pages/
        │   ├── _app.tsx
        │   └── index.tsx
        ├── components/
        │   └── {component_files}.tsx
        ├── styles/
        │   └── globals.css
        └── utils/
            └── anchorSetup.ts
```

### 2. Create Anchor.toml

```toml
[toolchain]
anchor_version = "0.32.1"

[features]
seeds = false
skip-lint = false

[programs.localnet]
{program_name} = "{PROGRAM_ID}"

[programs.devnet]
{program_name} = "{PROGRAM_ID}"

[registry]
url = "https://api.apr.dev"

[provider]
cluster = "Localnet"
wallet = "~/.config/solana/id.json"

[scripts]
test = "yarn run ts-mocha -p ./tsconfig.json -t 1000000 tests/**/*.ts"
```

### 3. Create Root package.json

```json
{
  "name": "{project-name}",
  "version": "1.0.0",
  "description": "{project-description}",
  "scripts": {
    "test": "anchor test"
  },
  "dependencies": {
    "@coral-xyz/anchor": "^0.32.1",
    "@solana/web3.js": "^1.87.6"
  },
  "devDependencies": {
    "@types/bn.js": "^5.1.0",
    "@types/chai": "^4.3.0",
    "@types/mocha": "^9.0.0",
    "chai": "^4.3.4",
    "mocha": "^9.0.3",
    "ts-mocha": "^10.0.0",
    "typescript": "^5.0.0"
  }
}
```

### 4. Create Root tsconfig.json

```json
{
    "compilerOptions": {
        "types": ["mocha", "chai"],
        "typeRoots": ["./node_modules/@types"],
        "lib": ["es2015"],
        "module": "commonjs",
        "target": "es6",
        "esModuleInterop": true,
        "skipLibCheck": true,
        "strict": true,
        "resolveJsonModule": true
    }
}
```

### 5. Create .gitignore

```
.anchor
.DS_Store
target
**/*.rs.bk
node_modules
test-ledger
.yarn
.cargo
```

### 6. Create Program Cargo.toml

Path: `programs/{program-name}/Cargo.toml`

```toml
[package]
name = "{program_name}"
version = "0.1.0"
description = "{program-description}"
edition = "2021"

[lib]
crate-type = ["cdylib", "lib"]
name = "{program_name}"

[features]
no-entrypoint = []
no-idl = []
no-log-ix-name = []
cpi = ["no-entrypoint"]
idl-build = ["anchor-lang/idl-build"]
default = []

[dependencies]
anchor-lang = "0.32.1"
```

### 7. Create Program lib.rs Template

Path: `programs/{program-name}/src/lib.rs`

```rust
use anchor_lang::prelude::*;

pub mod state;
pub mod instructions;
pub mod errors;

use instructions::*;

declare_id!("{PROGRAM_ID}");

#[program]
pub mod {program_name} {
    use super::*;

    // Add instruction handlers here
    // Example:
    // pub fn initialize(ctx: Context<Initialize>, param: Type) -> Result<()> {
    //     instructions::initialize::handler(ctx, param)
    // }
}
```

### 8. Create Program state.rs Template

Path: `programs/{program-name}/src/state.rs`

```rust
use anchor_lang::prelude::*;

#[account]
pub struct {StateName} {
    // Define account fields here
    // Example:
    // pub owner: Pubkey,           // 32 bytes
    // pub data: String,            // 4 + max_len bytes
    // pub is_initialized: bool,    // 1 byte
    // pub created_at: i64,         // 8 bytes
}

impl {StateName} {
    // Calculate space: 8 (discriminator) + field sizes
    pub const MAX_SIZE: usize = 8 + 32 + 4 + 200 + 1 + 8;
}
```

### 9. Create Program errors.rs Template

Path: `programs/{program-name}/src/errors.rs`

```rust
use anchor_lang::prelude::*;

#[error_code]
pub enum {ProgramName}Error {
    #[msg("Error description here.")]
    ErrorName,
}
```

### 10. Create Program instructions/mod.rs Template

Path: `programs/{program-name}/src/instructions/mod.rs`

```rust
pub mod {instruction_name};

pub use {instruction_name}::*;
```

### 11. Create Instruction Template

Path: `programs/{program-name}/src/instructions/{instruction_name}.rs`

```rust
use anchor_lang::prelude::*;
use crate::state::{StateName};
use crate::errors::{ProgramName}Error;

#[derive(Accounts)]
pub struct {InstructionName}<'info> {
    #[account(
        init,  // or mut for existing accounts
        payer = user,
        space = {StateName}::MAX_SIZE
    )]
    pub account: Account<'info, {StateName}>,

    #[account(mut)]
    pub user: Signer<'info>,

    pub system_program: Program<'info, System>,
}

pub fn handler(ctx: Context<{InstructionName}>, /* params */) -> Result<()> {
    let account = &mut ctx.accounts.account;
    // Implementation here
    Ok(())
}
```

### 12. Create Test File Template

Path: `tests/{program-name}.ts`

```typescript
import * as anchor from "@coral-xyz/anchor";
import { Program } from "@coral-xyz/anchor";
import { {ProgramType} } from "../target/types/{program_name}";
import { expect } from "chai";

describe("{program-name}", () => {
    const provider = anchor.AnchorProvider.env();
    anchor.setProvider(provider);

    const program = anchor.workspace.{ProgramName} as Program<{ProgramType}>;

    it("Test case description", async () => {
        // Test implementation
    });
});
```

### 13. Create Frontend app/package.json

```json
{
    "name": "{project-name}-dapp",
    "version": "0.1.0",
    "private": true,
    "scripts": {
        "dev": "next dev",
        "build": "next build",
        "start": "next start",
        "lint": "next lint"
    },
    "dependencies": {
        "@coral-xyz/anchor": "^0.32.1",
        "@solana/wallet-adapter-base": "^0.9.23",
        "@solana/wallet-adapter-react": "^0.15.35",
        "@solana/wallet-adapter-react-ui": "^0.9.35",
        "@solana/wallet-adapter-wallets": "^0.19.32",
        "@solana/web3.js": "^1.87.6",
        "next": "14.0.4",
        "react": "^18.2.0",
        "react-dom": "^18.2.0"
    },
    "devDependencies": {
        "@types/node": "^20",
        "@types/react": "^18",
        "@types/react-dom": "^18",
        "typescript": "^5"
    }
}
```

### 14. Create Frontend app/tsconfig.json

```json
{
    "compilerOptions": {
        "target": "es5",
        "lib": ["dom", "dom.iterable", "esnext"],
        "allowJs": true,
        "skipLibCheck": true,
        "strict": true,
        "noEmit": true,
        "esModuleInterop": true,
        "module": "esnext",
        "moduleResolution": "bundler",
        "resolveJsonModule": true,
        "isolatedModules": true,
        "jsx": "preserve",
        "incremental": true,
        "paths": {
            "@/*": ["./src/*"]
        }
    },
    "include": ["next-env.d.ts", "**/*.ts", "**/*.tsx"],
    "exclude": ["node_modules"]
}
```

### 15. Create Frontend app/next.config.js

```javascript
/** @type {import('next').NextConfig} */
const nextConfig = {
    reactStrictMode: true,
    webpack: (config) => {
        config.resolve.fallback = {
            ...config.resolve.fallback,
            fs: false,
            path: false,
            crypto: false,
        };
        return config;
    },
}

module.exports = nextConfig
```

### 16. Create Frontend app/src/pages/_app.tsx

```tsx
import '@/styles/globals.css';
import '@solana/wallet-adapter-react-ui/styles.css';
import type { AppProps } from 'next/app';
import { useMemo } from 'react';
import { ConnectionProvider, WalletProvider } from '@solana/wallet-adapter-react';
import { WalletAdapterNetwork } from '@solana/wallet-adapter-base';
import { WalletModalProvider } from '@solana/wallet-adapter-react-ui';
import { PhantomWalletAdapter, SolflareWalletAdapter } from '@solana/wallet-adapter-wallets';
import { clusterApiUrl } from '@solana/web3.js';

export default function App({ Component, pageProps }: AppProps) {
    // Use localhost for local development
    const endpoint = 'http://127.0.0.1:8899';

    const wallets = useMemo(
        () => [
            new PhantomWalletAdapter(),
            new SolflareWalletAdapter(),
        ],
        []
    );

    return (
        <ConnectionProvider endpoint={endpoint}>
            <WalletProvider wallets={wallets} autoConnect>
                <WalletModalProvider>
                    <Component {...pageProps} />
                </WalletModalProvider>
            </WalletProvider>
        </ConnectionProvider>
    );
}
```

### 17. Create Frontend app/src/utils/anchorSetup.ts

```typescript
import { AnchorProvider, Program } from '@coral-xyz/anchor';
import { Connection, PublicKey } from '@solana/web3.js';
import { AnchorWallet } from '@solana/wallet-adapter-react';
import idl from '../../../target/idl/{program_name}.json';
import type { {ProgramType} } from '../../../target/types/{program_name}';

const PROGRAM_ID = new PublicKey('{PROGRAM_ID}');

export function getProgram(wallet: AnchorWallet, connection: Connection) {
    const provider = new AnchorProvider(connection, wallet, {
        commitment: 'confirmed',
    });

    return new Program(idl as unknown as {ProgramType}, provider);
}

export { PROGRAM_ID };
```

### 18. Create Frontend app/.gitignore

```
node_modules
.next
out
.DS_Store
```

---

## Build & Deploy Commands

After generating the project, run:

```bash
# Install dependencies
yarn install
cd app && yarn install && cd ..

# Generate new program ID (first time only)
anchor keys list
# Update PROGRAM_ID in Anchor.toml, lib.rs, and anchorSetup.ts

# Build the program
anchor build

# Start local validator
solana-test-validator

# Deploy to localnet
anchor deploy

# Run tests
anchor test

# Start frontend dev server
cd app && yarn dev
```

---

## Target Directory Structure (Generated after build)

```
target/
├── deploy/
│   └── {program_name}.so          # Compiled program binary
├── idl/
│   └── {program_name}.json        # Program IDL for clients
├── types/
│   ├── index.ts
│   └── {program_name}.ts          # TypeScript types
├── debug/
├── release/
└── sbpf-solana-solana/
    └── release/
        └── {program_name}.so
```

---

## Usage Example

User: "Create a Solana NFT marketplace project"

Response: Create project with:
- Project name: solana-nft-marketplace
- Program name: nft_marketplace
- States: Listing, Offer, Collection
- Instructions: create_listing, make_offer, accept_offer, cancel_listing
- Frontend components: ListingCard, CreateListing, OfferModal, WalletConnect
