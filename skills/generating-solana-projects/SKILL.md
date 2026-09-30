---
name: generating-solana-projects
description: Generates complete Solana blockchain projects with Anchor framework (v0.32.1) and Next.js frontend including Rust smart contracts, tests, and wallet integration. Use when creating Solana dApps, NFT marketplaces, token programs, DAOs, DeFi protocols, or when user mentions Solana, Anchor, or blockchain projects.
allowed-tools: Bash, Write, Read
---

# Generating Solana Projects

**Goal**: Create production-ready Solana blockchain projects with Anchor framework and Next.js frontend.

## Workflow

1. **Gather requirements**: Ask user for project name, program functionality, required instructions, and frontend features
2. **Generate project structure**: Create complete directory tree following Anchor conventions
3. **Create Rust smart contract**: Generate lib.rs, state.rs, errors.rs, and instruction handlers in `programs/`
4. **Create configuration files**: Generate Anchor.toml, Cargo.toml, package.json, tsconfig.json with version 0.32.1
5. **Create tests**: Generate TypeScript test file with Anchor testing framework setup
6. **Create Next.js frontend**: Generate wallet provider setup, Anchor client, and UI components in `app/`
7. **Provide setup instructions**: Tell user to run `anchor keys list`, update program IDs, build, deploy, and test

## Critical versions

Always use these exact versions for compatibility:
- Anchor: 0.32.1
- anchor-lang (Rust): 0.32.1
- @coral-xyz/anchor (JS): ^0.32.1
- @solana/web3.js: ^1.87.6
- Next.js: 14.0.4

## Project structure template

```
{project-name}/
├── Anchor.toml
├── Cargo.toml (workspace)
├── package.json
├── programs/{program-name}/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── state.rs
│       ├── errors.rs
│       └── instructions/
├── tests/{program-name}.ts
└── app/ (Next.js)
    ├── package.json
    └── src/
        ├── pages/_app.tsx
        ├── components/
        └── utils/anchorSetup.ts
```

## Important reminders

After generation, user must:
1. Generate program ID: `anchor keys list`
2. Update program ID in three locations: Anchor.toml, lib.rs (declare_id!), anchorSetup.ts
3. Build before deploying: `anchor build` generates IDL and types needed by frontend

For detailed templates, code snippets, and examples, see [reference.md](reference.md) and [examples.md](examples.md).
