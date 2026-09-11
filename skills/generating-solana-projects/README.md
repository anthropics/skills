# Generating Solana Projects - Claude Code Skill

A Claude Code skill for generating complete, production-ready Solana blockchain projects with Anchor framework and Next.js frontend.

## Overview

This skill automates the creation of Solana dApps with proper structure, configuration, and best practices. It generates:

- Complete Anchor framework project structure (v0.32.1)
- Rust smart contracts with proper state management and error handling
- TypeScript tests with Anchor testing framework
- Next.js frontend with wallet integration
- All necessary configuration files

## Use Cases

- NFT marketplaces
- Token programs (SPL tokens)
- DAOs (Decentralized Autonomous Organizations)
- DeFi protocols
- Custom Solana dApps

## Installation

1. Copy the entire `generating-solana-projects` directory to your Claude Code skills folder:
   ```
   ~/.claude/skills/generating-solana-projects/
   ```

2. The skill will be automatically available in Claude Code

## Usage

Simply ask Claude Code to create a Solana project:

```
Create a Solana NFT marketplace project
```

```
Generate a Solana token program with transfer and mint features
```

```
Build a Solana voting DAO
```

## What Gets Generated

### Project Structure
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

### Technologies

- **Anchor Framework**: 0.32.1
- **Rust**: Latest stable with anchor-lang 0.32.1
- **Next.js**: 14.0.4
- **Solana Web3.js**: 1.87.6
- **TypeScript**: For tests and frontend

## Post-Generation Steps

After Claude generates your project:

1. Generate program ID:
   ```bash
   anchor keys list
   ```

2. Update program ID in three locations:
   - `Anchor.toml`
   - `programs/{name}/src/lib.rs` (declare_id!)
   - `app/src/utils/anchorSetup.ts`

3. Build the project:
   ```bash
   anchor build
   ```

4. Deploy to devnet:
   ```bash
   anchor deploy
   ```

5. Run tests:
   ```bash
   anchor test
   ```

6. Start the frontend:
   ```bash
   cd app
   npm install
   npm run dev
   ```

## Features

- **Complete Smart Contracts**: Includes state management, instruction handlers, and custom errors
- **Comprehensive Tests**: Pre-configured test suite with Anchor testing framework
- **Wallet Integration**: Frontend includes Solana wallet adapter setup
- **Best Practices**: Follows Anchor and Solana development conventions
- **Type Safety**: Full TypeScript support in tests and frontend

## Documentation

- `SKILL.md` - Main skill configuration and workflow
- `reference.md` - Detailed templates and code snippets
- `examples.md` - Example projects and use cases

## Requirements

To use generated projects, you need:

- Rust 1.75+
- Solana CLI 1.18+
- Anchor CLI 0.32.1
- Node.js 18+

## Contributing

Feel free to submit issues or pull requests to improve this skill.

## License

MIT License - Feel free to use and modify for your projects.

## Author

Created for Claude Code to streamline Solana development.
