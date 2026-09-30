# @proton/cli Reference

Complete command reference for the Proton CLI tool used for XPR Network smart contract development, deployment, and blockchain interaction.

## Installation

```bash
npm i -g @proton/cli
# or
yarn global add @proton/cli
```

**Requires Node.js 16+**

If you get permission errors on Mac/Linux:
```bash
sudo chown -R $USER /usr/local/lib/node_modules
sudo chown -R $USER /usr/local/bin
```

---

## Network Configuration

```bash
# List available networks
proton chain:list

# Get current network
proton chain:get
# or
proton network

# Switch to mainnet
proton chain:set proton

# Switch to testnet
proton chain:set proton-test

# Get chain info (head block, etc.)
proton chain:info

# Get current RPC endpoint
proton endpoint:get

# Set custom RPC endpoint
proton endpoint:set https://proton.eosusa.io

# Restore default endpoint
proton endpoint:default
```

---

## Key Management

**IMPORTANT**: Never store private keys in code or config files!

```bash
# Generate new key pair
proton key:generate

# Add existing private key (interactive)
proton key:add

# Add key directly (will prompt for encryption)
proton key:add PVT_K1_xxxxx

# Add key without encryption prompt
echo "no" | proton key:add PVT_K1_xxxxx

# List all stored keys
proton key:list

# Get private key for a public key
proton key:get PUB_K1_xxxxx

# Lock keys with password
proton key:lock

# Unlock keys
proton key:unlock [PASSWORD]

# Remove a specific key
proton key:remove PVT_K1_xxxxx

# Reset password and delete ALL keys
proton key:reset
```

### Key Storage Location

- **Keys**: `~/.proton-cli/keys.json` (encrypted when locked)
- **Config**: `~/.proton-cli/config.json`

---

## Account Management

```bash
# Get account info
proton account myaccount

# Get account with token balances
proton account myaccount -t

# Get raw account data (JSON)
proton account myaccount -r

# Create new account
proton account:create newaccount

# Update account permissions
proton permission myaccount

# Link permission to contract action
proton permission:link myaccount mypermission mycontract

# Unlink permission
proton permission:unlink myaccount mycontract
```

---

## Smart Contract Deployment

### Build Contract

Contract files must be named `*.contract.ts` and compiled with `proton-asc`:

```bash
# Build command (in package.json)
npx proton-asc ./assembly/mycontract.contract.ts

# Output files in assembly/target/:
# - mycontract.contract.wasm
# - mycontract.contract.abi
```

### Deploy Contract

```bash
# Deploy WASM + ABI (looks for *.wasm and *.abi in target dir)
proton contract:set mycontract ./assembly/target

# Deploy only WASM
proton contract:set mycontract ./assembly/target -w

# Deploy only ABI
proton contract:set mycontract ./assembly/target -a

# Get contract ABI
proton contract:abi mycontract

# Clear contract (remove WASM + ABI)
proton contract:clear mycontract

# Clear only ABI
proton contract:clear mycontract -a

# Clear only WASM
proton contract:clear mycontract -w

# Enable inline actions on contract
proton contract:enableinline mycontract
```

### Deployment Workflow

```bash
# 1. Set network
proton chain:set proton

# 2. Add private key
proton key:add

# 3. Build contract
npm run build

# 4. Check RAM (WASM requires ~100-200KB)
proton account mycontract

# 5. Buy RAM if needed
proton ram:buy mycontract mycontract 200000 -p mycontract@active

# 6. Deploy
proton contract:set mycontract ./assembly/target

# 7. Initialize
proton action mycontract init '{"owner":"mycontract"}' mycontract
```

---

## Executing Actions

```bash
# Basic syntax
proton action CONTRACT ACTION 'DATA_JSON' AUTHORIZATION

# Authorization format: account or account@permission (defaults to @active)
```

### Examples

```bash
# Token transfer
proton action eosio.token transfer \
  '{"from":"alice","to":"bob","quantity":"1.0000 XPR","memo":"test"}' \
  alice

# Initialize contract
proton action mycontract init '{"owner":"mycontract"}' mycontract

# Vote for block producers
proton action eosio voteproducer \
  '{"voter":"myaccount","proxy":"","producers":["bp1","bp2","bp3","bp4"]}' \
  myaccount

# Update permissions
proton action eosio updateauth '{
  "account":"mycontract",
  "permission":"active",
  "parent":"owner",
  "auth":{
    "threshold":1,
    "keys":[{"key":"PUB_K1_xxx","weight":1}],
    "accounts":[
      {"permission":{"actor":"mycontract","permission":"eosio.code"},"weight":1}
    ],
    "waits":[]
  }
}' mycontract@owner
```

---

## Querying Tables

```bash
# Basic table query
proton table CONTRACT TABLE [SCOPE]

# Default scope is same as contract
proton table eosio.proton usersinfo
proton table eosio.proton usersinfo eosio.proton  # Explicit scope
```

### Query Options

```bash
# Limit rows
proton table mycontract mytable -c 10

# Lower bound (filter by primary key >=)
proton table mycontract mytable -l 100

# Upper bound (filter by primary key <=)
proton table mycontract mytable -u 200

# Exact match (lower = upper)
proton table mycontract mytable -l mykey -u mykey

# Reverse order
proton table mycontract mytable -r

# Use secondary index
proton table mycontract mytable -i 2

# Show RAM payer
proton table mycontract mytable -p
```

### Common Table Queries

```bash
# User profile from eosio.proton
proton table eosio.proton usersinfo -l alice -u alice

# Token balance
proton table eosio.token accounts alice

# Oracle price (BTC/USD = index 4)
proton table oracles data -l 4 -u 4
```

---

## Transactions

```bash
# Execute raw transaction JSON
proton transaction '{"actions":[...]}'

# Get transaction by ID
proton transaction:get TRANSACTION_ID

# Push signed transaction
proton transaction:push SIGNED_TX_JSON

# Push to specific endpoint
proton transaction:push SIGNED_TX_JSON -u https://proton.eosusa.io
```

---

## Code Generation (Boilerplate)

```bash
# Create new project with contract, frontend, tests
proton boilerplate myproject

# Generate new contract
proton generate:contract mycontract

# Add action to contract
proton generate:action

# Add table to contract
proton generate:table mytable

# Add singleton table
proton generate:table myconfig -s

# Add inline action class
proton generate:inlineaction myaction
```

---

## Resource Management

```bash
# Get RAM price
proton ram

# Buy RAM (bytes)
proton ram:buy BUYER RECEIVER BYTES -p BUYER@active

# Example: Buy 150KB for contract
proton ram:buy mycontract mycontract 150000 -p mycontract@active

# List faucets
proton faucet

# Claim from faucet (testnet)
proton faucet:claim XPR myaccount
```

---

## Multisig Operations

```bash
# Create multisig proposal
proton msig:propose myproposal '[{"account":"eosio.token","name":"transfer",...}]' proposer

# Approve proposal
proton msig:approve proposer myproposal approver

# Execute approved proposal
proton msig:exec proposer myproposal executor

# Cancel proposal
proton msig:cancel myproposal proposer
```

---

## Utility Commands

```bash
# Encode account name to u64
proton encode:name myaccount

# Encode token symbol
proton encode:symbol XPR 4

# Open account in Proton Scan
proton scan myaccount

# Create session from Proton Sign Request URI
proton psr "proton://..."

# Get CLI version
proton version

# Get help for any command
proton --help
proton [COMMAND] --help
```

---

## Common Issues & Solutions

### "Key not found" Error

```bash
proton key:list  # Check if key is stored
proton key:add   # Add the key
```

### "Authorization error"

- Check account has correct permissions
- Verify key matches account's active key
- Try explicit permission: `account@active`

### "Transaction failed"

- Check account has enough RAM: `proton account myaccount`
- Check account has enough CPU/NET
- Verify action parameters match ABI

### WebAuthn Keys (PUB_WA_) Cannot Be Used

If an account's active key is WebAuthn (starts with `PUB_WA_`), you cannot sign from CLI. Update permission to use K1 key:

```bash
proton action eosio updateauth '{
  "account":"ACCOUNT",
  "permission":"active",
  "parent":"owner",
  "auth":{
    "threshold":1,
    "keys":[{"key":"PUB_K1_xxx","weight":1}],
    "accounts":[{"permission":{"actor":"ACCOUNT","permission":"eosio.code"},"weight":1}],
    "waits":[]
  }
}' ACCOUNT@owner
```

### RAM Requirements

WASM files require significant RAM. Check before deploying:

```bash
proton account mycontract  # Check available RAM
proton ram                 # Check RAM price
proton ram:buy mycontract mycontract 150000 -p mycontract@active
```

### Misleading Error Messages

Some commands show errors but still succeed. Always check the transaction link in output:
- `"Error: Inline actions already enabled"` may appear on successful deploy

### ram:buy Syntax

Authorization uses `-p` flag, not positional:

```bash
# Correct
proton ram:buy BUYER RECEIVER BYTES -p BUYER@active

# Incorrect (will fail)
proton ram:buy BUYER RECEIVER BYTES BUYER
```

---

## Quick Reference Card

| Task | Command |
|------|---------|
| Set mainnet | `proton chain:set proton` |
| Set testnet | `proton chain:set proton-test` |
| Add key | `proton key:add` |
| Account info | `proton account NAME -t` |
| Deploy contract | `proton contract:set ACCOUNT ./assembly/target` |
| Execute action | `proton action CONTRACT ACTION 'JSON' AUTH` |
| Query table | `proton table CONTRACT TABLE` |
| Buy RAM | `proton ram:buy PAYER RECV BYTES -p PAYER@active` |
| Enable inline | `proton contract:enableinline CONTRACT` |
