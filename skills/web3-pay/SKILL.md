---
name: web3-pay
description: Accept crypto payments (USDC) on Base, Polygon, Ethereum, and Arbitrum. Verify on-chain transactions, manage paid users, and track subscriptions.
---

# Web3 Pay

Accept cryptocurrency payments and manage user subscriptions through on-chain USDC transfers.

## When to Use

- User wants to pay for a service or subscription
- Need to verify a crypto payment transaction
- Managing paid user access (grant, check, revoke)
- Checking recent transfers to a wallet

## Setup

Set environment variables:
```bash
export WEB3PAY_ADDRESS=0xYourWalletAddress
export WEB3PAY_CHAIN=base  # base | polygon | ethereum | arbitrum
export BASESCAN_API_KEY=your_key  # optional, for better rate limits
```

## Commands

```bash
# Show payment info (address, plans, chain)
python3 web3pay.py info --address 0x... --chain base

# Verify a transaction
python3 web3pay.py verify --tx 0xTransactionHash --address 0x...

# Get recent USDC transfers to address
python3 web3pay.py transfers --address 0x...

# Grant access to a user
python3 web3pay.py grant --user user123 --plan monthly --tx 0x...

# Check if user has access
python3 web3pay.py check --user user123

# Revoke access
python3 web3pay.py revoke --user user123

# List all paid users
python3 web3pay.py list
```

## Payment Flow

1. User requests to subscribe → Show wallet address + pricing
2. User sends USDC on Base/Polygon/ETH → Gets transaction hash
3. Verify transaction → `verify --tx 0x...` confirms the transfer
4. Grant access → `grant --user X --plan monthly`

## Supported Chains

| Chain | Gas Cost | Best For |
|-------|----------|----------|
| Base | ~$0.01 | Recommended - cheapest |
| Polygon | ~$0.01 | Alternative cheap option |
| Arbitrum | ~$0.05 | Ethereum L2 |
| Ethereum | $1-5 | High-value only |

## Default Plans

- `monthly`: 10 USDC (30 days)
- `yearly`: 50 USDC (365 days)
- `lifetime`: 100 USDC (forever)

## Source

https://github.com/BENZEMA216/clawdbot-skill-web3-pay
