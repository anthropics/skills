---
name: agentpay-mcp
description: Add payment capabilities to Claude agents. Create non-custodial wallets, send/receive payments, check balances, and settle tasks between agents using the AgentPay MCP server. Use when an agent needs to handle money, pay for services, or participate in agent-to-agent commerce.
license: MIT
---

# AgentPay MCP - Payment Skill for Claude Agents

## Overview

Give Claude agents the ability to handle payments autonomously. AgentPay MCP is an MCP server that provides non-custodial wallet management, payment sending/receiving, balance checking, and inter-agent settlement.

Use this skill when:
- An agent needs to pay for an API, service, or data feed
- Agents need to settle payments between each other (task completion, bounties)
- An agent needs to manage its own wallet and check balances
- Building agent commerce workflows where agents transact autonomously

---

# Setup

## Installation

```bash
npm install -g agentpay-mcp
```

## MCP Configuration

Add to your Claude MCP settings:

```json
{
  "mcpServers": {
    "agentpay": {
      "command": "npx",
      "args": ["agentpay-mcp"],
      "env": {
        "AGENT_WALLET_PRIVATE_KEY": "your-wallet-private-key",
        "PAYMENT_NETWORK": "base-sepolia"
      }
    }
  }
}
```

Supported networks: `base`, `base-sepolia`, `ethereum`, `solana`

---

# Available Tools

## Wallet Management

- **create_wallet** - Generate a new non-custodial wallet for the agent
- **get_balance** - Check wallet balance across supported tokens
- **get_address** - Return the agent's wallet address

## Payments

- **send_payment** - Send tokens to another address or agent
- **request_payment** - Create a payment request for services rendered
- **check_payment_status** - Verify if a payment was received

## Task Settlement

- **settle_task** - Complete payment for a finished task between agents
- **escrow_funds** - Lock funds for a pending task agreement

---

# Usage Patterns

## Pay for an API call

When an agent needs to access a paid API:
1. Check balance with `get_balance`
2. If sufficient funds, call `send_payment` with the API provider's address and the required amount
3. Include the transaction hash in the API request as proof of payment

## Agent-to-agent task settlement

When one agent completes work for another:
1. Requesting agent calls `escrow_funds` with task details and payment amount
2. Working agent completes the task
3. Either party calls `settle_task` to release escrowed funds to the worker

## Balance management

Before committing to any paid operation:
1. Always call `get_balance` first
2. If balance is insufficient, inform the user with the shortfall amount
3. Never attempt a payment that exceeds the available balance

---

# Security Notes

- Private keys are stored locally and never transmitted to external services
- All transactions require explicit agent action (no automatic spending)
- Use testnets (base-sepolia) for development and testing
- Set spending limits in your agent configuration to prevent runaway costs

---

# Links

- Repository: https://github.com/AI-Agent-Economy/agentpay-mcp
- npm: https://www.npmjs.com/package/agentpay-mcp
- Agent Wallet SDK: https://github.com/AI-Agent-Economy/agentwallet-sdk
