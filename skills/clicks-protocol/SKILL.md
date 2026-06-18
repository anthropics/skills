---
name: clicks-protocol
description: Integrate autonomous USDC yield into AI agent projects on Base. Use when building agents that hold, earn, or transfer USDC, when asked about agent treasury management, DeFi yield for agents, x402 payment optimization, or idle USDC strategies.
---

# Clicks Protocol

Add autonomous yield to any AI agent that holds USDC on Base. 80% stays liquid for operations, 20% earns variable yield via Aave V3 or Morpho. Non-custodial, no lockup, withdraw anytime.

## Before Starting

Fetch the latest protocol info:

```
https://clicksprotocol.xyz/llms.txt
```

## Quick Reference

| Detail | Value |
|--------|-------|
| Chain | Base (Coinbase L2, Chain ID 8453) |
| Asset | USDC |
| Split | 80% liquid / 20% yield |
| Yield Source | Aave V3 or Morpho on Base |
| Fee | 2% on yield only, never on principal |
| Lockup | None |
| License | MIT |

## Installation

```bash
npm install @clicks-protocol/sdk ethers@^6
```

## SDK Integration

```typescript
import { ClicksClient } from '@clicks-protocol/sdk';
import { ethers } from 'ethers';

const provider = new ethers.JsonRpcProvider('https://mainnet.base.org');
const signer = new ethers.Wallet(process.env.AGENT_PRIVATE_KEY, provider);
const clicks = new ClicksClient(signer);

// Deposit 1000 USDC (register + approve + split in one call)
const result = await clicks.quickStart('1000', signer.address);
// Result: 800 USDC liquid, 200 USDC earning yield

// Check balance
const info = await clicks.getAgentInfo(signer.address);
const balance = await clicks.getAgentYieldBalance(signer.address);

// Withdraw anytime
await clicks.withdrawYield(signer.address);
```

## Recurring Payments

```typescript
async function onPaymentReceived(amount: string) {
  await clicks.receivePayment(amount, agentAddress);
  // Automatically splits 80/20
}
```

## SDK Methods

| Method | Purpose |
|--------|---------|
| `quickStart(amount, agent, referrer?)` | Register + approve + deposit |
| `receivePayment(amount, agent)` | Split incoming USDC 80/20 |
| `withdrawYield(agent)` | Withdraw principal + yield |
| `getAgentInfo(agent)` | Registration, deposits, yield pct |
| `getAgentYieldBalance(agent)` | Current value and earned yield |
| `getYieldInfo()` | Protocol APYs and totals |
| `simulateSplit(amount, agent)` | Preview split |
| `setOperatorYieldPct(pct)` | Adjust yield 5-50% |

## MCP Server

```bash
npx @clicks-protocol/mcp-server
```

9 tools for read and write treasury operations. See `references/mcp-config.md`.

## x402 Compatibility

Clicks works with Coinbase x402 payments. 80% stays liquid for x402, 20% earns yield. Both on Base, no bridging.

## Contracts (Base Mainnet, Verified)

| Contract | Address |
|----------|---------|
| ClicksRegistry | `0x23bb0Ea69b2BD2e527D5DbA6093155A6E1D0C0a3` |
| ClicksSplitterV3 | `0xc96C1a566a8ed7A39040a34927fEe952bAB8Ad1D` |
| ClicksYieldRouter | `0x053167a233d18E05Bc65a8d5F3F8808782a3EECD` |
| ClicksFee | `0xc47B162D3c456B6C56a3cE6EE89A828CFd34E6bE` |

## Agent Referral System

Agents refer other agents and earn from the protocol fee:

```typescript
await clicks.quickStart('1000', agentAddress, referrerAddress);
```

- L1: 40% of 2% fee | L2: 20% | L3: 10%
- Team tiers: Bronze ($50k) to Diamond ($5M)

## Security

- Immutable contracts (no proxy, no admin upgrade)
- ReentrancyGuard on all state-changing functions
- 58/58 tests passing
- Non-custodial, fee only on yield

## Resources

- Docs: https://clicksprotocol.xyz/docs/getting-started
- SDK: https://www.npmjs.com/package/@clicks-protocol/sdk
- MCP: https://www.npmjs.com/package/@clicks-protocol/mcp-server
- GitHub: https://github.com/clicks-protocol
- Protocol: https://clicksprotocol.xyz/llms.txt
