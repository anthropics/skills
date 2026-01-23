# Staking, Governance & Resources on XPR Network

This guide covers XPR staking, Block Producer voting, the DPoS consensus mechanism, and XPR Network's unique resource model.

## Overview

XPR Network uses **Delegated Proof of Stake (DPoS)** where token holders stake XPR and vote for Block Producers who validate transactions and produce blocks.

Key differences from other EOSIO chains:
- **Zero gas fees** for regular users
- **Subscription-based resources** for dApps (not stake-based CPU/NET)
- **4 Block Producer minimum** voting requirement
- **24-hour unstaking delay** for security

---

## Staking XPR

### Why Stake?

- **Governance participation** - Vote for Block Producers
- **Earn rewards** - Staking rewards distributed proportionally
- **Security** - 24-hour unstaking delay protects against key compromise

### How to Stake

#### Via Explorer UI

1. Go to https://explorer.xprnetwork.org
2. Login with WebAuth wallet
3. Select **Wallet** → **Short Stake XPR**
4. Go to **Stake** tab
5. Enter amount (or use 25/50/75/100% buttons)
6. Click **Stake** and sign transaction

#### Via CLI

```bash
# Stake XPR
proton action eosio.proton stake '{"owner":"myaccount","amount":"1000.0000 XPR"}' myaccount
```

#### Via Code

```typescript
async function stakeXPR(session: any, amount: string): Promise<any> {
  return session.transact({
    actions: [{
      account: 'eosio.proton',
      name: 'stake',
      authorization: [session.auth],
      data: {
        owner: session.auth.actor,
        amount: amount  // e.g., "1000.0000 XPR"
      }
    }]
  }, { broadcast: true });
}
```

---

## Unstaking XPR

### 24-Hour Security Delay

Unstaking takes **24 hours** to complete. This is a security feature:
- If your keys are compromised, you have 24 hours to use your **owner key** to change your active key before funds can be withdrawn
- The attacker cannot speed up the unstaking process

### How to Unstake

#### Via Explorer UI

1. Select **Wallet** → **Short Stake XPR**
2. Go to **Unstake** tab
3. Enter amount to unstake
4. Click **Unstake** and sign
5. Wait 24 hours
6. Go to **Refund** tab to claim (or it processes automatically)

#### Via CLI

```bash
# Start unstaking
proton action eosio.proton unstake '{"owner":"myaccount","amount":"500.0000 XPR"}' myaccount

# After 24 hours, claim refund (usually automatic)
proton action eosio.proton refund '{"owner":"myaccount"}' myaccount
```

#### Via Code

```typescript
async function unstakeXPR(session: any, amount: string): Promise<any> {
  return session.transact({
    actions: [{
      account: 'eosio.proton',
      name: 'unstake',
      authorization: [session.auth],
      data: {
        owner: session.auth.actor,
        amount: amount
      }
    }]
  }, { broadcast: true });
}

// After 24 hours
async function claimRefund(session: any): Promise<any> {
  return session.transact({
    actions: [{
      account: 'eosio.proton',
      name: 'refund',
      authorization: [session.auth],
      data: {
        owner: session.auth.actor
      }
    }]
  }, { broadcast: true });
}
```

---

## Voting for Block Producers

### About Block Producers

Block Producers (BPs) are the backbone of XPR Network:
- Validate transactions and produce blocks
- Elected via Delegated Proof of Stake (DPoS)
- Only **top 21 BPs** actively produce blocks
- Must operate reliable, secure infrastructure

### Voting Requirements

- **Must have XPR staked** before voting
- **Must vote for at least 4 Block Producers**
- Voting choice does **NOT** affect staking reward amount

### What to Consider

Choose BPs who:
- Run solid, reliable infrastructure
- Contribute to ecosystem development
- Support developers and dApps
- Drive adoption and marketing

### How to Vote

#### Via Explorer UI

1. Stake XPR first (if not already staked)
2. Select **Vote** from top menu
3. View Block Producer list (ranked by votes)
4. Check boxes for **up to 4 BPs**
5. Click blue **VOTE** button
6. Sign transaction

#### Via CLI

```bash
# Vote for block producers (minimum 4)
proton action eosio voteproducer '{"voter":"myaccount","proxy":"","producers":["bp1","bp2","bp3","bp4"]}' myaccount
```

#### Via Code

```typescript
async function voteForProducers(
  session: any,
  producers: string[]  // Must be at least 4
): Promise<any> {
  if (producers.length < 4) {
    throw new Error('Must vote for at least 4 Block Producers');
  }

  // Producers must be sorted alphabetically
  const sortedProducers = [...producers].sort();

  return session.transact({
    actions: [{
      account: 'eosio',
      name: 'voteproducer',
      authorization: [session.auth],
      data: {
        voter: session.auth.actor,
        proxy: '',
        producers: sortedProducers
      }
    }]
  }, { broadcast: true });
}
```

### Query Block Producers

```typescript
async function getBlockProducers(): Promise<any[]> {
  const { rows } = await rpc.get_table_rows({
    code: 'eosio',
    scope: 'eosio',
    table: 'producers',
    limit: 100
  });

  // Sort by total votes
  return rows.sort((a, b) => parseFloat(b.total_votes) - parseFloat(a.total_votes));
}

// Get top 21 (active producers)
const producers = await getBlockProducers();
const activeProducers = producers.slice(0, 21);
```

---

## Claiming Staking Rewards

### Reward Distribution

- Rewards are distributed **automatically and proportionally** based on staked amount
- Can claim once every **24 hours**
- Voting choice does NOT affect reward amount

### How to Claim

#### Via Explorer UI

1. Select **Wallet** → **Short Stake XPR**
2. Go to **Claim Rewards** tab
3. Click **Claim** button
4. Sign transaction

#### Via CLI

```bash
proton action eosio.proton claimrewards '{"owner":"myaccount"}' myaccount
```

#### Via Code

```typescript
async function claimStakingRewards(session: any): Promise<any> {
  return session.transact({
    actions: [{
      account: 'eosio.proton',
      name: 'claimrewards',
      authorization: [session.auth],
      data: {
        owner: session.auth.actor
      }
    }]
  }, { broadcast: true });
}
```

---

## Resource Model

### XPR Network vs EOS/WAX

XPR Network has a **fundamentally different resource model** than other EOSIO chains:

| Feature | XPR Network | EOS / WAX |
|---------|-------------|-----------|
| User Fees | **Zero** for regular users | Users pay CPU/NET |
| CPU/NET Model | Subscription-based for dApps | Stake-based |
| RAM | Purchase with XPR | Purchase with tokens |
| Target Users | Consumer apps | General blockchain |

### Free Resources for Users

Regular users on XPR Network get **free resources** for transactions. This is why XPR is marketed as "gas-free" - end users don't pay transaction fees.

### Subscription Plans for dApps

dApps and developers can purchase **monthly resource subscription plans** at https://resources.xprnetwork.org:

| Plan | Price | CPU Credits | NET Credits | Transactions/Day | Best For |
|------|-------|-------------|-------------|------------------|----------|
| **Basic** | 100 XPR/mo | 100 | 10 | ~500 | Small demo apps |
| **Plus** | 1,000 XPR/mo | 1,000 | 100 | ~5,000 | Games, small apps |
| **Pro** | 10,000 XPR/mo | 10,000 | 1,000 | ~50,000 | Most apps + Priority Support |
| **Enterprise** | 100,000 XPR/mo | 100,000 | 10,000 | ~500,000 | Priority Support + Surge availability |

**Key Details:**
- **CPU is the scarcer resource** - System allocates at 80:20 CPU:NET ratio
- **Upgrade/downgrade anytime** - Remaining time credited toward new plan
- **Battle tested** - Enterprise BOT runs 1M+ transactions daily with steady consumption

### Resource Contract

The `resources` contract manages subscription plans:

```typescript
// Query available plans
async function getResourcePlans(): Promise<any[]> {
  const { rows } = await rpc.get_table_rows({
    code: 'resources',
    scope: 'resources',
    table: 'plans',
    limit: 100
  });
  return rows;
}

// Query account subscription
async function getSubscription(account: string): Promise<any | null> {
  const { rows } = await rpc.get_table_rows({
    code: 'resources',
    scope: 'resources',
    table: 'subscription',
    lower_bound: account,
    upper_bound: account,
    limit: 1
  });
  return rows[0] ?? null;
}
```

### Buying a Resource Plan

```typescript
async function buyResourcePlan(
  session: any,
  planIndex: number,
  quantity: number = 1
): Promise<any> {
  return session.transact({
    actions: [{
      account: 'resources',
      name: 'buyplan',
      authorization: [session.auth],
      data: {
        account: session.auth.actor,
        plan_index: planIndex,
        quantity: quantity
      }
    }]
  }, { broadcast: true });
}
```

---

## RAM (Blockchain Storage)

### About RAM

RAM is used to store data on-chain (table rows, NFTs, tokens, etc.). Unlike CPU/NET:
- RAM must be **purchased** (not subscription-based)
- RAM is a **persistent resource** (data stays until deleted)
- RAM can be **sold back** when no longer needed

### RAM Pricing

| Item | Cost |
|------|------|
| RAM Storage | **0.0022 XPR per byte** |
| Free RAM (WebAuth) | **12,000 unsellable bytes** per account |
| Maximum Purchase | **6 MB** |

**Portal:** https://resources.xprnetwork.org/storage

### Use Cases

- NFT storage
- Marketplace sales data
- Token balances
- On-chain application data

### Buy RAM

#### Via CLI

```bash
# Buy RAM in bytes
proton ram:buy myaccount myaccount 50000

# Or via action
proton action eosio buyrambytes '{"payer":"myaccount","receiver":"myaccount","bytes":50000}' myaccount
```

#### Via Code

```typescript
async function buyRAM(
  session: any,
  bytes: number,
  receiver?: string
): Promise<any> {
  return session.transact({
    actions: [{
      account: 'eosio',
      name: 'buyrambytes',
      authorization: [session.auth],
      data: {
        payer: session.auth.actor,
        receiver: receiver ?? session.auth.actor,
        bytes: bytes
      }
    }]
  }, { broadcast: true });
}
```

### Sell RAM

```typescript
async function sellRAM(session: any, bytes: number): Promise<any> {
  return session.transact({
    actions: [{
      account: 'eosio',
      name: 'sellram',
      authorization: [session.auth],
      data: {
        account: session.auth.actor,
        bytes: bytes
      }
    }]
  }, { broadcast: true });
}
```

### Check RAM Usage

```bash
# Via CLI
proton account myaccount

# Shows RAM quota and usage
```

```typescript
// Via RPC
async function getRAMUsage(account: string): Promise<{
  used: number;
  quota: number;
  available: number;
}> {
  const accountInfo = await rpc.get_account(account);

  return {
    used: accountInfo.ram_usage,
    quota: accountInfo.ram_quota,
    available: accountInfo.ram_quota - accountInfo.ram_usage
  };
}
```

---

## Governance Portal

XPR Network has a governance portal for proposals and voting:

**URL:** https://gov.xprnetwork.org

Features:
- Submit governance proposals
- Vote on active proposals
- View proposal history
- Track governance metrics

---

## Supported Wallets

| Wallet | Type | Platforms | Best For |
|--------|------|-----------|----------|
| **WebAuth** | Mobile/Web | iOS, Android, Web | General users (recommended) |
| **Anchor** | Mobile/Desktop | iOS, Android, Mac, Win, Linux | Advanced users, owner key access |
| **Ledger** | Hardware | Nano X, Nano S | Maximum security |
| **TokenPocket** | Mobile | iOS (TestFlight), Android | Multi-chain users |
| **Scatter** | Desktop | Mac, Windows, Linux | Desktop multi-chain |

---

## Quick Reference

### Staking Commands

```bash
# Stake XPR
proton action eosio.proton stake '{"owner":"ACCOUNT","amount":"1000.0000 XPR"}' ACCOUNT

# Unstake XPR
proton action eosio.proton unstake '{"owner":"ACCOUNT","amount":"500.0000 XPR"}' ACCOUNT

# Claim refund (after 24h)
proton action eosio.proton refund '{"owner":"ACCOUNT"}' ACCOUNT

# Claim rewards
proton action eosio.proton claimrewards '{"owner":"ACCOUNT"}' ACCOUNT

# Vote for BPs (minimum 4)
proton action eosio voteproducer '{"voter":"ACCOUNT","proxy":"","producers":["bp1","bp2","bp3","bp4"]}' ACCOUNT
```

### Key Tables

| Contract | Table | Description |
|----------|-------|-------------|
| `eosio` | `producers` | Block Producer list |
| `eosio` | `voters` | Voter information |
| `eosio` | `global` | Chain parameters |
| `eosio.proton` | `usersinfo` | User profiles |
| `resources` | `plans` | Resource subscription plans |
| `resources` | `subscription` | Active subscriptions |

### Important Links

| Resource | URL |
|----------|-----|
| Explorer (Mainnet) | https://explorer.xprnetwork.org |
| Explorer (Testnet) | https://testnet.explorer.xprnetwork.org |
| Governance Portal | https://gov.xprnetwork.org |
| Resources Portal | https://resources.xprnetwork.org |
| WebAuth Wallet | https://webauth.com |
| Help Desk | https://help.xprnetwork.org |
