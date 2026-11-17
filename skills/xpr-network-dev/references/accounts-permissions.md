# Accounts and Permissions on XPR Network

This guide covers account creation, permission management, and multisig operations on XPR Network.

## Account Basics

### Account Name Rules

| Rule | Description |
|------|-------------|
| Length | 1-12 characters |
| Characters | Lowercase a-z and digits 1-5 only |
| No dots | Unlike EOS, XPR accounts cannot contain dots |
| No uppercase | Must be entirely lowercase |

Valid: `alice`, `mycontract`, `game123`, `x`
Invalid: `Alice`, `my.contract`, `game_123`, `user@home`

### Account Structure

Every account has:
- **owner** permission - Highest authority, can change all permissions
- **active** permission - Standard transaction signing
- Custom permissions (optional) - Limited access for specific actions

```
Account: mycontract
├── owner (threshold: 1)
│   └── PUB_K1_owner_key (weight: 1)
└── active (threshold: 1)
    ├── PUB_K1_active_key (weight: 1)
    └── mycontract@eosio.code (weight: 1)  ← For inline actions
```

---

## Creating Accounts

### Via CLI

```bash
# Create new account (requires existing account to pay)
proton account:create newaccount

# Create with specific key
proton account:create newaccount --key PUB_K1_xxxxx

# Create on testnet
proton chain:set proton-test
proton account:create testaccount
```

### Via Transaction

```typescript
// Create account programmatically
const actions = [{
  account: 'eosio',
  name: 'newaccount',
  authorization: [{ actor: creator, permission: 'active' }],
  data: {
    creator: creator,
    name: 'newaccount',
    owner: {
      threshold: 1,
      keys: [{ key: 'PUB_K1_xxxxx', weight: 1 }],
      accounts: [],
      waits: []
    },
    active: {
      threshold: 1,
      keys: [{ key: 'PUB_K1_xxxxx', weight: 1 }],
      accounts: [],
      waits: []
    }
  }
},
{
  account: 'eosio',
  name: 'buyrambytes',
  authorization: [{ actor: creator, permission: 'active' }],
  data: {
    payer: creator,
    receiver: 'newaccount',
    bytes: 8192  // Initial RAM
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### Free Account Creation

On mainnet, accounts can be created free through:
- WebAuth wallet (automatic)
- Proton Resources portal

On testnet:
```bash
proton faucet:claim XPR newaccount
```

---

## Permission Management

### View Account Permissions

```bash
proton account myaccount
```

Output shows:
```
permissions:
     owner     1:    1 PUB_K1_xxxxx
        active     1:    1 PUB_K1_yyyyy
```

### Update Permission (Add Key)

```bash
proton action eosio updateauth '{
  "account": "myaccount",
  "permission": "active",
  "parent": "owner",
  "auth": {
    "threshold": 1,
    "keys": [
      {"key": "PUB_K1_newkey", "weight": 1}
    ],
    "accounts": [],
    "waits": []
  }
}' myaccount@owner
```

### Enable Inline Actions for Contract

For a contract to send inline actions, it needs `eosio.code` permission:

```bash
proton action eosio updateauth '{
  "account": "mycontract",
  "permission": "active",
  "parent": "owner",
  "auth": {
    "threshold": 1,
    "keys": [
      {"key": "PUB_K1_contractkey", "weight": 1}
    ],
    "accounts": [
      {"permission": {"actor": "mycontract", "permission": "eosio.code"}, "weight": 1}
    ],
    "waits": []
  }
}' mycontract@owner
```

### Create Custom Permission

```bash
# Create 'minter' permission under 'active'
proton action eosio updateauth '{
  "account": "myaccount",
  "permission": "minter",
  "parent": "active",
  "auth": {
    "threshold": 1,
    "keys": [
      {"key": "PUB_K1_minterkey", "weight": 1}
    ],
    "accounts": [],
    "waits": []
  }
}' myaccount@owner

# Link permission to specific action
proton action eosio linkauth '{
  "account": "myaccount",
  "code": "atomicassets",
  "type": "mintasset",
  "requirement": "minter"
}' myaccount@owner
```

Now signing with the `minter` key only allows calling `atomicassets::mintasset`.

### Delete Permission

```bash
proton action eosio deleteauth '{
  "account": "myaccount",
  "permission": "minter"
}' myaccount@owner
```

### Unlink Permission

```bash
proton action eosio unlinkauth '{
  "account": "myaccount",
  "code": "atomicassets",
  "type": "mintasset"
}' myaccount@owner
```

---

## Multisig (Multi-Signature)

Multisig requires multiple parties to approve a transaction.

### Create Multisig Account

2-of-3 multisig:

```bash
proton action eosio updateauth '{
  "account": "multisig",
  "permission": "active",
  "parent": "owner",
  "auth": {
    "threshold": 2,
    "keys": [],
    "accounts": [
      {"permission": {"actor": "alice", "permission": "active"}, "weight": 1},
      {"permission": {"actor": "bob", "permission": "active"}, "weight": 1},
      {"permission": {"actor": "charlie", "permission": "active"}, "weight": 1}
    ],
    "waits": []
  }
}' multisig@owner
```

### Propose Multisig Transaction

```bash
# Create proposal
proton msig:propose myproposal '{
  "actions": [{
    "account": "eosio.token",
    "name": "transfer",
    "authorization": [{"actor": "multisig", "permission": "active"}],
    "data": {
      "from": "multisig",
      "to": "recipient",
      "quantity": "100.0000 XPR",
      "memo": "Approved payment"
    }
  }]
}' proposer
```

### Approve Proposal

```bash
# Alice approves
proton msig:approve proposer myproposal alice

# Bob approves
proton msig:approve proposer myproposal bob
```

### Execute Proposal

Once threshold is met:

```bash
proton msig:exec proposer myproposal executor
```

### Cancel Proposal

```bash
proton msig:cancel myproposal proposer
```

### Programmatic Multisig

```typescript
// Propose
const proposeActions = [{
  account: 'eosio.msig',
  name: 'propose',
  authorization: [{ actor: proposer, permission: 'active' }],
  data: {
    proposer: proposer,
    proposal_name: 'myprop',
    requested: [
      { actor: 'alice', permission: 'active' },
      { actor: 'bob', permission: 'active' }
    ],
    trx: {
      expiration: '2025-12-31T23:59:59',
      ref_block_num: 0,
      ref_block_prefix: 0,
      max_net_usage_words: 0,
      max_cpu_usage_ms: 0,
      delay_sec: 0,
      context_free_actions: [],
      actions: [/* the proposed actions */],
      transaction_extensions: []
    }
  }
}];

// Approve
const approveActions = [{
  account: 'eosio.msig',
  name: 'approve',
  authorization: [{ actor: approver, permission: 'active' }],
  data: {
    proposer: proposer,
    proposal_name: 'myprop',
    level: { actor: approver, permission: 'active' }
  }
}];

// Execute
const execActions = [{
  account: 'eosio.msig',
  name: 'exec',
  authorization: [{ actor: executor, permission: 'active' }],
  data: {
    proposer: proposer,
    proposal_name: 'myprop',
    executer: executor
  }
}];
```

---

## Time-Delayed Permissions

Add a time delay before permission can be used:

```bash
proton action eosio updateauth '{
  "account": "myaccount",
  "permission": "delayed",
  "parent": "active",
  "auth": {
    "threshold": 1,
    "keys": [
      {"key": "PUB_K1_delayedkey", "weight": 1}
    ],
    "accounts": [],
    "waits": [
      {"wait_sec": 86400, "weight": 1}
    ]
  }
}' myaccount@owner
```

This requires a 24-hour delay before the key can authorize transactions.

---

## Key Types

### K1 Keys (Standard)

Standard secp256k1 keys:
```
Private: PVT_K1_xxxxx
Public:  PUB_K1_xxxxx
```

Generated with:
```bash
proton key:generate
```

### WebAuthn Keys

Hardware-backed keys (Face ID, fingerprint, security keys):
```
Public: PUB_WA_xxxxx
```

Cannot be used from CLI - only through WebAuth wallet.

### R1 Keys

secp256r1 keys (less common):
```
Private: PVT_R1_xxxxx
Public:  PUB_R1_xxxxx
```

---

## Common Permission Patterns

### Contract Admin Pattern

```typescript
// In contract
@table("config", singleton)
class Config extends Table {
  constructor(
    public owner: Name = new Name(),
    public admins: Name[] = []
  ) { super(); }
}

function isAdmin(account: Name): boolean {
  const config = this.configSingleton.get();
  if (account == config.owner) return true;
  return config.admins.includes(account);
}

@action("adminaction")
adminAction(admin: Name): void {
  requireAuth(admin);
  check(this.isAdmin(admin), "Not an admin");
  // ... admin logic
}

@action("addadmin")
addAdmin(newAdmin: Name): void {
  const config = this.configSingleton.get();
  requireAuth(config.owner);  // Only owner can add admins

  if (!config.admins.includes(newAdmin)) {
    config.admins.push(newAdmin);
    this.configSingleton.set(config, this.receiver);
  }
}
```

### Tiered Permissions

```
Account: myapp
├── owner (cold storage, rarely used)
├── active (standard operations)
├── admin (config changes)
│   └── Linked to: myapp::setconfig, myapp::pause
├── operator (daily operations)
│   └── Linked to: myapp::process, myapp::update
└── minter (limited NFT minting)
    └── Linked to: atomicassets::mintasset
```

### Recovery Pattern

```bash
# Owner can always recover by updating active
proton action eosio updateauth '{
  "account": "myaccount",
  "permission": "active",
  "parent": "owner",
  "auth": {
    "threshold": 1,
    "keys": [{"key": "PUB_K1_newkey", "weight": 1}],
    "accounts": [],
    "waits": []
  }
}' myaccount@owner
```

---

## Security Best Practices

### Key Separation

| Key | Use | Storage |
|-----|-----|---------|
| Owner | Emergency recovery only | Cold storage (hardware wallet) |
| Active | Standard operations | Hot wallet with strong security |
| Custom | Limited operations | Can be on server for automation |

### Never Share Owner Key

The owner key should be:
- Generated offline
- Stored in multiple secure locations
- Never used for routine operations
- Used only to recover active key if compromised

### Use Permission Linking

Instead of giving a key full `active` permission, link it to specific actions:

```bash
# Create limited permission
proton action eosio updateauth '{
  "account": "mybot",
  "permission": "resolver",
  "parent": "active",
  "auth": {"threshold":1,"keys":[{"key":"PUB_K1_botkey","weight":1}],"accounts":[],"waits":[]}
}' mybot@owner

# Only allow calling resolve action
proton action eosio linkauth '{
  "account": "mybot",
  "code": "pricebattle",
  "type": "resolve",
  "requirement": "resolver"
}' mybot@owner
```

If the bot key is compromised, attacker can only call `resolve`, not transfer funds.

### Rotate Keys Regularly

```bash
# Generate new key
proton key:generate

# Update active permission
proton action eosio updateauth '{
  "account": "myaccount",
  "permission": "active",
  "parent": "owner",
  "auth": {"threshold":1,"keys":[{"key":"PUB_K1_newkey","weight":1}],"accounts":[],"waits":[]}
}' myaccount@owner

# Remove old key from storage
proton key:remove PVT_K1_oldkey
```

---

## Quick Reference

### CLI Commands

| Command | Description |
|---------|-------------|
| `proton account NAME` | View account info |
| `proton account:create NAME` | Create new account |
| `proton key:generate` | Generate new key pair |
| `proton key:add` | Add key to local storage |
| `proton key:list` | List stored keys |
| `proton msig:propose` | Create multisig proposal |
| `proton msig:approve` | Approve proposal |
| `proton msig:exec` | Execute approved proposal |

### Permission Hierarchy

```
owner (highest)
  └── active (standard)
        └── custom permissions (limited)
```

Child permissions cannot exceed parent's authority.
