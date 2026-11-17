# CRITICAL: Smart Contract Safety Guidelines

This document contains **critical safety rules** for XPR Network smart contract development. Violating these rules can make your data unreadable.

---

## AI-Generated Code Disclaimer

> **Smart contracts are immutable and handle real assets. AI-generated code requires human review before deployment.**

When using Claude or any AI assistant for smart contract development:

1. **Always review generated code** - AI can produce functional but suboptimal or insecure code
2. **Test on testnet first** - Never deploy untested code to mainnet
3. **Understand what the code does** - Don't deploy code you can't explain
4. **Get a second opinion** - Have another developer review critical contracts
5. **Consider professional audits** - For contracts handling significant value

Claude accelerates development but does not replace:
- Code review by experienced developers
- Comprehensive testing
- Security audits for production contracts

---

## The Golden Rule

> **NEVER modify existing table structures once deployed with data.**

This rule applies to ALL XPR Network / EOSIO smart contracts. Breaking this rule will make your existing data unreadable.

---

## Why This Matters: Real Incident (January 2026)

### What Happened

We attempted to add a `parent_id` field to an existing `posts` table for a replies feature:

```typescript
// WRONG - DO NOT DO THIS
@table("posts")
export class Post extends Table {
  // ... existing fields ...
  public is_deleted: bool = false,
  public parent_id: u64 = 0  // ← Added field BREAKS existing data
}
```

### The Result

**All 9 posts became unreadable** with this error:

```
"Stream unexpectedly ended; unable to unpack field 'parent_id' of struct 'Post'"
```

### Why It Broke

EOSIO stores table data as **raw binary bytes**, not JSON. The ABI defines how to deserialize those bytes:

```
Existing data on-chain (per row):
[id:8][author:8][content:var][image_url:var][timestamp:8][is_pinned:1][pin_expires:8][is_deleted:1]

New ABI expected:
[id:8][author:8][content:var][image_url:var][timestamp:8][is_pinned:1][pin_expires:8][is_deleted:1][parent_id:8]
                                                                                                    ↑ Missing!
```

The deserializer tries to read 8 more bytes that don't exist → **crash**.

### Recovery

**The data was never deleted!** Only the ABI (decoder) was wrong.

1. Removed `parent_id` from table definition
2. Rebuilt contract (`npm run build`)
3. Redeployed contract with old ABI
4. All 9 posts immediately readable again

---

## What You Cannot Do to Existing Tables

| Action | Result |
|--------|--------|
| Add a field | ❌ Breaks deserialization |
| Remove a field | ❌ Breaks deserialization |
| Change field order | ❌ Breaks deserialization |
| Change field type | ❌ Breaks deserialization |
| Rename a field | ❌ Breaks deserialization (ABI mismatch) |

---

## Safe Patterns for New Features

### Pattern 1: Create NEW Tables (Recommended)

```typescript
// SAFE - New table doesn't affect existing data
@table("replies")
export class Reply extends Table {
  constructor(
    public id: u64 = 0,
    public parent_id: u64 = 0,  // Links to posts.id
    public author: Name = new Name(),
    public content: string = "",
    public timestamp: u64 = 0,
    public is_deleted: bool = false
  ) { super(); }

  @primary
  get primary(): u64 { return this.id; }
}
```

This is the safest approach:
- Existing `posts` table unchanged
- New `replies` table for new feature
- Zero risk to existing data

### Pattern 2: New Singleton for New Config

```typescript
// SAFE - New singleton for reply-specific config
@table("replyconf", singleton)
export class ReplyConfig extends Table {
  constructor(
    public next_reply_id: u64 = 0
  ) { super(); }
}
```

Don't modify existing `config` singleton; create a new one.

### Pattern 3: New Contract Entirely

For major features, deploy to a new contract account:

```bash
# Create new account for new feature
proton account:create newfeature

# Deploy separate contract
proton contract:set newfeature ./assembly/target
```

Benefits:
- Zero risk to existing contract/data
- Clean separation of concerns
- Easy to rollback by just not using it
- Can interact with original contract via inline actions

### Pattern 4: Migration Action (Advanced/Risky)

```typescript
@action("migrate")
migrate(limit: u8): void {
  requireAuth(this.receiver);

  // Read from old table
  let cursor = this.oldTable.first();
  let count: u8 = 0;

  while (cursor && count < limit) {
    // Create new row with new schema
    const newRow = new NewPost(
      cursor.id,
      cursor.author,
      cursor.content,
      // ... copy fields
      0  // new field default
    );

    // Store in new table
    this.newTable.store(newRow, this.receiver);

    // Delete from old table
    const toDelete = cursor;
    cursor = this.oldTable.next(cursor);
    this.oldTable.remove(toDelete);

    count++;
  }
}
```

**Risks**:
- Requires extensive testing
- Partial migration can leave data in inconsistent state
- RAM costs for duplicate data during migration
- Transaction limits may require multiple migration calls

---

## Pre-Deployment Checklist

Before deploying ANY contract update:

### 1. Check if Tables Have Data

```bash
curl -s -X POST https://proton.eosusa.io/v1/chain/get_table_rows \
  -H "Content-Type: application/json" \
  -d '{"code":"CONTRACT","scope":"CONTRACT","table":"TABLE","limit":1}'
```

If `rows` is not empty, **DO NOT modify that table's schema**.

### 2. Verify Schema Changes

Compare old and new table definitions:

```bash
# Get current ABI
proton contract:abi mycontract > old.abi

# After build, compare
diff old.abi ./assembly/target/mycontract.abi
```

### 3. Test on Testnet First

```bash
# Switch to testnet
proton chain:set proton-test

# Deploy to testnet account
proton contract:set mycontract-test ./assembly/target

# Test thoroughly before mainnet
```

### 4. Back Up Current ABI

```bash
proton contract:abi mycontract > backup-$(date +%Y%m%d).abi
```

### 5. Verify Target Account

**CRITICAL**: We often have multiple contracts. Wrong account = overwrite:

```bash
# Verify you're in the correct directory
pwd
# Should show: /correct/project/path

# Verify target account
proton account mycontract

# Double-check the command before running!
proton contract:set mycontract ./assembly/target
#                   ^^^^^^^^^^
#                   IS THIS CORRECT?
```

---

## Multi-Contract Account Safety

If you manage multiple contracts, maintain a clear mapping:

| Account | Contract | Purpose |
|---------|----------|---------|
| `myapp` | Main app | Core logic |
| `myapptoken` | Token | Custom token |
| `myappnft` | NFTs | Collection |
| `myappgame` | Game | Gameplay |

**Before EVERY deployment**:
1. Check `pwd` - am I in the right project?
2. Check the account name in the deploy command
3. Never copy-paste without verifying

---

## Recovery Options

### Option 1: Rollback ABI (Fastest)

If you broke deserialization:

```bash
# Remove the new field from code
# Rebuild
npm run build

# Redeploy (restores old ABI)
proton contract:set mycontract ./assembly/target
```

Data becomes readable again immediately.

### Option 2: Rebuild from Transaction History

All actions are recorded forever on-chain. Query with Hyperion:

```bash
curl -s "https://proton.eosusa.io/v2/history/get_actions" \
  -H "Content-Type: application/json" \
  -d '{"account":"mycontract","limit":100}' | jq '.actions[]'
```

Every action that created table rows can be replayed to rebuild data.

### Option 3: Read Raw Binary

For advanced recovery, you can read the raw binary and manually parse:

```typescript
const { rows } = await rpc.get_table_rows({
  code: 'mycontract',
  scope: 'mycontract',
  table: 'mytable',
  json: false,  // Return binary
  limit: 100
});

// Manually deserialize using old schema knowledge
```

---

## Key Insight

> The blockchain is immutable. Data stored on-chain cannot be deleted or corrupted by a bad deploy. Only the ABI (interpretation layer) can break. Rolling back the ABI restores access.

This is actually a **safety feature** - your data survives developer mistakes!

---

## Summary

| Do This | Don't Do This |
|---------|---------------|
| Create new tables for new features | Modify existing table schemas |
| Create new singletons for new config | Add fields to existing singletons |
| Test on testnet first | Deploy schema changes directly to mainnet |
| Back up ABI before deploying | Assume you can always recover |
| Verify target account twice | Copy-paste deploy commands blindly |
| Check if tables have data | Assume empty tables |

---

## Quick Reference: Safe Changes

| Change | Safe? |
|--------|-------|
| Add new action | ✅ Safe |
| Modify action logic | ✅ Safe |
| Add new table | ✅ Safe |
| Add new singleton | ✅ Safe |
| Change existing table schema | ❌ **DANGEROUS** |
| Add field to existing table | ❌ **DANGEROUS** |
| Remove field from existing table | ❌ **DANGEROUS** |

When in doubt, create a NEW table.
