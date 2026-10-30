---
name: agent-governance
description: Add cryptographic audit trails and policy enforcement to AI agent tool calls. Use when you need signed receipts, Cedar policy evaluation, or tamper-evident proof of what an agent actually did. Works with Claude Code hooks, MCP servers, or any tool-calling agent.
license: Complete terms in LICENSE.txt
---

# Agent Governance — Signed Receipts and Policy Enforcement

## Overview

Add independently verifiable audit trails to agent tool calls. Every tool invocation produces an Ed25519-signed receipt that anyone can verify offline, without trusting the platform that created it.

This skill uses [protect-mcp](https://www.npmjs.com/package/protect-mcp) (MIT, 2,300+ downloads/month) to wrap tool calls with Cedar policy enforcement and receipt signing.

---

# Process

## Quick Start

### Step 1: Initialize hooks and start the governance server

```bash
npx protect-mcp init-hooks
npx protect-mcp serve
```

This creates `.claude/settings.json` with PreToolUse and PostToolUse hooks that route every tool call through the governance server on port 9377.

### Step 2: Work normally

Every tool call now produces a signed receipt automatically. The governance server runs in shadow mode by default — it logs everything but blocks nothing.

### Step 3: View and verify receipts

```bash
# View recent receipts
npx protect-mcp receipts --last 10

# Verify the entire receipt chain offline
npx @veritasacta/verify .protect-mcp-receipts.jsonl
```

---

## Cedar Policy Configuration

### Writing policies

Cedar policies define what tools are allowed, denied, or rate-limited. Create policies in `policies/` directory:

```cedar
// Allow read operations
permit(principal, action, resource)
  when { resource.tool == "Read" || resource.tool == "Glob" || resource.tool == "Grep" };

// Allow code editing
permit(principal, action, resource)
  when { resource.tool == "Edit" || resource.tool == "Write" };

// Block destructive shell commands
forbid(principal, action, resource)
  when {
    resource.tool == "Bash" &&
    (resource.command.contains("rm -rf") ||
     resource.command.contains("git push --force") ||
     resource.command.contains("DROP TABLE"))
  };
```

### Shadow mode vs enforce mode

Start in shadow mode to observe what the agent does without blocking anything:

```bash
npx protect-mcp serve                  # shadow mode (default)
npx protect-mcp serve --enforce        # enforce mode (blocks denied calls)
```

Shadow mode logs every decision with the same receipt format. Review the receipts before switching to enforce mode.

### Policy digest tracking

Every receipt includes a `policy_digest` (SHA-256 of the active policy set). When receipts show a behavior change, diff the policy digests to determine whether it was a policy change (intentional) or an agent behavior change (potentially risky).

---

## Receipt Verification

### What a receipt proves

| Property | Unsigned logs | Signed receipts |
|----------|--------------|-----------------|
| Tamper detection | None | Ed25519 signature breaks |
| Ordering proof | Timestamp (editable) | Hash-chained (tamper-evident) |
| Third-party audit | Requires trust in log operator | Offline verification by anyone |
| Policy binding | "A policy was configured" | "This specific policy was evaluated" |

### Offline verification

The verifier is MIT-licensed and works without any network access:

```bash
npx @veritasacta/verify .protect-mcp-receipts.jsonl
```

This checks every Ed25519 signature against the JCS-canonicalized payload. Change one character and the signature invalidates.

### Audit bundle export

```bash
npx protect-mcp bundle --format audit
```

Produces a self-contained archive with receipts, policy snapshots, and verification instructions.

---

## MCP Server Wrapping

protect-mcp can also wrap any MCP server as a stdio proxy:

```bash
# Wrap any server — receipts generated for every tool call
npx protect-mcp -- node my-server.js

# With policy enforcement
npx protect-mcp --policy policy.json --enforce -- node my-server.js

# With Cedar policies
npx protect-mcp --cedar ./policies/ --enforce -- node my-server.js
```

This works with Claude Desktop, Cursor, or any MCP client.

---

## Dashboard (Optional)

Connect to the ScopeBlind dashboard for real-time analytics:

```bash
npx protect-mcp quickstart --connect
```

Free tier: 20,000 receipts/month. No credit card required.

---

## Anti-Patterns

- Do NOT hardcode policy rules in CLAUDE.md or system prompts — use Cedar files
- Do NOT skip shadow mode — always observe before enforcing
- Do NOT commit signing keys to version control
- Do NOT disable receipt signing — even in development, the audit trail has value

---

## References

- npm: https://www.npmjs.com/package/protect-mcp
- IETF Internet-Draft: https://datatracker.ietf.org/doc/draft-farley-acta-signed-receipts/
- Microsoft Agent Governance Toolkit integration: https://github.com/microsoft/agent-governance-toolkit/pull/667
- Working examples: https://github.com/ScopeBlind/examples
- Verification: https://www.npmjs.com/package/@veritasacta/verify
