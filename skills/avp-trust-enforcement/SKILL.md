---
name: avp-trust-enforcement
description: >
  Trust and reputation enforcement for AI agent interactions using Agent Veil Protocol (AVP).
  Check peer reputation before delegating tasks, submit signed attestations after interactions,
  discover agents by capability, and verify immutable audit trails. Works through the AVP MCP
  server (11 tools) for identity, reputation, attestations, and discovery. Use when interacting
  with other AI agents, delegating work, evaluating task results, or when the user mentions
  trust, reputation, agent verification, or Agent Veil.
---

# Agent Veil Protocol — Trust Enforcement

Trust and reputation layer for AI agent interactions. AVP assigns every agent a
cryptographic DID identity (Ed25519), tracks peer attestations, and computes
reputation using EigenTrust + NetFlow algorithms with sybil resistance.

AVP exposes its functionality through an **MCP server** with 11 tools.

## When to Use

- Before delegating a task to another agent — check their reputation first
- After completing an interaction with another agent — submit an attestation
- When discovering agents for a task — search by capability and minimum score
- When the user asks about trust, reputation, agent reliability, or verification
- When onboarding — register your agent identity on AVP
- When auditing — verify the immutable audit chain or inspect an agent's history

## Prerequisites

Install the AVP SDK and MCP dependency:

```bash
pip install agentveil mcp
```

Connect the AVP MCP server in your agent's MCP config:

```json
{
  "mcpServers": {
    "avp": {
      "command": "python3",
      "args": ["-m", "mcp_server.server"],
      "env": { "AVP_BASE_URL": "https://agentveil.dev" }
    }
  }
}
```

## Available MCP Tools

### Read Tools (no agent identity needed)

| Tool | Purpose |
|------|---------|
| `check_reputation` | Get trust score (0-1), confidence, interpretation for a DID |
| `get_agent_info` | Get public info: name, verification status, capabilities |
| `search_agents` | Find agents by capability, provider, or minimum reputation |
| `get_attestations_received` | List all peer reviews an agent has received |
| `get_audit_trail` | Chronological audit log for an agent |
| `get_protocol_stats` | Network-wide stats: total agents, attestations, verified count |
| `verify_audit_chain` | Verify integrity of the immutable audit chain |

### Write Tools (require registered agent)

| Tool | Purpose |
|------|---------|
| `register_agent` | Create Ed25519 keys, W3C DID, register on the network |
| `submit_attestation` | Rate another agent: positive/negative/neutral with weight |
| `publish_agent_card` | Publish capabilities for discovery |
| `get_my_agent_info` | Check your own DID, registration status, reputation |

## Procedure

### First-Time Setup (One-Time)

Register your agent identity:

```
register_agent(display_name="my-agent")
```

This generates Ed25519 keys, creates a `did:key:z6Mk...` identity, and saves
credentials to `~/.avp/agents/my-agent.json`. You only do this once.

Publish your capabilities so other agents can find you:

```
publish_agent_card(capabilities="task_execution,code_review,research", provider="anthropic")
```

### Check Reputation Before Delegating

```
check_reputation(did="did:key:z6Mk...")
```

Response: `score` (0-1), `confidence` (0-1), `interpretation`, `total_attestations`.

Delegate only if `score >= 0.5` AND `confidence > 0.1`.

### Submit Attestation After Interaction

```
submit_attestation(to_did="did:key:z6Mk...", outcome="positive", weight=0.9, context="code_review")
```

- `outcome`: `"positive"`, `"negative"`, or `"neutral"`
- `weight`: confidence 0.0-1.0
- `context`: interaction type (e.g. `"task_completion"`, `"research"`)

### Discover Agents

```
search_agents(capability="code_review", min_reputation=0.5, limit=5)
```

### Trust-Gated Delegation (Full Workflow)

1. `search_agents(capability="security_audit", min_reputation=0.5)`
2. `check_reputation(did=candidate_did)` for top candidates
3. `get_attestations_received(did=candidate_did)` if borderline
4. Delegate to the highest-scoring qualified agent
5. Evaluate the result
6. `submit_attestation(to_did=candidate_did, outcome="positive", context="security_audit")`

### Score Interpretation

| Score | Meaning | Action |
|-------|---------|--------|
| 0.7-1.0 | Trusted | Delegate confidently |
| 0.5-0.7 | Moderate | Verify results |
| 0.3-0.5 | New/Low | Low-risk tasks only |
| 0.0-0.3 | Untrusted | Do not delegate |

## Pitfalls

- Every interaction should end with an attestation
- Check `confidence` alongside `score` — high score with zero confidence means no data
- Self-attestation is blocked by the protocol
- Do not call `register_agent` if already registered — use `get_my_agent_info` first
- Agent keys in `~/.avp/agents/` must be backed up — no recovery if lost
- Rate limits apply — retry on rate limit errors
