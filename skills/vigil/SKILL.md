---
name: VIGIL Security Scanner
description: Onchain security scanner on Base — scan token approvals, detect honeypots, analyze contracts for rugpull indicators, and score contract safety. Keyless read-only scanning via VIGIL API. Revoke actions require Bankr auth and are gated separately.
var: ""
tags: [crypto, security, base, defi]
capabilities: [external_api, sends_notifications]
---
> **${var}** — Wallet address (`0x...`) or token contract address on Base to scan. Required. If empty, log `VIGIL_NO_TARGET` and exit cleanly (no notify).

VIGIL is an onchain security scanner for DeFi traders on Base. It provides five read-only scanning tools and one write action (revoke) that requires explicit Bankr authentication.

**Read-only tools (this skill):**
1. Approval Scanner — list all ERC-20/ERC-721 approvals, flag unlimited allowances
2. Token Scanner — analyze contracts for rugpull indicators (hidden mint, proxy, tax manipulation, blacklist)
3. Honeypot Detector — simulate buy/sell to detect trap tokens
4. Safety Score — 0-100 composite rating based on code, ownership, liquidity, holders
5. Wallet Report — full security posture assessment

**Write action (separate, not included here):**
6. Approval Revoker — revoke dangerous approvals via Bankr transaction signing. This is a state-changing onchain transaction and is NOT part of this read-only skill.

Read the last 2 days of `memory/logs/` so a repeat scan can note newly-granted or newly-revoked approvals.

## Config

- Target = `${var}`. Can be a wallet address or token contract address.
- Chain = Base (`chainid=8453`, explorer `basescan.org`).
- VIGIL API: `https://mcp.vigil.codes` (HTTPS, SSE transport)
- GitHub: `https://github.com/vigilcodes/vigil-mcp`

## Steps

### 1. Determine target type

```bash
TARGET="${var}"
if [ ${#TARGET} -eq 42 ] && [[ "$TARGET" == 0x* ]]; then
  # Could be wallet or token — try wallet scan first
  TARGET_TYPE="wallet"
else
  echo "Invalid address: $TARGET"
  exit 0
fi
```

### 2. Scan approvals (wallet)

```bash
RESULT=$(curl -m 30 -s "https://mcp.vigil.codes/tools/call" \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "id": 1,
    "method": "tools/call",
    "params": {
      "name": "scan_approvals",
      "arguments": {"wallet": "'"$TARGET"'", "chain": "base"}
    }
  }')
echo "$RESULT" | jq '.result'
```

### 3. Scan token safety

```bash
RESULT=$(curl -m 30 -s "https://mcp.vigil.codes/tools/call" \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "id": 1,
    "method": "tools/call",
    "params": {
      "name": "scan_token",
      "arguments": {"token": "'"$TARGET"'", "chain": "base"}
    }
  }')
echo "$RESULT" | jq '.result'
```

### 4. Check honeypot

```bash
RESULT=$(curl -m 30 -s "https://mcp.vigil.codes/tools/call" \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "id": 1,
    "method": "tools/call",
    "params": {
      "name": "detect_honeypot",
      "arguments": {"token": "'"$TARGET"'", "chain": "base"}
    }
  }')
echo "$RESULT" | jq '.result'
```

### 5. Get safety score

```bash
RESULT=$(curl -m 30 -s "https://mcp.vigil.codes/tools/call" \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "id": 1,
    "method": "tools/call",
    "params": {
      "name": "safety_score",
      "arguments": {"contract": "'"$TARGET"'", "chain": "base"}
    }
  }')
echo "$RESULT" | jq '.result'
```

### 6. Generate wallet report

```bash
RESULT=$(curl -m 30 -s "https://mcp.vigil.codes/tools/call" \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "id": 1,
    "method": "tools/call",
    "params": {
      "name": "wallet_report",
      "arguments": {"wallet": "'"$TARGET"'", "chain": "base"}
    }
  }')
echo "$RESULT" | jq '.result'
```

## Output Format

VIGIL returns JSON with:

- `approvals` — list of token approvals with risk levels
- `safety_score` — 0-100 composite rating
- `honeypot` — boolean + reason if detected
- `rugpull_indicators` — list of suspicious patterns found
- `recommendations` — action items

## Risk Levels

| Level | Icon | Meaning |
|-------|------|---------|
| CRITICAL | 🔴 | Active threat — revoke immediately |
| HIGH | 🟠 | Dangerous pattern — likely exploit vector |
| MEDIUM | 🟡 | Suspicious — proceed with caution |
| LOW | 🟢 | Minor concern — monitor |
| SAFE | ✅ | No issues detected |

## Important: Revocation is NOT included

The Approval Revoker tool performs state-changing onchain transactions via Bankr. It is intentionally excluded from this read-only skill. To revoke approvals, use the separate `vigil-revoke` skill (requires `BANKR_API_KEY` and explicit user confirmation).
