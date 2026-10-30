# VIGIL API Reference

## Endpoint

**Base URL:** `https://mcp.vigil.codes`

### Health Check

```
GET /health
```

Response:
```json
{"status": "ok", "service": "vigil-mcp", "tools": 10}
```

### List Tools

```
GET /tools/list
```

### Call Tool

```
POST /tools/call
Content-Type: application/json

{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "tools/call",
  "params": {
    "name": "tool_name",
    "arguments": { ... }
  }
}
```

## Available Tools

| Tool | Arguments | Description |
|------|-----------|-------------|
| `vigil_scan_approvals` | `wallet`, `chain` | Scan wallet approvals |
| `vigil_scan_token` | `token`, `chain` | Analyze token contract |
| `vigil_detect_honeypot` | `token`, `chain` | Detect honeypot tokens |
| `vigil_safety_score` | `contract`, `chain` | Get safety score |
| `vigil_wallet_report` | `wallet`, `chain` | Full wallet report |

## Supported Chains

- base (default)
- ethereum
- polygon
- arbitrum

## Example: Scan USDC

```bash
curl -s -X POST https://mcp.vigil.codes/tools/call \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "id": 1,
    "method": "tools/call",
    "params": {
      "name": "vigil_scan_token",
      "arguments": {
        "token": "0x833588f63916024ffc580c12724940f2b8d47b5b",
        "chain": "base"
      }
    }
  }'
```

Response:
```json
{
  "token_name": "USD Coin",
  "token_symbol": "USDC",
  "safety_score": 92,
  "risk_level": "safe",
  "honeypot": {"detected": false},
  "recommendation": "Score: 92/100 — USD Coin is a known, verified contract"
}
```
