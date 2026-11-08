# MCP Server Configuration

## Setup

```json
{
  "mcpServers": {
    "clicks-protocol": {
      "command": "npx",
      "args": ["@clicks-protocol/mcp-server"],
      "env": {
        "CLICKS_PRIVATE_KEY": "your-agent-private-key",
        "CLICKS_RPC_URL": "https://mainnet.base.org"
      }
    }
  }
}
```

Read-only tools work without `CLICKS_PRIVATE_KEY`.

## Available Tools

### Read (no key needed)
- `clicks_get_agent_info` - Registration status, deposited amount, yield percentage
- `clicks_simulate_split` - Preview how a deposit splits
- `clicks_get_yield_info` - Protocol APYs, total deposited, active protocol
- `clicks_get_referral_stats` - Referral count, earnings, claimable amount

### Write (requires CLICKS_PRIVATE_KEY)
- `clicks_quick_start` - Register + approve + deposit in one call
- `clicks_receive_payment` - Split incoming USDC 80/20
- `clicks_withdraw_yield` - Withdraw principal + earned yield
- `clicks_register_agent` - Register agent on-chain
- `clicks_set_yield_pct` - Adjust yield percentage (5-50%)
