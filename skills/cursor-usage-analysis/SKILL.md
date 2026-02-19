---
name: cursor-usage-analysis
description: Interpret Cursor Enterprise API data correctly. Use when analyzing team AI spending, usage patterns, model adoption, or answering questions about Cursor usage metrics. Knows the gotchas and nuances that raw API numbers don't reveal.
license: MIT
metadata:
  author: ofershap
  version: "1.0"
---

# Cursor Usage Analysis

Guide for correctly interpreting data from the Cursor Enterprise Admin and Analytics APIs. The API returns raw numbers, but understanding what they mean requires context that is not in the official docs.

## When to Use This Skill

Use this when working with Cursor Enterprise API data, whether through:
- The `cursor-usage-mcp` MCP server (`npx cursor-usage-mcp`)
- Direct API calls to `https://api.cursor.com`
- Exported data from the Cursor admin dashboard

## Critical Data Interpretation Rules

### Spending

- `spendCents` is the **total** spend including the subscription-included amount. To get overage (extra cost beyond the plan), subtract `includedSpendCents`.
- A user with `spendCents: 5000` and `includedSpendCents: 4000` has $10 in overage, not $50 in total extra cost.
- `fastPremiumRequests` counts requests to premium/expensive models (Opus, GPT-5) that consume the fast request quota faster.
- Spend limits (`hardLimitOverrideDollars`) only cap overage spend, not included spend. A limit of $0 means "no overage allowed," not "no usage allowed."

### Lines of Code Metrics

- `totalLinesAdded` includes ALL lines: agent-suggested, tab-completed, and manually typed. It is NOT a measure of AI productivity.
- `acceptedLinesAdded` is the real AI productivity metric, counting lines the user explicitly accepted from AI suggestions.
- The acceptance rate (`acceptedLinesAdded / totalLinesAdded`) is misleading because the denominator includes manual edits. Use `totalAccepts / totalApplies` for the true AI acceptance rate.
- Agent mode lines are counted in `totalLinesAdded` but may not appear in `acceptedLinesAdded` because agent mode auto-applies changes.

### Request Types

- `composerRequests`: Inline edit requests (Cmd+K / Ctrl+K)
- `chatRequests`: Chat panel conversations
- `agentRequests`: Agent mode (autonomous multi-step tasks)
- `usageBasedReqs`: Requests that count against usage-based billing (overage)
- `cmdkUsages`: Legacy name for composer/inline edit usage
- `bugbotUsages`: Automated bug detection runs

### Model Usage

Model names in the API don't always match marketing names. Common mappings:
- `claude-sonnet-4.5` = Claude 4.5 Sonnet (mid-tier, good balance)
- `claude-opus-4.5` / `claude-opus-4.6` = Claude Opus (expensive, highest quality)
- `gpt-4o` = GPT-4o (OpenAI mid-tier)
- `gpt-5.2` / `gpt-5.3-codex` = GPT-5 variants (expensive)
- `gemini-3-flash` = Gemini Flash (fast, cheap)
- `gemini-3-pro` = Gemini Pro (mid-tier)

Cost tiers (approximate per request):
- **Budget**: Gemini Flash, smaller models ($0.001-0.01)
- **Standard**: Sonnet, GPT-4o ($0.01-0.05)
- **Premium**: Opus, GPT-5 ($0.10-0.50+)

A single user switching from Sonnet to Opus can 10x their daily spend.

### Analytics Data

- Analytics data is aggregated and may lag up to 1 hour behind real-time.
- `dau` counts anyone who made at least one request that day.
- `cli_dau` counts users of the Cursor CLI (terminal-based usage).
- `cloud_agent_dau` counts users of cloud-hosted agent sessions.
- Model breakdown `users` is the peak concurrent users for that model on that day, not unique users over the period.

### Usage Events

- Each event represents a single API request to an AI model.
- `isChargeable: false` means the request was covered by the subscription.
- `isChargeable: true` means it counted against overage/usage-based billing.
- `isHeadless: true` means the request came from background processing (Bugbot, indexing), not direct user action.
- `tokenUsage` may be null for non-token-based requests.
- `kind` values include: `chat`, `composer`, `agent`, `tab`, `cmd-k`, `bugbot`.

## Analysis Patterns

### "Who is spending the most?"
1. Get spending data for all members
2. Sort by `spendCents` descending
3. Flag anyone whose spend is >3x the team median
4. Check their model usage since premium model users will dominate

### "Are we getting value from AI?"
1. Get agent edit metrics for acceptance rates
2. Get tab completion metrics for autocomplete effectiveness
3. Compare `total_accepted_diffs / total_suggested_diffs` (healthy teams see 40-70% acceptance)
4. Low acceptance + high spend = the team is not finding AI suggestions useful

### "Which models should we standardize on?"
1. Get model usage for the last 30 days
2. Calculate cost-per-message for each model (cross-reference with spending data)
3. Models with high usage AND high acceptance rates are the best value
4. Models with high usage but low acceptance rates are wasting money

## MCP Server

For programmatic access to all these metrics, install the `cursor-usage-mcp` MCP server:

```json
{
  "mcpServers": {
    "cursor-usage": {
      "command": "npx",
      "args": ["-y", "cursor-usage-mcp"],
      "env": {
        "CURSOR_API_KEY": "your-api-key"
      }
    }
  }
}
```

For historical trends, anomaly detection, alerting, and a web dashboard, see [cursor-usage-tracker](https://github.com/ofershap/cursor-usage-tracker).
