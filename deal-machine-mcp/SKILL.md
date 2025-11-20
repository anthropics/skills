---
name: deal-machine-mcp
description: Ultimate Deal Machine MCP server that transforms Claude or ChatGPT into your real estate investment expert. Provides 10 AI-powered skills for lead analysis, ranking, marketing campaign creation, budget monitoring, and investment strategy planning. One-click install for comprehensive real estate investing automation.
---

# Deal Machine MCP Server

Transform your AI assistant into a real estate investment expert with 10 powerful tools for lead management, marketing campaigns, and investment planning.

## What It Does

This MCP server integrates Deal Machine's real estate platform with your AI assistant to provide:

1. **AI-Powered Lead Analysis** - Score and rank property leads by likelihood to sell
2. **Marketing Campaign Planning** - Create data-driven campaigns with ROI projections
3. **Budget Monitoring** - Track campaign performance and cost metrics
4. **Investment Strategy** - Generate personalized plans based on your goals
5. **Lead Management** - Add, update, and organize leads in Deal Machine
6. **High-Value Search** - Find properties matching your investment criteria
7. **Cost Estimation** - Forecast campaign costs and returns
8. **Performance Analytics** - Monitor response rates and conversion metrics

## Quick Start

### 1. Get Your API Key

1. Log in to [Deal Machine](https://www.dealmachine.com/)
2. Go to **Automation** → **API Docs**
3. Copy your API key

### 2. Install the MCP Server

Add to your Claude Desktop config (`~/Library/Application Support/Claude/claude_desktop_config.json` on macOS):

```json
{
  "mcpServers": {
    "deal-machine": {
      "command": "npx",
      "args": ["-y", "@dealmachine/mcp-server"],
      "env": {
        "DEALMACHINE_API_KEY": "your_api_key_here"
      }
    }
  }
}
```

### 3. Restart Claude Desktop

The Deal Machine tools will now be available in your conversations!

## Example Usage

### Analyze a Property Lead

```
You: Analyze this property for me:
     123 Main St, Austin TX 78701
     Value: $350K, Equity: $180K
     Built: 1985, Last sale: 2005

AI: [Provides detailed analysis with likelihood score, opportunities, and recommendations]
```

### Plan a Marketing Campaign

```
You: I have $2,000 for direct mail this month. Create a campaign plan.

AI: [Creates campaign with costs, expected response rate, and ROI projections]
```

### Generate Investment Strategy

```
You: I have $50K to invest over 12 months in wholesaling. Help me plan.

AI: [Generates complete strategy with monthly budgets, action steps, and deal projections]
```

## Available Tools

- **analyze_lead** - AI-powered property analysis with scoring
- **rank_leads** - Prioritize multiple leads by potential
- **add_property_lead** - Add leads to Deal Machine
- **update_lead_status** - Manage lead pipeline
- **create_marketing_campaign** - Design campaigns with ROI projections
- **estimate_campaign_cost** - Budget planning and forecasting
- **track_campaign_performance** - Monitor campaign metrics
- **generate_investment_strategy** - Personalized investment plans
- **find_high_value_leads** - Search for opportunities
- **get_lead_details** - Retrieve lead information

## Use Cases

### For New Investors
- Learn which leads to pursue first
- Plan your first marketing campaign
- Understand investment strategy basics
- Track early deals and ROI

### For Experienced Investors
- Scale operations with AI-powered analysis
- Optimize marketing spend and ROI
- Manage larger lead pipelines
- Track multiple campaigns simultaneously

### For Teams
- Standardize lead qualification
- Share campaign insights
- Coordinate marketing efforts
- Monitor team performance

## Requirements

- Node.js 18 or higher
- Deal Machine account with API access
- Claude Desktop or compatible MCP client

## Learn More

- [Full Documentation](./README.md)
- [Usage Examples](./EXAMPLES.md)
- [Deal Machine API Docs](https://docs.dealmachine.com/)
- [Model Context Protocol](https://modelcontextprotocol.io/)

## Support

For issues or questions:
- GitHub Issues: [Report a bug](https://github.com/yourusername/deal-machine-mcp/issues)
- Deal Machine Support: [Get API help](https://help.dealmachine.com/)

---

Built with ❤️ for real estate investors
