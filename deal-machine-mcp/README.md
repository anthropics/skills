# Deal Machine MCP Server

> Your AI-powered real estate investment expert - Transform Claude or ChatGPT into a sophisticated real estate investment assistant

## Overview

The Deal Machine MCP (Model Context Protocol) Server turns your AI assistant into a real estate investment expert. It combines the power of Deal Machine's property lead database with AI-driven analysis to help you:

- **Review and rank leads** by likelihood to sell
- **Create data-driven marketing campaigns** optimized for your budget
- **Monitor campaign performance** with detailed analytics
- **Generate personalized investment strategies** based on your goals
- **Automate lead management** and follow-up workflows

## Features

### 10 Powerful Tools

1. **analyze_lead** - AI-powered lead analysis with likelihood scores (0-100), risk factors, opportunities, and actionable recommendations
2. **rank_leads** - Automatically rank multiple leads to prioritize your outreach efforts
3. **add_property_lead** - Add new property leads directly to your Deal Machine account
4. **update_lead_status** - Update lead status, add notes, and manage tags
5. **create_marketing_campaign** - Design complete marketing campaigns with cost estimates and ROI projections
6. **estimate_campaign_cost** - Get detailed cost breakdowns for any campaign size
7. **track_campaign_performance** - Monitor response rates, cost per lead, and ROI metrics
8. **generate_investment_strategy** - Create personalized investment plans with step-by-step action items
9. **find_high_value_leads** - Search for leads matching your investment criteria
10. **get_lead_details** - Retrieve comprehensive information about any lead

## Quick Start

### Prerequisites

- Node.js 18 or higher
- A Deal Machine account with API access
- Claude Desktop or compatible MCP client

### Installation

#### Option 1: Install from npm (recommended)

```bash
npm install -g @dealmachine/mcp-server
```

#### Option 2: Install from source

```bash
git clone https://github.com/yourusername/deal-machine-mcp.git
cd deal-machine-mcp
npm install
npm run build
```

### Get Your Deal Machine API Key

1. Log in to your Deal Machine account
2. Navigate to **Automation** → **API Docs**
3. Copy your API key

### Configuration

#### For Claude Desktop

Add to your Claude Desktop configuration file:

**macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`
**Windows**: `%APPDATA%\Claude\claude_desktop_config.json`

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

#### For ChatGPT (with MCP support)

Configure in your MCP settings:

```json
{
  "servers": {
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

#### Using .env file (for development)

Create a `.env` file in the project root:

```bash
DEALMACHINE_API_KEY=your_api_key_here
```

### Verify Installation

Restart your Claude Desktop or ChatGPT application. You should see the Deal Machine tools available in your AI assistant.

## Usage Examples

### Example 1: Analyze a Property Lead

```
Human: Analyze this property lead for me:
- Address: 123 Main St, Austin, TX 78701
- Owner: John Smith
- Estimated Value: $350,000
- Estimated Equity: $180,000
- Year Built: 1985
- Last Sale: 2005

AI: [Uses analyze_lead tool]
```

**Result**: Comprehensive analysis with a likelihood score, key indicators, risk factors, and recommended actions.

### Example 2: Create an Investment Plan

```
Human: I have $50,000 to invest in real estate over the next 12 months. I'm interested in wholesaling and fix-and-flip properties. Help me create an investment strategy.

AI: [Uses generate_investment_strategy tool]
```

**Result**: Detailed strategy including monthly marketing budget, expected lead flow, target property types, and step-by-step action plan.

### Example 3: Plan a Direct Mail Campaign

```
Human: I want to send postcards to 500 properties with a budget of $1,000. What can I expect?

AI: [Uses create_marketing_campaign tool]
```

**Result**: Campaign plan with cost breakdown, expected response rate, estimated leads, and ROI projections.

### Example 4: Rank Your Lead List

```
Human: I have 20 property leads. Help me prioritize which ones to contact first based on likelihood to sell.

AI: [Uses rank_leads tool]
```

**Result**: Sorted list of leads with scores and detailed analysis for each property.

### Example 5: Monitor Campaign Performance

```
Human: I sent 1,000 postcards at $0.85 each. I got 15 responses and closed 2 deals worth $20,000 in total revenue. How did my campaign perform?

AI: [Uses track_campaign_performance tool]
```

**Result**: Detailed performance metrics including response rate, cost per response, ROI percentage, and recommendations.

## Tool Reference

### analyze_lead

Analyzes a single property lead with AI-powered insights.

**Parameters:**
- `lead` (object, required): Property information including address, city, state, zip, and optional fields like estimated_value, estimated_equity, year_built, last_sale_date, etc.

**Returns:**
- Likelihood score (0-100)
- Confidence level (low/medium/high)
- Key indicators
- Risk factors
- Opportunity factors
- Recommended action
- Estimated ROI potential

### rank_leads

Ranks multiple property leads by likelihood to sell.

**Parameters:**
- `leads` (array, required): Array of lead objects

**Returns:**
- Sorted array of lead analyses from highest to lowest potential

### add_property_lead

Adds a new property lead to Deal Machine.

**Parameters:**
- `address` (string, required)
- `city` (string, required)
- `state` (string, required)
- `zip` (string, required)
- `owner_name` (string, optional)
- `owner_phone` (string, optional)
- `owner_email` (string, optional)
- `property_type` (string, optional)
- `estimated_value` (number, optional)
- `notes` (string, optional)
- `tags` (array, optional)

**Returns:**
- Success confirmation and lead ID

### update_lead_status

Updates an existing lead's information.

**Parameters:**
- `lead_id` (string, required)
- `status` (string, optional)
- `notes` (string, optional)
- `tags` (array, optional)

**Returns:**
- Success confirmation

### create_marketing_campaign

Creates a detailed marketing campaign plan.

**Parameters:**
- `budget` (number, required): Total campaign budget
- `target_count` (number, required): Number of properties to target
- `campaign_type` (enum, required): 'direct_mail', 'postcards', 'letters', or 'combo'
- `min_equity` (number, optional): Minimum equity requirement
- `property_types` (array, optional): Types of properties to target

**Returns:**
- Complete campaign plan with costs, response rates, and ROI projections

### estimate_campaign_cost

Estimates campaign costs and returns.

**Parameters:**
- `lead_count` (number, required): Number of leads to mail
- `campaign_type` (enum, required): Campaign type
- `mailing_frequency` (number, optional): Number of mailings per lead (default: 1)

**Returns:**
- Total cost
- Cost breakdown
- Expected responses
- Cost per response

### track_campaign_performance

Monitors campaign performance metrics.

**Parameters:**
- `campaign_name` (string, required)
- `budget` (number, required)
- `target_count` (number, required)
- `cost_per_piece` (number, required)
- `campaign_type` (string, required)
- `sent_count` (number, required)
- `responses` (number, required)
- `deals_closed` (number, optional)
- `revenue_generated` (number, optional)

**Returns:**
- Detailed performance analytics including ROI

### generate_investment_strategy

Creates a personalized investment strategy.

**Parameters:**
- `budget` (number, required): Total investment budget
- `timeline_months` (number, required): Investment timeline
- `goals` (array, required): Array of goals ('wholesaling', 'rental_income', 'fix_and_flip', 'buy_and_hold')

**Returns:**
- Comprehensive investment strategy with action steps

### find_high_value_leads

Searches for high-value investment opportunities.

**Parameters:**
- `min_equity` (number, optional): Minimum equity threshold
- `max_price` (number, optional): Maximum property price
- `property_types` (array, optional): Property types to search
- `min_age` (number, optional): Minimum property age

**Returns:**
- Filtered and ranked list of matching leads

### get_lead_details

Retrieves detailed information about a specific lead.

**Parameters:**
- `lead_id` (string, required): Lead ID to retrieve

**Returns:**
- Complete lead information and analysis

## Real-World Workflows

### Workflow 1: New Investor Getting Started

1. **Generate Strategy**: Use `generate_investment_strategy` with your budget and goals
2. **Find Opportunities**: Use `find_high_value_leads` to identify good prospects
3. **Plan Campaign**: Use `create_marketing_campaign` to design your outreach
4. **Add Leads**: Use `add_property_lead` to import properties into Deal Machine
5. **Monitor Results**: Use `track_campaign_performance` to measure success

### Workflow 2: Experienced Investor Optimizing Operations

1. **Analyze Current Leads**: Use `rank_leads` to prioritize your list
2. **Review Top Prospects**: Use `analyze_lead` for detailed insights on high-scorers
3. **Update Pipeline**: Use `update_lead_status` to keep your CRM current
4. **Estimate ROI**: Use `estimate_campaign_cost` before launching campaigns
5. **Track Performance**: Use `track_campaign_performance` for continuous improvement

### Workflow 3: Scale Your Business

1. **Batch Analysis**: Upload lead lists and use `rank_leads` to process hundreds at once
2. **Automated Campaigns**: Create multiple campaigns with `create_marketing_campaign`
3. **Performance Tracking**: Monitor all campaigns with `track_campaign_performance`
4. **Strategy Refinement**: Use insights to generate new strategies with `generate_investment_strategy`

## API Rate Limits

- **Per Second**: 10 requests
- **Per Day**: 5,000 requests

The MCP server automatically handles rate limiting to prevent errors.

## Development

### Build from source

```bash
npm install
npm run build
```

### Watch mode for development

```bash
npm run watch
```

### Test with MCP Inspector

```bash
npm run inspector
```

## Architecture

```
deal-machine-mcp/
├── src/
│   ├── index.ts          # Main MCP server and tool definitions
│   ├── api-client.ts     # Deal Machine API client with rate limiting
│   ├── analytics.ts      # AI-powered analysis and ranking algorithms
│   └── types.ts          # TypeScript type definitions
├── dist/                 # Compiled JavaScript (generated)
├── package.json          # Dependencies and scripts
├── tsconfig.json         # TypeScript configuration
└── README.md            # This file
```

## Technology Stack

- **MCP SDK**: Model Context Protocol for AI integration
- **TypeScript**: Type-safe development
- **Axios**: HTTP client for API calls
- **Zod**: Runtime type validation

## Troubleshooting

### API Key Issues

**Error**: "Invalid API key"

**Solution**:
1. Verify your API key is correct
2. Ensure it's properly set in your environment
3. Check that your Deal Machine account has API access enabled

### Rate Limit Errors

**Error**: "Rate limit exceeded"

**Solution**: The server automatically manages rate limits. If you see this error, wait a moment and try again. For high-volume use, consider batching operations.

### Connection Issues

**Error**: "No response from Deal Machine API"

**Solution**:
1. Check your internet connection
2. Verify Deal Machine API is operational
3. Ensure your API key hasn't expired

### Installation Issues

**Error**: Module not found

**Solution**:
```bash
# Clear npm cache and reinstall
npm cache clean --force
npm install
npm run build
```

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## Support

- **Issues**: Report bugs or request features on [GitHub Issues](https://github.com/yourusername/deal-machine-mcp/issues)
- **Deal Machine Support**: Contact Deal Machine support for API-related questions
- **Documentation**: Visit [Deal Machine API Docs](https://docs.dealmachine.com/)

## License

MIT License - See LICENSE file for details

## Acknowledgments

- Built with the [Model Context Protocol](https://modelcontextprotocol.io/)
- Powered by [Deal Machine](https://www.dealmachine.com/) - The #1 tool for real estate investors
- Designed for use with [Claude](https://claude.ai/) and other AI assistants

---

**Ready to transform your real estate investing?** Install now and start analyzing leads like a pro! 🏠📈
