---
project:
  pypi: https://pypi.org/project/strands-hubspot/
  github: https://github.com/eraykeskinmac/strands-hubspot
  maintainer: eraykeskinmac
service:
  name: hubspot
  link: https://developers.hubspot.com/
---

# strands-hubspot

{{ community_contribution_banner }}

[strands-hubspot](https://github.com/eraykeskinmac/strands-hubspot) is a production-ready HubSpot CRM tool designed for **READ-ONLY** operations with zero risk of data modification. It enables agents to safely access and analyze CRM data without any possibility of corrupting customer information.

This community tool provides comprehensive HubSpot integration for AI agents, offering safe CRM data access for sales intelligence, customer research, and data analytics workflows.

## Installation

```bash
pip install strands-hubspot
```

## Usage

```python
from strands import Agent
from strands_hubspot import hubspot

# Create an agent with HubSpot READ-ONLY tool
agent = Agent(tools=[hubspot])

# Search contacts (READ-ONLY)
agent("find all contacts created in the last 30 days")

# Get company details (READ-ONLY)
agent("get company information for ID 67890")

# List available properties (READ-ONLY)
agent("show me all available deal properties")

# Search with filters (READ-ONLY)
agent("search for deals with amount greater than 10000")
```

## Key Features

- **Universal READ-ONLY Access**: Safely search ANY HubSpot object type (contacts, deals, companies, tickets, etc.)
- **Smart Search**: Advanced filtering with property-based queries and sorting
- **Object Retrieval**: Get detailed information for specific CRM objects by ID
- **Property Discovery**: List and explore all available properties for any object type
- **User Management**: Get HubSpot user/owner details and assignments
- **100% Safe**: NO CREATE, UPDATE, or DELETE operations - read-only by design
- **Rich Console Output**: Beautiful table displays with Rich library formatting
- **Type Safe**: Full type hints and comprehensive error handling

## Configuration

Set your HubSpot API key as an environment variable:

```bash
HUBSPOT_API_KEY=your_hubspot_api_key      # Required
HUBSPOT_DEFAULT_LIMIT=100                 # Optional
```

Get your API key at: [HubSpot Private Apps](https://developers.hubspot.com/docs/api/private-apps)

## Resources

- [PyPI Package](https://pypi.org/project/strands-hubspot/)
- [GitHub Repository](https://github.com/eraykeskinmac/strands-hubspot)
- [Examples & Demos](https://github.com/eraykeskinmac/strands-tools-examples)
- [HubSpot API Docs](https://developers.hubspot.com/)
