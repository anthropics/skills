---
project:
  pypi: https://pypi.org/project/strands-teams/
  github: https://github.com/eraykeskinmac/strands-teams
  maintainer: eraykeskinmac
service:
  name: microsoft-teams
  link: https://teams.microsoft.com/
---

# strands-teams

{{ community_contribution_banner }}

[strands-teams](https://github.com/eraykeskinmac/strands-teams) is a production-ready Microsoft Teams notification tool with rich Adaptive Cards support and custom messaging capabilities.

## Installation

```bash
pip install strands-teams
```

## Usage

```python
from strands import Agent
from strands_teams import teams

agent = Agent(tools=[teams])

# Simple notification
agent("send a Teams message: New lead from Acme Corp")

# Status update with formatting
agent("send a status update: Website redesign is 75% complete")

# Custom adaptive card
agent("create approval request for Q4 budget with amount $50000")
```

## Key Features

- **Adaptive Cards**: Rich, interactive message cards with modern UI
- **Pre-built Templates**: Notifications, approvals, status updates, and alerts
- **Custom Cards**: Full adaptive card schema support for complex layouts
- **Action Buttons**: Add interactive elements and quick actions
- **Rich Formatting**: Markdown support, images, tables, and media
- **Webhook Integration**: Seamless Teams channel integration

## Configuration

```bash
TEAMS_WEBHOOK_URL=your_teams_webhook_url  # Optional (can be provided per call)
```

Setup webhook: Teams Channel → Connectors → Incoming Webhook

## Resources

- [PyPI Package](https://pypi.org/project/strands-teams/)
- [GitHub Repository](https://github.com/eraykeskinmac/strands-teams)
- [Examples & Demos](https://github.com/eraykeskinmac/strands-tools-examples)
- [Adaptive Cards](https://adaptivecards.io/)
- [Teams Webhooks](https://learn.microsoft.com/en-us/microsoftteams/platform/webhooks-and-connectors/what-are-webhooks-and-connectors)
