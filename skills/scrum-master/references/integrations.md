# Project Management Integrations

This skill works best when connected to project management tools via MCP (Model Context Protocol) servers. MCP servers give Claude direct access to boards, sprints, issues, and workflows without copy-pasting.

Browse available servers: [MCP Registry](https://registry.modelcontextprotocol.io)

## Detecting Available Integrations

Before performing project management actions, check what tools are available:

1. **MCP servers** — If Jira, Trello, Azure DevOps, Linear, GitHub, or GitLab MCP servers are connected, use them directly
2. **CLI tools** — Fall back to `gh` (GitHub CLI), `glab` (GitLab CLI), or `az` (Azure CLI) via Bash if available
3. **Manual input** — If no integrations are detected, ask the user to provide data manually or suggest they connect an MCP server

Always inform the user which integration path is being used.

## Jira / Atlassian

### Official MCP Server

Atlassian provides an official remote MCP server for Jira and Confluence Cloud.

**Repository:** [atlassian/atlassian-mcp-server](https://github.com/atlassian/atlassian-mcp-server)

**Claude Code setup:**
```bash
claude mcp add atlassian-mcp-server \
  --transport streamable-http \
  --url https://mcp.atlassian.com/v1/sse
```

**Claude Desktop (`claude_desktop_config.json`):**
```json
{
  "mcpServers": {
    "atlassian": {
      "url": "https://mcp.atlassian.com/v1/sse"
    }
  }
}
```

Authentication is handled via OAuth through the Atlassian cloud.

### Community Alternative

For Jira Server/Data Center or more control:

**Repository:** [sooperset/mcp-atlassian](https://github.com/sooperset/mcp-atlassian)

```bash
claude mcp add jira -- \
  npx -y @sooperset/mcp-atlassian \
  --jira-url https://your-instance.atlassian.net \
  --jira-email your@email.com \
  --jira-token YOUR_API_TOKEN
```

### Scrum Master Actions with Jira

When Jira MCP is connected, use it to:
- Fetch current sprint data: board ID, sprint goal, active stories
- Pull velocity metrics from completed sprints
- Create and update stories during backlog refinement
- Move issues between columns during standups
- Generate sprint reports from completed work
- Query impediments (blocked issues) across the board

## Trello

### MCP Server

**npm:** [@delorenj/mcp-server-trello](https://www.npmjs.com/package/@delorenj/mcp-server-trello)

**Claude Code setup:**
```bash
claude mcp add trello -- \
  npx -y @delorenj/mcp-server-trello
```

**Environment variables required:**
```
TRELLO_API_KEY=your_api_key
TRELLO_TOKEN=your_token
```

Get credentials at: https://trello.com/power-ups/admin

### Scrum Master Actions with Trello

When Trello MCP is connected, use it to:
- Read board columns (map to sprint backlog, in progress, done)
- Move cards between lists during standups
- Create cards during backlog refinement
- Read card details for sprint planning
- Track card movement history for cycle time analysis

## Azure DevOps

### Official MCP Server

Microsoft provides an official MCP server for Azure DevOps (GA since October 2025).

**Repository:** [microsoft/azure-devops-mcp](https://github.com/microsoft/azure-devops-mcp)

**Claude Code setup:**
```bash
claude mcp add azure-devops -- \
  npx -y @microsoft/azure-devops-mcp-server \
  --organization your-org \
  --project your-project
```

**Environment variables required:**
```
AZURE_DEVOPS_PAT=your_personal_access_token
```

Generate a PAT at: https://dev.azure.com/{org}/_usersSettings/tokens

### Scrum Master Actions with Azure DevOps

When Azure DevOps MCP is connected, use it to:
- Query work items by sprint iteration path
- Read sprint capacity and burndown data
- Create and update work items (user stories, tasks, bugs)
- Manage sprint scope (move items between iterations)
- Pull build/release pipeline status for sprint reviews
- Generate sprint velocity from completed iterations

## Linear

### MCP Server

**Remote MCP:** [linear.dev](https://www.remote-mcp.com/servers/linear)

**Claude Code setup:**
```bash
claude mcp add linear -- \
  npx -y @ibraheem4/linear-mcp \
  --api-key YOUR_LINEAR_API_KEY
```

Get API key at: https://linear.app/settings/api

### Scrum Master Actions with Linear

When Linear MCP is connected, use it to:
- Fetch cycle (sprint) data and progress
- List and filter issues by status, assignee, or label
- Create issues during backlog refinement
- Update issue status during standups
- Query project progress for sprint reviews
- Pull team workload for capacity planning

## GitHub (Issues and Projects)

### Official MCP Server

**Repository:** [github/github-mcp-server](https://github.com/github/github-mcp-server)

**Claude Code setup:**
```bash
claude mcp add github -- \
  npx -y @modelcontextprotocol/server-github
```

**Environment variables required:**
```
GITHUB_PERSONAL_ACCESS_TOKEN=your_pat
```

### Scrum Master Actions with GitHub

When GitHub MCP is connected, use it to:
- Query GitHub Projects boards for sprint tracking
- Create and label issues during refinement
- Manage milestones as sprint containers
- Pull PR review status for sprint reviews
- Track issue cycle time via label/status changes

## GitLab (Issues and Boards)

### Official MCP Server

**Repository:** [modelcontextprotocol/servers (GitLab)](https://github.com/modelcontextprotocol/servers)
**GitLab docs:** [GitLab MCP Server](https://docs.gitlab.com/user/gitlab_duo/model_context_protocol/mcp_server/)

**Claude Code setup:**
```bash
claude mcp add gitlab -- \
  npx -y @modelcontextprotocol/server-gitlab
```

**Environment variables required:**
```
GITLAB_PERSONAL_ACCESS_TOKEN=your_pat
GITLAB_API_URL=https://gitlab.com/api/v4
```

### Scrum Master Actions with GitLab

When GitLab MCP is connected, use it to:
- Query issue boards for sprint tracking
- Create and label issues during refinement
- Manage milestones as sprint containers
- Pull merge request status for sprint reviews
- Track issue weight for velocity calculations

## Integration Detection Pattern

When a user asks for help with sprint data or project management tasks, follow this sequence:

1. Check if any project management MCP server tools are available
2. If yes, use them to fetch real data before providing advice
3. If no MCP tools are available, check for CLI tools (`gh`, `glab`, `az`)
4. If nothing is available, ask the user:
   - "I don't have direct access to your project management tool. You can connect one via MCP server — see the [MCP Registry](https://registry.modelcontextprotocol.io) for available integrations."
   - "Alternatively, paste your sprint board data or describe the current state and I'll work with that."
