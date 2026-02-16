# Project Management Integrations

This skill works best when connected to project management tools via MCP (Model Context Protocol) servers. MCP servers give Claude direct access to backlogs, boards, issues, and workflows.

Browse available servers: [MCP Registry](https://registry.modelcontextprotocol.io)

## Detecting Available Integrations

Before performing backlog management actions, check what tools are available:

1. **MCP servers** — If Jira, Trello, Azure DevOps, Linear, GitHub, or GitLab MCP servers are connected, use them directly
2. **CLI tools** — Fall back to `gh` (GitHub CLI), `glab` (GitLab CLI), or `az` (Azure CLI) via Bash if available
3. **Manual input** — If no integrations detected, ask the user to provide data or suggest they connect an MCP server

## Jira / Atlassian

**Official:** [atlassian/atlassian-mcp-server](https://github.com/atlassian/atlassian-mcp-server)

```bash
claude mcp add atlassian-mcp-server \
  --transport streamable-http \
  --url https://mcp.atlassian.com/v1/sse
```

**Community (Server/Data Center):** [sooperset/mcp-atlassian](https://github.com/sooperset/mcp-atlassian)

```bash
claude mcp add jira -- \
  npx -y @sooperset/mcp-atlassian \
  --jira-url https://your-instance.atlassian.net \
  --jira-email your@email.com \
  --jira-token YOUR_API_TOKEN
```

**Product Owner actions:** Create and prioritize stories, write acceptance criteria on issues, manage epics and backlog ordering, query sprint completion rates for release planning, pull stakeholder feedback from Confluence pages.

## Trello

**npm:** [@delorenj/mcp-server-trello](https://www.npmjs.com/package/@delorenj/mcp-server-trello)

```bash
claude mcp add trello -- npx -y @delorenj/mcp-server-trello
```

Requires `TRELLO_API_KEY` and `TRELLO_TOKEN` env vars. Get credentials at: https://trello.com/power-ups/admin

**Product Owner actions:** Create cards with user stories and acceptance criteria, organize lists as backlog priority tiers, label cards by MoSCoW category, track card completion for velocity data.

## Azure DevOps

**Official:** [microsoft/azure-devops-mcp](https://github.com/microsoft/azure-devops-mcp)

```bash
claude mcp add azure-devops -- \
  npx -y @microsoft/azure-devops-mcp-server \
  --organization your-org --project your-project
```

Requires `AZURE_DEVOPS_PAT` env var. Generate at: https://dev.azure.com/{org}/_usersSettings/tokens

**Product Owner actions:** Create and prioritize work items (epics, features, user stories), manage backlog ordering, set iteration paths for sprint scoping, query backlog health metrics, write acceptance criteria on work items.

## Linear

```bash
claude mcp add linear -- npx -y @ibraheem4/linear-mcp --api-key YOUR_LINEAR_API_KEY
```

Get API key at: https://linear.app/settings/api

**Product Owner actions:** Create and prioritize issues, manage project roadmaps, set cycle scope, track project progress for release planning.

## GitHub (Issues and Projects)

**Official:** [github/github-mcp-server](https://github.com/github/github-mcp-server)

```bash
claude mcp add github -- npx -y @modelcontextprotocol/server-github
```

Requires `GITHUB_PERSONAL_ACCESS_TOKEN` env var.

**Product Owner actions:** Create issues with user stories and acceptance criteria, manage milestones for release planning, label issues by priority, query project board columns for backlog state.

## GitLab (Issues and Boards)

**Official:** [GitLab MCP Server](https://docs.gitlab.com/user/gitlab_duo/model_context_protocol/mcp_server/)

```bash
claude mcp add gitlab -- npx -y @modelcontextprotocol/server-gitlab
```

Requires `GITLAB_PERSONAL_ACCESS_TOKEN` and `GITLAB_API_URL` env vars.

**Product Owner actions:** Create issues with acceptance criteria, manage issue weights for estimation, set milestones for releases, organize board lists as priority lanes.

## Integration Detection Pattern

When a user asks for help with backlog management or story writing:

1. Check if any project management MCP server tools are available
2. If yes, use them to fetch the current backlog and create/update items directly
3. If no MCP tools available, check for CLI tools (`gh`, `glab`, `az`)
4. If nothing available: "I can connect to your project management tool via MCP server — see the [MCP Registry](https://registry.modelcontextprotocol.io). Otherwise, describe your backlog and I'll work with that."
