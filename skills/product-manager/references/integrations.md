# Product and Analytics Integrations

This skill works best when connected to product tools via MCP (Model Context Protocol) servers. MCP servers give Claude direct access to roadmaps, metrics, customer feedback, and project data.

Browse available servers: [MCP Registry](https://registry.modelcontextprotocol.io)

## Detecting Available Integrations

Before performing product management actions, check what tools are available:

1. **MCP servers** — If Jira, Linear, GitHub, GitLab, or analytics MCP servers are connected, use them directly
2. **CLI tools** — Fall back to `gh`, `glab`, or `az` via Bash if available
3. **Manual input** — If no integrations detected, ask the user to provide data or suggest connecting an MCP server

## Jira / Atlassian

**Official:** [atlassian/atlassian-mcp-server](https://github.com/atlassian/atlassian-mcp-server)

```bash
claude mcp add atlassian-mcp-server \
  --transport streamable-http \
  --url https://mcp.atlassian.com/v1/sse
```

**Community (Server/Data Center):** [sooperset/mcp-atlassian](https://github.com/sooperset/mcp-atlassian)

**Product Manager actions:** Query epics and roadmap initiatives across projects, pull Confluence product specs and strategy docs, analyze sprint completion for delivery predictability, extract customer feedback from Jira Service Management, generate competitive analysis from linked Confluence spaces.

## Linear

```bash
claude mcp add linear -- npx -y @ibraheem4/linear-mcp --api-key YOUR_LINEAR_API_KEY
```

Get API key at: https://linear.app/settings/api

**Product Manager actions:** Review project and initiative progress, analyze cycle velocity for roadmap planning, query issue labels and priorities for feature categorization, track team workload for resource allocation.

## GitHub (Issues and Projects)

**Official:** [github/github-mcp-server](https://github.com/github/github-mcp-server)

```bash
claude mcp add github -- npx -y @modelcontextprotocol/server-github
```

Requires `GITHUB_PERSONAL_ACCESS_TOKEN` env var.

**Product Manager actions:** Analyze issue trends for product health metrics, query project boards for roadmap status, review PR merge frequency for delivery cadence, track milestone progress for release planning.

## GitLab (Issues and Boards)

**Official:** [GitLab MCP Server](https://docs.gitlab.com/user/gitlab_duo/model_context_protocol/mcp_server/)

```bash
claude mcp add gitlab -- npx -y @modelcontextprotocol/server-gitlab
```

Requires `GITLAB_PERSONAL_ACCESS_TOKEN` and `GITLAB_API_URL` env vars.

**Product Manager actions:** Query issue analytics for product metrics, track milestone progress, analyze merge request throughput, review epic rollup status for roadmap reporting.

## Azure DevOps

**Official:** [microsoft/azure-devops-mcp](https://github.com/microsoft/azure-devops-mcp)

```bash
claude mcp add azure-devops -- \
  npx -y @microsoft/azure-devops-mcp-server \
  --organization your-org --project your-project
```

Requires `AZURE_DEVOPS_PAT` env var.

**Product Manager actions:** Query work item analytics for feature progress, pull test plan results for quality metrics, track build pipeline health for delivery confidence, analyze area path data for feature categorization.

## Integration Detection Pattern

When a user asks for help with product strategy, metrics, or roadmapping:

1. Check if any project management or analytics MCP server tools are available
2. If yes, pull real data to inform strategy recommendations
3. If no tools available: "I can connect to your product tools via MCP server — see the [MCP Registry](https://registry.modelcontextprotocol.io). Otherwise, share your data and I'll analyze it."
