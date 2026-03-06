# Migration Tool Integrations

This skill works best when connected to development platforms via MCP (Model Context Protocol) servers. MCP servers give Claude direct access to source and target repositories, issue trackers, and pipeline systems.

Browse available servers: [MCP Registry](https://registry.modelcontextprotocol.io)

## Detecting Available Integrations

Before performing migration tasks, check what tools are available:

1. **MCP servers** — If GitHub, GitLab, Azure DevOps, or Jira MCP servers are connected, use them directly
2. **CLI tools** — Fall back to `gh`, `glab`, `az`, `terraform`, `kubectl`, `docker` via Bash
3. **Manual input** — If no integrations detected, ask the user to provide data or suggest connecting an MCP server

## GitHub

**Official:** [github/github-mcp-server](https://github.com/github/github-mcp-server)

```bash
claude mcp add github -- npx -y @modelcontextprotocol/server-github
```

Requires `GITHUB_PERSONAL_ACCESS_TOKEN` env var.

**Migration actions:** Analyze source repository structure and dependencies, create migration tracking issues and milestones, manage migration PRs across branches, review code changes during incremental migration, track migration progress via project boards.

## GitLab

**Official:** [GitLab MCP Server](https://docs.gitlab.com/user/gitlab_duo/model_context_protocol/mcp_server/)

```bash
claude mcp add gitlab -- npx -y @modelcontextprotocol/server-gitlab
```

Requires `GITLAB_PERSONAL_ACCESS_TOKEN` and `GITLAB_API_URL` env vars.

**Migration actions:** Analyze source project structure, create migration tracking issues, manage merge requests for migration branches, review CI pipeline configurations during migration, track migration milestones.

## Azure DevOps

**Official:** [microsoft/azure-devops-mcp](https://github.com/microsoft/azure-devops-mcp)

```bash
claude mcp add azure-devops -- \
  npx -y @microsoft/azure-devops-mcp-server \
  --organization your-org --project your-project
```

Requires `AZURE_DEVOPS_PAT` env var.

**Migration actions:** Query source project work items for migration scope, track migration tasks and bugs, review build pipeline changes during platform migration, manage test plans for migration validation, analyze repository structure.

## Jira / Atlassian

**Official:** [atlassian/atlassian-mcp-server](https://github.com/atlassian/atlassian-mcp-server)

```bash
claude mcp add atlassian-mcp-server \
  --transport streamable-http \
  --url https://mcp.atlassian.com/v1/sse
```

**Migration actions:** Create and track migration epics with phase breakdowns, manage risk register as Jira issues, document migration decisions in Confluence, track go/no-go checklist items, link migration tasks to impacted services.

## Pusher Channels (Migration Monitoring)

**Registry:** [Pusher MCP on registry](https://registry.modelcontextprotocol.io/?q=pusher&all=1)

```bash
claude mcp add pusher -- npx -y @AshDevFr/pusher-channels-mcp-server
```

Requires `PUSHER_APP_ID`, `PUSHER_KEY`, `PUSHER_SECRET`, `PUSHER_CLUSTER` env vars.

**Migration actions:** Broadcast real-time migration progress updates to stakeholder dashboards, send cutover status notifications, trigger alerts on data validation failures during migration, monitor parallel-run discrepancy events.

## Integration Detection Pattern

When a user asks for help with migration planning or execution:

1. Check if any platform MCP servers are connected (for both source and target systems)
2. If yes, use them to analyze current state, create migration plans, and track progress
3. If no MCP tools available, check for CLI tools (`gh`, `glab`, `az`, `terraform`, `kubectl`)
4. If nothing available: "I can connect to your source and target platforms via MCP server — see the [MCP Registry](https://registry.modelcontextprotocol.io). Otherwise, describe your current architecture and I'll plan from there."
