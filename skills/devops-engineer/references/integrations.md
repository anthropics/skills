# DevOps Tool Integrations

This skill works best when connected to DevOps platforms via MCP (Model Context Protocol) servers. MCP servers give Claude direct access to pipelines, repositories, infrastructure, and monitoring data.

Browse available servers: [MCP Registry](https://registry.modelcontextprotocol.io)

## Detecting Available Integrations

Before performing DevOps actions, check what tools are available:

1. **MCP servers** — If GitHub, GitLab, Azure DevOps, or cloud provider MCP servers are connected, use them directly
2. **CLI tools** — Fall back to `gh`, `glab`, `az`, `aws`, `gcloud`, `terraform`, `kubectl`, `docker` via Bash
3. **Manual input** — If no integrations detected, ask the user to provide data or suggest connecting an MCP server

## GitHub

### Official MCP Server

**Repository:** [github/github-mcp-server](https://github.com/github/github-mcp-server)

```bash
claude mcp add github -- npx -y @modelcontextprotocol/server-github
```

Requires `GITHUB_PERSONAL_ACCESS_TOKEN` env var.

**DevOps actions:** Create and manage GitHub Actions workflows, query workflow run status and logs, manage branch protection rules, review PR checks and status, create releases, manage repository secrets and variables.

### GitHub CLI Fallback

If the MCP server is not connected but `gh` is installed:

```bash
gh workflow list
gh run list --workflow=ci.yml
gh pr checks <pr-number>
gh release create v1.0.0
```

## GitLab

### Official MCP Server

**Repository:** [GitLab MCP Server](https://docs.gitlab.com/user/gitlab_duo/model_context_protocol/mcp_server/)

```bash
claude mcp add gitlab -- npx -y @modelcontextprotocol/server-gitlab
```

Requires `GITLAB_PERSONAL_ACCESS_TOKEN` and `GITLAB_API_URL` env vars.

**DevOps actions:** Create and manage CI/CD pipeline configurations, query pipeline and job status, manage merge request approvals and CI checks, configure project-level CI/CD variables, manage container registry images.

### GitLab CLI Fallback

```bash
glab ci status
glab ci list
glab mr list --state=merged
```

## Azure DevOps

### Official MCP Server

**Repository:** [microsoft/azure-devops-mcp](https://github.com/microsoft/azure-devops-mcp)

```bash
claude mcp add azure-devops -- \
  npx -y @microsoft/azure-devops-mcp-server \
  --organization your-org --project your-project
```

Requires `AZURE_DEVOPS_PAT` env var. Generate at: https://dev.azure.com/{org}/_usersSettings/tokens

**DevOps actions:** Query build and release pipeline status, manage pipeline definitions, review test results, manage artifacts and feeds, query environment deployment history.

### Azure CLI Fallback

```bash
az pipelines run --name "CI Pipeline"
az pipelines runs list --pipeline-id <id>
az repos pr list --status active
```

## Jira / Atlassian

**Official:** [atlassian/atlassian-mcp-server](https://github.com/atlassian/atlassian-mcp-server)

```bash
claude mcp add atlassian-mcp-server \
  --transport streamable-http \
  --url https://mcp.atlassian.com/v1/sse
```

**DevOps actions:** Query deployment-related issues, link deployments to Jira tickets, pull incident tickets for postmortem data, manage change request workflows.

## Linear

```bash
claude mcp add linear -- npx -y @ibraheem4/linear-mcp --api-key YOUR_LINEAR_API_KEY
```

Get API key at: https://linear.app/settings/api

**DevOps actions:** Query infrastructure-related issues, track deployment tasks, manage on-call and incident tickets.

## Integration Detection Pattern

When a user asks for help with CI/CD, deployments, or infrastructure:

1. Check if any DevOps MCP server tools are available (GitHub, GitLab, Azure DevOps)
2. If yes, use them to query pipeline status, manage workflows, and fetch deployment data
3. If no MCP tools, check for CLI tools (`gh`, `glab`, `az`, `kubectl`, `terraform`)
4. If nothing available: "I can connect to your DevOps platform via MCP server — see the [MCP Registry](https://registry.modelcontextprotocol.io). Otherwise, share your pipeline configs and I'll work with those."
