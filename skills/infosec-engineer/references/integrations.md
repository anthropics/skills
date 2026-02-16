# Security Tool Integrations

This skill works best when connected to development and security platforms via MCP (Model Context Protocol) servers. MCP servers give Claude direct access to repositories, pipelines, issues, and security findings.

Browse available servers: [MCP Registry](https://registry.modelcontextprotocol.io)

## Detecting Available Integrations

Before performing security actions, check what tools are available:

1. **MCP servers** — If GitHub, GitLab, Azure DevOps, or Jira MCP servers are connected, use them directly
2. **CLI tools** — Fall back to `gh`, `glab`, `az`, `trivy`, `npm audit`, `pip-audit` via Bash
3. **Manual input** — If no integrations detected, ask the user to provide data or suggest connecting an MCP server

## GitHub

**Official:** [github/github-mcp-server](https://github.com/github/github-mcp-server)

```bash
claude mcp add github -- npx -y @modelcontextprotocol/server-github
```

Requires `GITHUB_PERSONAL_ACCESS_TOKEN` env var.

**InfoSec actions:** Review PR diffs for security vulnerabilities, query Dependabot alerts, manage security advisory issues, review GitHub Actions workflows for CI/CD security gaps, check branch protection rules, audit repository access permissions.

## GitLab

**Official:** [GitLab MCP Server](https://docs.gitlab.com/user/gitlab_duo/model_context_protocol/mcp_server/)

```bash
claude mcp add gitlab -- npx -y @modelcontextprotocol/server-gitlab
```

Requires `GITLAB_PERSONAL_ACCESS_TOKEN` and `GITLAB_API_URL` env vars.

**InfoSec actions:** Review merge requests for security issues, query vulnerability reports, manage security-labeled issues, review CI pipeline security scan results, audit project-level access controls.

## Azure DevOps

**Official:** [microsoft/azure-devops-mcp](https://github.com/microsoft/azure-devops-mcp)

```bash
claude mcp add azure-devops -- \
  npx -y @microsoft/azure-devops-mcp-server \
  --organization your-org --project your-project
```

Requires `AZURE_DEVOPS_PAT` env var.

**InfoSec actions:** Query security-related work items, review build pipeline configurations for hardening gaps, track security bug resolution SLAs, manage compliance-related test plans, audit pipeline permissions and approvals.

## Jira / Atlassian

**Official:** [atlassian/atlassian-mcp-server](https://github.com/atlassian/atlassian-mcp-server)

```bash
claude mcp add atlassian-mcp-server \
  --transport streamable-http \
  --url https://mcp.atlassian.com/v1/sse
```

**InfoSec actions:** Track vulnerability remediation workflows, manage incident response tickets, query security policy documents in Confluence, track compliance audit findings, manage penetration test result tickets.

## Pusher Channels (Incident Communication)

**Registry:** [Pusher MCP on registry](https://registry.modelcontextprotocol.io/?q=pusher&all=1)

```bash
claude mcp add pusher -- npx -y @AshDevFr/pusher-channels-mcp-server
```

Requires `PUSHER_APP_ID`, `PUSHER_KEY`, `PUSHER_SECRET`, `PUSHER_CLUSTER` env vars.

**InfoSec actions:** Send real-time incident alerts to security channels, broadcast security status updates during active incidents, trigger automated notification workflows for severity escalations, monitor security event streams.

## Integration Detection Pattern

When a user asks for help with security reviews, compliance, or incident response:

1. Check if any development platform MCP servers are available
2. If yes, use them to review code for vulnerabilities, manage security issues, and audit configurations
3. If no MCP tools available, check for security CLI tools (`trivy`, `npm audit`, `pip-audit`, `bandit`)
4. If nothing available: "I can connect to your development and security platforms via MCP server — see the [MCP Registry](https://registry.modelcontextprotocol.io). Otherwise, share your code or findings and I'll analyze them."
