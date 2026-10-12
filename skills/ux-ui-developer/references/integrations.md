# Design and Development Integrations

This skill works best when connected to development platforms via MCP (Model Context Protocol) servers. MCP servers give Claude direct access to repositories, issue trackers, and real-time collaboration channels.

Browse available servers: [MCP Registry](https://registry.modelcontextprotocol.io)

## Detecting Available Integrations

Before performing UI development actions, check what tools are available:

1. **MCP servers** — If GitHub, GitLab, or communication MCP servers are connected, use them directly
2. **CLI tools** — Fall back to `gh`, `glab`, or `npx` via Bash if available
3. **Manual input** — If no integrations detected, ask the user to provide design specs or suggest connecting an MCP server

## GitHub

**Official:** [github/github-mcp-server](https://github.com/github/github-mcp-server)

```bash
claude mcp add github -- npx -y @modelcontextprotocol/server-github
```

Requires `GITHUB_PERSONAL_ACCESS_TOKEN` env var.

**UX/UI actions:** Create issues for accessibility bugs with WCAG references, review PR diffs for design system compliance, query component library repositories, manage design-related labels and milestones.

## GitLab

**Official:** [GitLab MCP Server](https://docs.gitlab.com/user/gitlab_duo/model_context_protocol/mcp_server/)

```bash
claude mcp add gitlab -- npx -y @modelcontextprotocol/server-gitlab
```

Requires `GITLAB_PERSONAL_ACCESS_TOKEN` and `GITLAB_API_URL` env vars.

**UX/UI actions:** Review merge requests for UI changes, manage design system issues, track accessibility audit findings, query component documentation in wikis.

## Jira / Atlassian

**Official:** [atlassian/atlassian-mcp-server](https://github.com/atlassian/atlassian-mcp-server)

```bash
claude mcp add atlassian-mcp-server \
  --transport streamable-http \
  --url https://mcp.atlassian.com/v1/sse
```

**UX/UI actions:** Track UX research findings in Confluence, manage design task workflows in Jira, link design decisions to implementation stories, query usability testing results.

## Pusher Channels (Real-Time UI)

**Registry:** [Pusher MCP on registry](https://registry.modelcontextprotocol.io/?q=pusher&all=1)

```bash
claude mcp add pusher -- npx -y @AshDevFr/pusher-channels-mcp-server
```

Requires `PUSHER_APP_ID`, `PUSHER_KEY`, `PUSHER_SECRET`, `PUSHER_CLUSTER` env vars.

**UX/UI actions:** Debug real-time UI updates (live notifications, collaborative editing, presence indicators), test WebSocket event flows, verify real-time component behavior, monitor channel subscriptions for live features.

## Integration Detection Pattern

When a user asks for help with UI development or design reviews:

1. Check if any development platform MCP servers are available
2. If yes, use them to review code, manage issues, or access documentation
3. If no MCP tools available, check for CLI tools
4. If nothing available: "I can connect to your development tools via MCP server — see the [MCP Registry](https://registry.modelcontextprotocol.io). Otherwise, share your code or design specs directly."
