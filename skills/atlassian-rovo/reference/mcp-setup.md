# Atlassian MCP Server Setup Guide

How to connect Claude Code to Jira + Confluence on a single Atlassian Cloud site via the Rovo MCP Server.

## Prerequisites

- **Atlassian Cloud site** with both Jira and Confluence (e.g., `https://yoursite.atlassian.net`)
- **Node.js v18+** (for `mcp-remote` proxy)
- **Site admin access** for first-time OAuth authorization

## Step 1: Add the MCP Server

Create `.mcp.json` in your project root:

```json
{
  "mcpServers": {
    "atlassian": {
      "command": "npx",
      "args": ["-y", "mcp-remote@latest", "https://mcp.atlassian.com/v1/mcp"]
    }
  }
}
```

> **Note:** Use the `/mcp` endpoint, not `/sse`. The `/sse` endpoint is deprecated and will be removed after June 30, 2026.

## Step 2: Add Project Config to CLAUDE.md

Add this to your project's `CLAUDE.md` to avoid unnecessary API calls. Replace the placeholders with your actual values:

```markdown
## Atlassian Rovo MCP

When connected to atlassian MCP server:
- **MUST** use Jira project key = {YOUR_PROJECT_KEY}
- **MUST** use cloudId = "{YOUR_SITE}.atlassian.net" (do NOT call getAccessibleAtlassianResources)
- **MUST** use `maxResults: 10` or `limit: 10` for ALL Jira JQL and Confluence CQL search operations.
```

To find your values:
- **Project key**: Visit your Jira board — the key is the prefix on tickets (e.g., `PROJ` in `PROJ-123`)
- **Cloud site**: Your Atlassian URL (e.g., `https://myteam.atlassian.net`)

## Step 3: Authenticate via OAuth

The first time you start Claude Code after adding the MCP config, `mcp-remote` will try to connect but the OAuth flow needs to complete interactively.

### Run mcp-remote manually to trigger the OAuth flow:

```bash
npx -y mcp-remote@latest "https://mcp.atlassian.com/v1/mcp"
```

This will:
1. Start an OAuth callback server on `localhost` (typically port 3736)
2. Open your browser to the Atlassian authorization page
3. Wait for you to authorize

### In the browser:
1. Sign in with your Atlassian account
2. Select the site to authorize (e.g., `agentic-workflow`)
3. Grant the requested permissions

### Important:
- **Keep the terminal running** while you authorize in the browser. If the process dies before you complete auth, the `localhost` callback will refuse the connection.
- After successful auth, you'll see:
  ```
  Auth code received, resolving promise
  Connected to remote server using StreamableHTTPClientTransport
  Proxy established successfully
  ```
- OAuth tokens are cached in `~/.mcp-auth/mcp-remote-*/` — you won't need to re-auth unless tokens expire or are cleared.

## Step 4: Restart Claude Code

After OAuth completes, restart Claude Code. The MCP server will connect automatically using the cached tokens. Verify with `/mcp` or by running a test query.

## Verifying the Connection

Once connected, test both Jira and Confluence:

```
# Check accessible resources (should show both Jira and Confluence scopes)
atlassian:getAccessibleAtlassianResources

# Test Jira (replace with your cloudId and project key)
atlassian:searchJiraIssuesUsingJql
  cloudId: "https://yoursite.atlassian.net"
  jql: "project = {YOUR_PROJECT_KEY} ORDER BY created DESC"
  maxResults: 10

# Test Confluence
atlassian:search
  query: "test"
```

Expected scopes after authorization:
- **Jira:** `read:jira-work`, `write:jira-work`
- **Confluence:** `read:page:confluence`, `write:page:confluence`, `search:confluence`, `read:comment:confluence`, `write:comment:confluence`

## Troubleshooting

### MCP tools not appearing after restart
The OAuth flow hasn't completed. Run `mcp-remote` manually (Step 3) and authorize in the browser.

### "localhost refused to connect" after clicking authorize
The `mcp-remote` process died before you completed auth. Re-run it and keep the terminal open while you authorize.

### Only Jira or only Confluence scopes granted
If your Jira and Confluence are on the **same Atlassian site**, a single OAuth authorization covers both. Make sure you select the correct site during the consent flow.

### Jira and Confluence on different Atlassian sites
Use the `--resource` flag to create separate OAuth sessions per site:

```json
{
  "mcpServers": {
    "atlassian-jira": {
      "command": "npx",
      "args": [
        "-y", "mcp-remote@latest",
        "https://mcp.atlassian.com/v1/mcp",
        "--resource",
        "https://jira-site.atlassian.net/"
      ]
    },
    "atlassian-confluence": {
      "command": "npx",
      "args": [
        "-y", "mcp-remote@latest",
        "https://mcp.atlassian.com/v1/mcp",
        "--resource",
        "https://confluence-site.atlassian.net/"
      ]
    }
  }
}
```

Each entry gets its own OAuth token. You'll need to authorize each site separately.

### Re-authenticating
Clear cached tokens and re-run:

```bash
rm -rf ~/.mcp-auth/mcp-remote-*
npx -y mcp-remote@latest "https://mcp.atlassian.com/v1/mcp"
```

### "Cloud id isn't explicitly granted by the user"
You authorized a different site than the one you're querying. Clear tokens and re-auth, selecting the correct site.
