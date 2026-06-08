# MCP Ecosystem Guide

## Ecosystem Scale (2026)

- 17,000+ MCP servers catalogued across registries
- The modelcontextprotocol/servers GitHub repo: 86,900+ stars
- Growth: 425 servers (Aug 2025) → 1,412 (Feb 2026) → 17,000+ (mid-2026)
- TypeScript SDK: 66M+ npm downloads, 27,000+ dependent packages
- Governance: Linux Foundation Agentic AI Foundation (donated Dec 2025)

## Official Reference Servers

From `github.com/modelcontextprotocol/servers` (Apache 2.0 / MIT):

| Server | Package | Capabilities |
|---|---|---|
| **Filesystem** | `@modelcontextprotocol/server-filesystem` | Secure file read/write with access controls |
| **Fetch** | `@modelcontextprotocol/server-fetch` | Web content retrieval, HTML→Markdown |
| **Memory** | `@modelcontextprotocol/server-memory` | Knowledge graph-based persistent memory |
| **Git** | `mcp-server-git` (Python) | Git repo reading, search, manipulation |
| **Time** | `@modelcontextprotocol/server-time` | Time queries and timezone conversion |
| **Sequential Thinking** | `@modelcontextprotocol/server-sequential-thinking` | Reflective problem-solving via thought chains |
| **Everything** | `@modelcontextprotocol/server-everything` | Demo server: prompts + resources + tools |

These are **reference/educational** implementations, not production-hardened.

## Client Configuration

### Claude Desktop

Config file location:
- macOS: `~/Library/Application Support/Claude/claude_desktop_config.json`
- Windows: `%APPDATA%\Claude\claude_desktop_config.json`

To open: Claude Desktop → Settings → Developer → Edit Config

**Basic stdio configuration:**
```json
{
  "mcpServers": {
    "filesystem": {
      "command": "npx",
      "args": [
        "-y",
        "@modelcontextprotocol/server-filesystem",
        "/Users/alice/Documents",
        "/Users/alice/Projects"
      ]
    },
    "memory": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-memory"]
    },
    "github": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-github"],
      "env": {
        "GITHUB_PERSONAL_ACCESS_TOKEN": "ghp_..."
      }
    },
    "postgres": {
      "command": "npx",
      "args": [
        "-y",
        "@modelcontextprotocol/server-postgres",
        "postgresql://localhost/mydb"
      ]
    }
  }
}
```

**Remote HTTP server:**
```json
{
  "mcpServers": {
    "my-api": {
      "url": "https://api.example.com/mcp",
      "headers": {
        "Authorization": "Bearer sk-..."
      }
    }
  }
}
```

After editing, restart Claude Desktop completely (Quit from menu, don't just close window).

### Claude Code (CLI)

Claude Code reads MCP config from:
- Project-level: `.claude/mcp_settings.json` in the project root
- Global: `~/.claude/mcp_settings.json`

```json
{
  "mcpServers": {
    "filesystem": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-filesystem", "."]
    }
  }
}
```

Or add via CLI: `claude mcp add <name> <command> [args...]`

### Cursor

Settings → Cursor Settings → MCP → Add MCP Server

Config: `~/.cursor/mcp.json`
```json
{
  "mcpServers": {
    "github": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-github"],
      "env": { "GITHUB_PERSONAL_ACCESS_TOKEN": "ghp_..." }
    }
  }
}
```

### Windsurf

Settings → Windsurf Settings → Cascade → MCP Servers

Config: `~/.codeium/windsurf/mcp_config.json`
```json
{
  "mcpServers": {
    "filesystem": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-filesystem", "/home/user"]
    }
  }
}
```

### VS Code (GitHub Copilot)

`.vscode/settings.json` or user settings:
```json
{
  "mcp.servers": {
    "my-server": {
      "command": "node",
      "args": ["./dist/index.js"]
    }
  }
}
```

### JetBrains IDEs

Settings → Tools → MCP Servers → Add

Supports stdio and HTTP transports. Config per-IDE.

## MCP Registries

| Registry | URL | Notable Feature |
|---|---|---|
| MCPNest | mcpnest.io | 7,500+ servers, one-click install |
| Glama | glama.ai/mcp/servers | Community favorites, quality ratings |
| FastMCP | fastmcp.ai | Python-focused, quality-curated |
| MCP.directory | mcp.directory | Blog + discovery |
| Awesome MCP Servers | mcpservers.org | Community-maintained list |
| Official repo | github.com/modelcontextprotocol/servers | Reference only |

## Commonly Used Community Servers

| Server | Use Case | Installation |
|---|---|---|
| `@modelcontextprotocol/server-github` | GitHub repos, issues, PRs | `npx -y @modelcontextprotocol/server-github` |
| `@modelcontextprotocol/server-postgres` | PostgreSQL read-only + schema | `npx -y @modelcontextprotocol/server-postgres` |
| `@modelcontextprotocol/server-slack` | Slack channels + messages | `npx -y @modelcontextprotocol/server-slack` |
| `@modelcontextprotocol/server-brave-search` | Web search via Brave | `npx -y @modelcontextprotocol/server-brave-search` |
| `@modelcontextprotocol/server-puppeteer` | Browser automation | `npx -y @modelcontextprotocol/server-puppeteer` |
| `mcp-server-sqlite` | SQLite database access | `uvx mcp-server-sqlite` |

## MCP Gateways

For enterprise deployments needing centralized control, rate limiting, and access management:

| Gateway | Key Features |
|---|---|
| MintMCP | Rate limiting, token bucket, per-client quotas |
| Gopher Security | Enterprise auth, audit logs, policy engine |
| MCPNest Enterprise | Private registry, team access control |

Gateways expose a single MCP endpoint that proxies to multiple backend servers,
adding auth, rate limiting, logging, and access control in one layer.

## Deployment Patterns

### Pattern 1: Claude Desktop + Local stdio Servers (Most Common)
Best for: Individual developers, local tools, no server infrastructure needed.

### Pattern 2: Docker Container + stdio
```dockerfile
FROM node:22-slim
WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production
COPY dist/ ./dist/
CMD ["node", "dist/index.js"]
```
Launch: `docker run -e API_KEY=sk-... my-mcp-server`

### Pattern 3: Remote HTTP + OAuth (Enterprise)
Best for: Team-wide access, CI/CD integration, multi-tenant.
Deploy to any HTTP host (Cloudflare Workers, Railway, Fly.io, AWS Lambda).

### Pattern 4: ASGI Multi-Server (Python)
Best for: Multiple tools in one deployment.
```python
# Single uvicorn process serves multiple MCP servers
app = Starlette(routes=[
    Mount("/github", mcp_github.streamable_http_app()),
    Mount("/slack", mcp_slack.streamable_http_app()),
])
```
