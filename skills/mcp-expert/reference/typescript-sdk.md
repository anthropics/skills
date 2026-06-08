# MCP TypeScript SDK Guide

## Installation

```bash
npm install @modelcontextprotocol/sdk zod
# Optional for HTTP transport
npm install express
```

Package: `@modelcontextprotocol/sdk` (66M+ npm downloads, 27K+ dependent packages)
Current stable: v1.29.x. v2 is pre-alpha, targeting Q3 2026.

## Key Imports

```typescript
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { StreamableHTTPServerTransport } from "@modelcontextprotocol/sdk/server/streamableHttp.js";
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { StdioClientTransport } from "@modelcontextprotocol/sdk/client/stdio.js";
import { z } from "zod";
```

## Server Setup

```typescript
const server = new McpServer({
  name: "my-service-mcp-server",  // Convention: {service}-mcp-server
  version: "1.0.0"
});
```

**CRITICAL**: Use `registerTool`, `registerResource`, `registerPrompt` — NOT the deprecated
`server.tool()`, `server.setRequestHandler(ListToolsRequestSchema, ...)`. The register* methods
provide automatic schema handling, better type safety, and are the only supported API going forward.

## Tool Registration

```typescript
server.registerTool(
  "github_create_issue",
  {
    title: "Create GitHub Issue",
    description: `Create a new issue in a GitHub repository.

Args:
  - repo (string): Repository in owner/repo format (e.g., "octocat/hello-world")
  - title (string): Issue title (1-256 chars)
  - body (string, optional): Issue body in Markdown

Returns:
  JSON with: { "number": int, "url": string, "state": "open" }

Error handling:
  - "Error: 404" if repo not found
  - "Error: 422" if title is empty`,
    inputSchema: z.object({
      repo: z.string()
        .regex(/^[\w.-]+\/[\w.-]+$/, "Must be owner/repo format")
        .describe("Repository in owner/repo format"),
      title: z.string()
        .min(1).max(256)
        .describe("Issue title"),
      body: z.string()
        .optional()
        .describe("Issue body in Markdown")
    }).strict(),
    annotations: {
      readOnlyHint: false,
      destructiveHint: false,
      idempotentHint: false,
      openWorldHint: true
    }
  },
  async ({ repo, title, body }) => {
    try {
      const issue = await createGitHubIssue(repo, title, body);
      return {
        content: [{ type: "text", text: JSON.stringify(issue, null, 2) }]
      };
    } catch (error) {
      return {
        isError: true,
        content: [{ type: "text", text: handleError(error) }]
      };
    }
  }
);
```

## Resource Registration

```typescript
import { ResourceTemplate } from "@modelcontextprotocol/sdk/server/mcp.js";

// Dynamic resource with URI template
server.registerResource(
  {
    uri: "github://repos/{owner}/{repo}/readme",
    name: "GitHub README",
    description: "README file of a GitHub repository",
    mimeType: "text/markdown"
  },
  async (uri: string) => {
    const match = uri.match(/^github:\/\/repos\/([^/]+)\/([^/]+)\/readme$/);
    if (!match) throw new Error("Invalid URI");
    const [, owner, repo] = match;
    const content = await fetchReadme(owner, repo);
    return {
      contents: [{ uri, mimeType: "text/markdown", text: content }]
    };
  }
);

// List available resources dynamically
server.registerResourceList(async () => {
  const repos = await listUserRepos();
  return {
    resources: repos.map(r => ({
      uri: `github://repos/${r.full_name}/readme`,
      name: `${r.name} README`,
      mimeType: "text/markdown"
    }))
  };
});
```

## Prompt Registration

```typescript
server.registerPrompt(
  "analyze_codebase",
  {
    description: "Generate a structured analysis prompt for a codebase",
    arguments: [
      { name: "language", description: "Primary language", required: true },
      { name: "focus", description: "Analysis focus: security|performance|quality", required: false }
    ]
  },
  async ({ language, focus = "quality" }) => ({
    messages: [
      {
        role: "user" as const,
        content: {
          type: "text" as const,
          text: `Analyze this ${language} codebase for ${focus} issues. Be specific and actionable.`
        }
      }
    ]
  })
);
```

## Notifications

```typescript
// Notify clients that tool list changed
await server.notification({ method: "notifications/tools/list_changed" });

// Notify that a subscribed resource updated
await server.notification({
  method: "notifications/resources/updated",
  params: { uri: "github://repos/owner/repo/readme" }
});
```

## Stdio Transport (Local)

```typescript
async function runStdio() {
  const apiKey = process.env.GITHUB_TOKEN;
  if (!apiKey) {
    console.error("ERROR: GITHUB_TOKEN is required");
    process.exit(1);
  }

  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error("MCP server running via stdio");  // MUST use stderr
}

runStdio().catch(err => {
  console.error("Fatal:", err);
  process.exit(1);
});
```

## Streamable HTTP Transport (Remote)

```typescript
import express from "express";
import { StreamableHTTPServerTransport } from "@modelcontextprotocol/sdk/server/streamableHttp.js";

const app = express();
app.use(express.json());

// Optional: API key middleware
app.use('/mcp', (req, res, next) => {
  const key = req.headers['x-api-key'] || req.headers['authorization']?.replace('Bearer ', '');
  if (key !== process.env.API_KEY) {
    res.status(401).json({ error: "Unauthorized" });
    return;
  }
  next();
});

app.post('/mcp', async (req, res) => {
  // New transport per request = stateless (recommended for scalability)
  const transport = new StreamableHTTPServerTransport({
    sessionIdGenerator: undefined,  // stateless
    enableJsonResponse: true
  });
  res.on('close', () => transport.close());
  await server.connect(transport);
  await transport.handleRequest(req, res, req.body);
});

app.listen(process.env.PORT || 3000);
```

## MCP Client Implementation

```typescript
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { StdioClientTransport } from "@modelcontextprotocol/sdk/client/stdio.js";

const transport = new StdioClientTransport({
  command: "node",
  args: ["./dist/index.js"],
  env: { GITHUB_TOKEN: process.env.GITHUB_TOKEN! }
});

const client = new Client({
  name: "my-client",
  version: "1.0.0"
}, {
  capabilities: {
    roots: { listChanged: true },
    sampling: {}
  }
});

await client.connect(transport);

// Discover tools (with pagination)
async function listAllTools() {
  const tools = [];
  let cursor: string | undefined;
  do {
    const page = await client.listTools({ cursor });
    tools.push(...page.tools);
    cursor = page.nextCursor;
  } while (cursor);
  return tools;
}

// Invoke a tool
const result = await client.callTool({
  name: "github_create_issue",
  arguments: { repo: "owner/repo", title: "Bug found" }
});

// Fetch a resource
const resource = await client.readResource({ uri: "github://repos/owner/repo/readme" });

// Get a prompt
const prompt = await client.getPrompt({
  name: "analyze_codebase",
  arguments: { language: "typescript", focus: "security" }
});

// Close cleanly
await client.close();
```

## Project Structure (Best Practice)

```
my-service-mcp-server/
├── package.json            # "type": "module", main: "dist/index.js"
├── tsconfig.json           # target: ES2022, module: Node16, strict: true
├── src/
│   ├── index.ts            # McpServer init + transport selection
│   ├── constants.ts        # API_BASE_URL, CHARACTER_LIMIT = 25000
│   ├── types.ts            # TypeScript interfaces
│   ├── tools/
│   │   ├── issues.ts       # Issue-related tools
│   │   └── repos.ts        # Repo-related tools
│   ├── services/
│   │   └── github-client.ts # Axios client, auth, retry
│   └── schemas/
│       └── pagination.ts   # Shared Zod pagination schema
└── dist/                   # Built output
```

## tsconfig.json

```json
{
  "compilerOptions": {
    "target": "ES2022",
    "module": "Node16",
    "moduleResolution": "Node16",
    "outDir": "./dist",
    "rootDir": "./src",
    "strict": true,
    "esModuleInterop": true,
    "skipLibCheck": true,
    "declaration": true,
    "sourceMap": true
  },
  "include": ["src/**/*"],
  "exclude": ["node_modules", "dist"]
}
```

## package.json

```json
{
  "name": "my-service-mcp-server",
  "version": "1.0.0",
  "type": "module",
  "main": "dist/index.js",
  "scripts": {
    "build": "tsc",
    "start": "node dist/index.js",
    "dev": "tsx watch src/index.ts"
  },
  "dependencies": {
    "@modelcontextprotocol/sdk": "^1.29.0",
    "zod": "^3.23.8",
    "express": "^4.18.0",
    "axios": "^1.7.9"
  },
  "devDependencies": {
    "@types/node": "^22.0.0",
    "@types/express": "^4.17.0",
    "typescript": "^5.7.0",
    "tsx": "^4.19.0"
  }
}
```

## Error Handling Patterns

```typescript
function handleError(error: unknown): string {
  if (axios.isAxiosError(error)) {
    switch (error.response?.status) {
      case 401: return "Error: Authentication failed. Check your API token.";
      case 403: return "Error: Permission denied. Insufficient scopes.";
      case 404: return "Error: Resource not found. Verify the ID is correct.";
      case 429: return "Error: Rate limited. Wait before retrying.";
      default: return `Error: API error ${error.response?.status}: ${error.response?.data?.message}`;
    }
  }
  if (error instanceof z.ZodError) {
    return `Error: Invalid input: ${error.errors.map(e => `${e.path}: ${e.message}`).join(', ')}`;
  }
  return `Error: ${error instanceof Error ? error.message : String(error)}`;
}
```

## Pagination Response Pattern

```typescript
const CHARACTER_LIMIT = 25_000;

interface PaginatedResponse<T> {
  total: number;
  count: number;
  offset: number;
  items: T[];
  has_more: boolean;
  next_offset?: number;
  truncated?: boolean;
  truncation_message?: string;
}

function buildPaginatedResponse<T>(
  items: T[], total: number, offset: number
): PaginatedResponse<T> {
  return {
    total, count: items.length, offset, items,
    has_more: total > offset + items.length,
    next_offset: total > offset + items.length ? offset + items.length : undefined
  };
}
```
