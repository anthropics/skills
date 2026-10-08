# Node/TypeScript MCP Server Implementation Guide (SDK v2)

## Overview

This document provides Node/TypeScript-specific best practices and examples for implementing MCP servers with **v2 of the MCP TypeScript SDK** (`@modelcontextprotocol/server`). It covers project structure, server setup, tool registration patterns, input validation with Zod, error handling, and complete working examples.

v2 is the current stable release line and the right choice for new servers. If the project already depends on the v1 package `@modelcontextprotocol/sdk`, either follow the [v1 guide](./node_mcp_server.md) or migrate first (see [Migrating a v1 Server](#migrating-a-v1-server)).

---

## Quick Reference

### Key Imports
```typescript
import { createMcpHandler, McpServer, ResourceTemplate } from "@modelcontextprotocol/server";
import { serveStdio } from "@modelcontextprotocol/server/stdio";
import { createMcpExpressApp } from "@modelcontextprotocol/express";  // HTTP only
import { toNodeHandler } from "@modelcontextprotocol/node";           // HTTP only
import * as z from "zod/v4";
```

### Server Initialization
```typescript
// A factory: the SDK calls it to build the server instance for each stdio connection or HTTP request
function createServer(): McpServer {
  const server = new McpServer({
    name: "service-mcp-server",
    version: "1.0.0"
  });
  // server.registerTool(...)
  return server;
}
```

### Tool Registration Pattern
```typescript
server.registerTool(
  "tool_name",
  {
    title: "Tool Display Name",
    description: "What the tool does",
    inputSchema: z.object({ param: z.string() }),
    outputSchema: z.object({ result: z.string() })
  },
  async ({ param }) => {
    const output = { result: `Processed: ${param}` };
    return {
      content: [{ type: "text", text: JSON.stringify(output) }],
      structuredContent: output // Must match outputSchema
    };
  }
);
```

### Serving
```typescript
// stdio (local)
serveStdio(createServer);

// Streamable HTTP (remote)
const handler = createMcpHandler(createServer);
const app = createMcpExpressApp();
const nodeHandler = toNodeHandler(handler);
app.all("/mcp", (req, res) => void nodeHandler(req, res, req.body));
app.listen(3000, "127.0.0.1");
```

### v1 → v2 at a Glance

Most published examples and training data show v1 code. Translate it before use:

| v1 (`@modelcontextprotocol/sdk`) | v2 |
|---|---|
| `import ... from "@modelcontextprotocol/sdk/server/mcp.js"` | `import ... from "@modelcontextprotocol/server"` |
| `import ... from "@modelcontextprotocol/sdk/server/stdio.js"` | `import ... from "@modelcontextprotocol/server/stdio"` |
| `zod ^3`, `import { z } from "zod"` | `zod ^4.2.0`, `import * as z from "zod/v4"` |
| `inputSchema: { q: z.string() }` (raw shape) | `inputSchema: z.object({ q: z.string() })` |
| `server.tool(...)`, `server.resource(...)`, `server.prompt(...)` | Removed: use `registerTool`, `registerResource`, `registerPrompt` |
| `new StdioServerTransport()` + `server.connect(transport)` | `serveStdio(createServer)` (`StdioServerTransport` from `@modelcontextprotocol/server/stdio` also still works) |
| Per-request `StreamableHTTPServerTransport` + `express.json()` | `createMcpHandler(createServer)` + `createMcpExpressApp()` + `toNodeHandler()` |
| Handler `extra.signal`, `extra.authInfo` | Handler `ctx.mcpReq.signal`, `ctx.http?.authInfo` |
| `McpError`, `ErrorCode` | `ProtocolError`, `ProtocolErrorCode` |
| Node.js 18+ | Node.js 20+ |

---

## MCP TypeScript SDK (v2)

The official MCP TypeScript SDK v2 provides:
- `@modelcontextprotocol/server`: `McpServer`, `registerTool` / `registerResource` / `registerPrompt`, `createMcpHandler` (HTTP), and `serveStdio` (from the `/stdio` subpath)
- Optional HTTP adapters: `@modelcontextprotocol/node` (`toNodeHandler`) plus `@modelcontextprotocol/express`, `@modelcontextprotocol/hono`, or `@modelcontextprotocol/fastify`
- [Standard Schema](https://standardschema.dev/) input and output schemas: Zod v4 (4.2.0 or later), Valibot, or ArkType
- Type-safe handlers: argument types are inferred from `inputSchema`
- Both protocol eras from one factory: clients on the 2026-07-28 revision and older 2025-era clients are served by default, with no extra code

**IMPORTANT - Use v2 APIs Only:**
- **DO use**: `server.registerTool()`, `server.registerResource()`, `server.registerPrompt()` with Zod object schemas; `serveStdio()`; `createMcpHandler()`
- **DO NOT use**: imports from `@modelcontextprotocol/sdk/...` (the v1 package), raw-shape schemas (`{ q: z.string() }`), Zod 3 or `zod/v3`, `server.tool()`, `server.setRequestHandler(...)`, or hand-wired `StreamableHTTPServerTransport` instances
- Register tools inside the server factory, never on a shared instance outside it

**Documentation**: The v2 docs index is `https://ts.sdk.modelcontextprotocol.io/v2/llms.txt`; every page is also served as markdown at its `.md` URL (e.g. `https://ts.sdk.modelcontextprotocol.io/v2/servers/tools.md`).

## Server Naming Convention

Node/TypeScript MCP servers must follow this naming pattern:
- **Format**: `{service}-mcp-server` (lowercase with hyphens)
- **Examples**: `github-mcp-server`, `jira-mcp-server`, `stripe-mcp-server`

The name should be:
- General (not tied to specific features)
- Descriptive of the service/API being integrated
- Easy to infer from the task description
- Without version numbers or dates

## Project Structure

Create the following structure for Node/TypeScript MCP servers:

```
{service}-mcp-server/
├── package.json
├── tsconfig.json
├── README.md
├── src/
│   ├── index.ts          # Entry point: createServer() factory and transport selection
│   ├── types.ts          # TypeScript type definitions and interfaces
│   ├── tools/            # Tool implementations (one file per domain)
│   ├── services/         # API clients and shared utilities
│   ├── schemas/          # Zod validation schemas
│   └── constants.ts      # Shared constants (API_URL, CHARACTER_LIMIT, etc.)
└── dist/                 # Built JavaScript files (entry point: dist/index.js)
```

A common layout is one `registerXxxTools(server: McpServer)` function per file in `tools/`, all called from `createServer()`.

## Tool Implementation

### Tool Naming

Use snake_case for tool names (e.g., "search_users", "create_project", "get_channel_info") with clear, action-oriented names.

**Avoid Naming Conflicts**: Include the service context to prevent overlaps:
- Use "slack_send_message" instead of just "send_message"
- Use "github_create_issue" instead of just "create_issue"
- Use "asana_list_tasks" instead of just "list_tasks"

### Tool Structure

Tools are registered using the `registerTool` method with the following requirements:
- The `description` field must be explicitly provided - JSDoc comments are NOT automatically extracted
- Explicitly provide `title`, `description`, `inputSchema`, and `annotations`
- `inputSchema` must be a Zod object schema (`z.object(...)` or `z.strictObject(...)`), not a raw shape and not a JSON Schema object
- From that one schema the SDK derives the JSON Schema clients see, validates arguments before the handler runs, and infers the handler's argument types
- If you declare `outputSchema`, every non-error result must include matching `structuredContent`; otherwise the SDK replaces the result with an output validation error
- A result that includes `structuredContent` should also include the same data serialized as JSON in a text block (the spec says SHOULD). A tool with a Markdown `response_format` therefore returns `structuredContent` only in JSON mode, and does not declare `outputSchema`

```typescript
import { McpServer } from "@modelcontextprotocol/server";
import * as z from "zod/v4";

// Zod schema for input validation
const UserSearchInputSchema = z.strictObject({
  query: z.string()
    .min(2, "Query must be at least 2 characters")
    .max(200, "Query must not exceed 200 characters")
    .describe("Search string to match against names/emails"),
  limit: z.number()
    .int()
    .min(1)
    .max(100)
    .default(20)
    .describe("Maximum results to return"),
  offset: z.number()
    .int()
    .min(0)
    .default(0)
    .describe("Number of results to skip for pagination"),
  response_format: z.enum(ResponseFormat)
    .default(ResponseFormat.MARKDOWN)
    .describe("Output format: 'markdown' for human-readable or 'json' for machine-readable")
});

interface User {
  id: string;
  name: string;
  email: string;
  team?: string;
  active: boolean;
}

interface UserSearchResponse {
  users: User[];
  total: number;
}

server.registerTool(
  "example_search_users",
  {
    title: "Search Example Users",
    description: `Search for users in the Example system by name, email, or team.

This tool searches across all user profiles in the Example platform, supporting partial matches and various search filters. It does NOT create or modify users, only searches existing ones.

Args:
  - query (string): Search string to match against names/emails
  - limit (number): Maximum results to return, between 1-100 (default: 20)
  - offset (number): Number of results to skip for pagination (default: 0)
  - response_format ('markdown' | 'json'): Output format (default: 'markdown')

Returns:
  For JSON format: Structured data with schema:
  {
    "total": number,           // Total number of matches found
    "count": number,           // Number of results in this response
    "offset": number,          // Current pagination offset
    "users": [
      {
        "id": string,          // User ID (e.g., "U123456789")
        "name": string,        // Full name (e.g., "John Doe")
        "email": string,       // Email address
        "team": string,        // Team name (optional)
        "active": boolean      // Whether user is active
      }
    ],
    "has_more": boolean,       // Whether more results are available
    "next_offset": number      // Offset for next page (if has_more is true)
  }

Examples:
  - Use when: "Find all marketing team members" -> params with query="team:marketing"
  - Use when: "Search for John's account" -> params with query="john"
  - Don't use when: You need to create a user (use example_create_user instead)

Error Handling:
  - Returns "Error: Rate limit exceeded" if too many requests (429 status)
  - Returns "No users found matching '<query>'" if search returns empty`,
    inputSchema: UserSearchInputSchema,
    annotations: {
      readOnlyHint: true,
      destructiveHint: false,
      idempotentHint: true,
      openWorldHint: true
    }
  },
  // params is inferred from inputSchema; defaults are already applied
  async (params, ctx) => {
    try {
      const data = await makeApiRequest<UserSearchResponse>(
        "users/search",
        "GET",
        undefined,
        { q: params.query, limit: params.limit, offset: params.offset },
        ctx.mcpReq.signal // Aborts the upstream request if the client cancels
      );

      const users = data.users;
      const hasMore = data.total > params.offset + users.length;

      if (params.response_format === ResponseFormat.JSON) {
        const output = {
          total: data.total,
          count: users.length,
          offset: params.offset,
          users,
          has_more: hasMore,
          ...(hasMore ? { next_offset: params.offset + users.length } : {})
        };
        // Structured data, plus the same data serialized as text
        return {
          content: [{ type: "text", text: JSON.stringify(output, null, 2) }],
          structuredContent: output
        };
      }

      if (!users.length) {
        return {
          content: [{ type: "text", text: `No users found matching '${params.query}'` }]
        };
      }

      const lines = [`# User Search Results: '${params.query}'`, "",
        `Found ${data.total} users (showing ${users.length})`, ""];
      for (const user of users) {
        lines.push(`## ${user.name} (${user.id})`);
        lines.push(`- **Email**: ${user.email}`);
        if (user.team) lines.push(`- **Team**: ${user.team}`);
        lines.push("");
      }
      if (hasMore) {
        lines.push(`More results available: use offset=${params.offset + users.length}`);
      }

      return {
        content: [{ type: "text", text: lines.join("\n") }]
      };
    } catch (error) {
      return {
        content: [{ type: "text", text: handleApiError(error) }],
        isError: true // The model reads this and can retry or adjust
      };
    }
  }
);
```

## Zod Schemas for Input Validation

v2 requires Zod 4.2.0 or later. Zod provides runtime type validation:

```typescript
import * as z from "zod/v4";

// Basic schema with validation
const CreateUserSchema = z.strictObject({  // Strict: rejects unknown fields
  name: z.string()
    .min(1, "Name is required")
    .max(100, "Name must not exceed 100 characters"),
  email: z.email("Invalid email format"),
  age: z.number()
    .int("Age must be a whole number")
    .min(0, "Age cannot be negative")
    .max(150, "Age cannot be greater than 150")
});

// Enums
enum ResponseFormat {
  MARKDOWN = "markdown",
  JSON = "json"
}

const SearchSchema = z.object({
  response_format: z.enum(ResponseFormat)
    .default(ResponseFormat.MARKDOWN)
    .describe("Output format")
});

// Optional fields with defaults
const PaginationSchema = z.object({
  limit: z.number()
    .int()
    .min(1)
    .max(100)
    .default(20)
    .describe("Maximum results to return"),
  offset: z.number()
    .int()
    .min(0)
    .default(0)
    .describe("Number of results to skip")
});
```

**Zod 4 notes:**
- `z.strictObject({...})` replaces `z.object({...}).strict()`, and advertises `additionalProperties: false`
- `z.enum(MyTsEnum)` replaces `z.nativeEnum(MyTsEnum)`
- `z.email()`, `z.url()`, `z.uuid()` replace `z.string().email()` and similar
- `.describe()` text becomes the JSON Schema `description`, which is the only documentation the model sees for each argument
- Fields with `.default()` are optional in the advertised JSON Schema and always present in the handler's arguments
- Arguments that fail validation never reach the handler: the client gets an `isError: true` result such as `Input validation error: Invalid arguments for tool example_search_users: query: Query must be at least 2 characters`

## Response Format Options

Support multiple output formats for flexibility:

```typescript
enum ResponseFormat {
  MARKDOWN = "markdown",
  JSON = "json"
}

const inputSchema = z.object({
  query: z.string(),
  response_format: z.enum(ResponseFormat)
    .default(ResponseFormat.MARKDOWN)
    .describe("Output format: 'markdown' for human-readable or 'json' for machine-readable")
});
```

**Markdown format**:
- Use headers, lists, and formatting for clarity
- Convert timestamps to human-readable format
- Show display names with IDs in parentheses
- Omit verbose metadata
- Group related information logically

**JSON format**:
- Return complete, structured data suitable for programmatic processing
- Include all available fields and metadata
- Use consistent field names and types

In JSON mode, return the data as `structuredContent` and the same data serialized as JSON in the text block. In Markdown mode, return only the Markdown text. A tool that declares `outputSchema` must return `structuredContent` on every successful call, so declare one only on tools whose text output is always JSON.

## Pagination Implementation

For tools that list resources:

```typescript
const ListSchema = z.object({
  limit: z.number().int().min(1).max(100).default(20),
  offset: z.number().int().min(0).default(0)
});

async function listItems(params: z.infer<typeof ListSchema>) {
  const data = await apiRequest(params.limit, params.offset);

  const response = {
    total: data.total,
    count: data.items.length,
    offset: params.offset,
    items: data.items,
    has_more: data.total > params.offset + data.items.length,
    next_offset: data.total > params.offset + data.items.length
      ? params.offset + data.items.length
      : undefined
  };

  return JSON.stringify(response, null, 2);
}
```

## Character Limits and Truncation

Add a CHARACTER_LIMIT constant to prevent overwhelming responses:

```typescript
// At module level in constants.ts
export const CHARACTER_LIMIT = 25000;  // Maximum response size in characters

async function searchTool(params: SearchInput) {
  let result = generateResponse(data);

  // Check character limit and truncate if needed
  if (result.length > CHARACTER_LIMIT) {
    const truncatedData = data.slice(0, Math.max(1, data.length / 2));
    response.data = truncatedData;
    response.truncated = true;
    response.truncation_message =
      `Response truncated from ${data.length} to ${truncatedData.length} items. ` +
      `Use 'offset' parameter or add filters to see more results.`;
    result = JSON.stringify(response, null, 2);
  }

  return result;
}
```

## Error Handling

MCP has two error channels:
- **Tool errors** are tool results with `isError: true`. The model reads them and can recover, so put the fix in the message.
- **Protocol errors** are JSON-RPC error responses handled by the client application; the model never sees them.

In tool handlers:
- Return `isError: true` with an actionable message for expected failures (not found, permission denied, rate limit)
- Anything a tool handler throws is converted to an `isError: true` result whose text is the exception's `message`, so a thrown `Error` is also visible to the model
- Schema validation failures are returned as `isError: true` results automatically

In resource and prompt callbacks (which have no `isError` channel), throw `ProtocolError` or one of its subclasses:

```typescript
import { ProtocolError, ProtocolErrorCode, ResourceNotFoundError } from "@modelcontextprotocol/server";

throw new ProtocolError(ProtocolErrorCode.InvalidParams, "Document names are lowercase letters");
throw new ResourceNotFoundError(uri.href);
```

Map upstream API failures to clear, actionable messages:

```typescript
import axios, { AxiosError } from "axios";

function handleApiError(error: unknown): string {
  if (error instanceof AxiosError) {
    if (error.response) {
      switch (error.response.status) {
        case 404:
          return "Error: Resource not found. Please check the ID is correct.";
        case 403:
          return "Error: Permission denied. You don't have access to this resource.";
        case 429:
          return "Error: Rate limit exceeded. Please wait before making more requests.";
        default:
          return `Error: API request failed with status ${error.response.status}`;
      }
    } else if (error.code === "ECONNABORTED") {
      return "Error: Request timed out. Please try again.";
    }
  }
  return `Error: Unexpected error occurred: ${error instanceof Error ? error.message : String(error)}`;
}
```

## Handler Context

Every handler receives a context object as its second argument (its only argument when the tool has no `inputSchema`):

```typescript
server.registerTool(
  "example_get_profile",
  {
    description: "Get the authenticated user's profile",
    inputSchema: z.object({ include_teams: z.boolean().default(false) })
  },
  async ({ include_teams }, ctx) => {
    const token = ctx.http?.authInfo?.token;  // Set by your auth middleware; undefined on stdio
    const res = await fetch(`${API_BASE_URL}/me?teams=${include_teams}`, {
      headers: token ? { Authorization: `Bearer ${token}` } : {},
      signal: ctx.mcpReq.signal               // Aborted when the client cancels the call
    });
    return { content: [{ type: "text", text: await res.text() }] };
  }
);
```

- `ctx.mcpReq.signal`: an `AbortSignal` for the call; pass it to upstream requests
- `ctx.http?.authInfo`: the verified token info on HTTP (see [Streamable HTTP](#streamable-http-recommended-for-remote-servers))
- Progress, logging, and asking the user for input mid-call are covered in the [v2 docs](https://ts.sdk.modelcontextprotocol.io/v2/llms.txt)

## Shared Utilities

Extract common functionality into reusable functions:

```typescript
// Shared API request function
async function makeApiRequest<T>(
  endpoint: string,
  method: "GET" | "POST" | "PUT" | "DELETE" = "GET",
  data?: unknown,
  params?: Record<string, unknown>,
  signal?: AbortSignal
): Promise<T> {
  const response = await axios<T>({
    method,
    url: `${API_BASE_URL}/${endpoint}`,
    data,
    params,
    signal,
    timeout: 30000,
    headers: {
      "Content-Type": "application/json",
      "Accept": "application/json"
    }
  });
  return response.data;
}
```

## Async/Await Best Practices

Always use async/await for network requests and I/O operations:

```typescript
// Good: Async network request
async function fetchData(resourceId: string): Promise<ResourceData> {
  const response = await axios.get(`${API_URL}/resource/${resourceId}`);
  return response.data;
}

// Bad: Promise chains
function fetchData(resourceId: string): Promise<ResourceData> {
  return axios.get(`${API_URL}/resource/${resourceId}`)
    .then(response => response.data);  // Harder to read and maintain
}
```

## TypeScript Best Practices

1. **Use Strict TypeScript**: Enable strict mode in tsconfig.json
2. **Define Interfaces**: Create clear interface definitions for all data structures
3. **Avoid `any`**: Use proper types or `unknown` instead of `any`
4. **Zod for Runtime Validation**: Use Zod schemas to validate external data
5. **Type Guards**: Create type guard functions for complex type checking
6. **Error Handling**: Always use try-catch with proper error type checking
7. **Null Safety**: Use optional chaining (`?.`) and nullish coalescing (`??`)

```typescript
// Good: Type-safe with Zod
const UserSchema = z.object({
  id: z.string(),
  name: z.string(),
  email: z.email(),
  team: z.string().optional(),
  active: z.boolean()
});

type User = z.infer<typeof UserSchema>;

async function getUser(id: string): Promise<User> {
  const data = await apiCall(`/users/${id}`);
  return UserSchema.parse(data);  // Runtime validation
}

// Bad: Using any
async function getUser(id: string): Promise<any> {
  return await apiCall(`/users/${id}`);  // No type safety
}
```

## Package Configuration

### package.json

```json
{
  "name": "{service}-mcp-server",
  "version": "1.0.0",
  "description": "MCP server for {Service} API integration",
  "type": "module",
  "main": "dist/index.js",
  "scripts": {
    "start": "node dist/index.js",
    "dev": "tsx watch src/index.ts",
    "build": "tsc",
    "clean": "rm -rf dist"
  },
  "engines": {
    "node": ">=20"
  },
  "dependencies": {
    "@modelcontextprotocol/server": "^2.3.1",
    "axios": "^1.7.9",
    "zod": "^4.2.0"
  },
  "devDependencies": {
    "@types/node": "^22.10.0",
    "tsx": "^4.19.2",
    "typescript": "^5.9.3"
  }
}
```

For a Streamable HTTP server with Express, also add:

```json
{
  "dependencies": {
    "@modelcontextprotocol/express": "^2.0.2",
    "@modelcontextprotocol/node": "^2.1.1",
    "express": "^5.1.0"
  },
  "devDependencies": {
    "@types/express": "^5.0.0"
  }
}
```

Keep `zod` at `^4.2.0` or later: v2 does not support Zod 3, and Zod 4.0–4.1 drops `.describe()` text from the advertised schemas.

### tsconfig.json

```json
{
  "compilerOptions": {
    "target": "ES2022",
    "module": "Node16",
    "moduleResolution": "Node16",
    "lib": ["ES2022"],
    "outDir": "./dist",
    "rootDir": "./src",
    "strict": true,
    "esModuleInterop": true,
    "skipLibCheck": true,
    "forceConsistentCasingInFileNames": true,
    "declaration": true,
    "declarationMap": true,
    "sourceMap": true
  },
  "include": ["src/**/*"],
  "exclude": ["node_modules", "dist"]
}
```

## Complete Example

```typescript
#!/usr/bin/env node
/**
 * MCP Server for Example Service.
 *
 * This server provides tools to interact with Example API, including user search,
 * project management, and data export capabilities.
 */

import { createMcpHandler, McpServer } from "@modelcontextprotocol/server";
import { serveStdio } from "@modelcontextprotocol/server/stdio";
import { createMcpExpressApp } from "@modelcontextprotocol/express";
import { toNodeHandler } from "@modelcontextprotocol/node";
import * as z from "zod/v4";
import axios, { AxiosError } from "axios";

// Constants
const API_BASE_URL = "https://api.example.com/v1";
const CHARACTER_LIMIT = 25000;

// Enums
enum ResponseFormat {
  MARKDOWN = "markdown",
  JSON = "json"
}

// Zod schemas
const UserSearchInputSchema = z.strictObject({
  query: z.string()
    .min(2, "Query must be at least 2 characters")
    .max(200, "Query must not exceed 200 characters")
    .describe("Search string to match against names/emails"),
  limit: z.number()
    .int()
    .min(1)
    .max(100)
    .default(20)
    .describe("Maximum results to return"),
  offset: z.number()
    .int()
    .min(0)
    .default(0)
    .describe("Number of results to skip for pagination"),
  response_format: z.enum(ResponseFormat)
    .default(ResponseFormat.MARKDOWN)
    .describe("Output format: 'markdown' for human-readable or 'json' for machine-readable")
});

interface User {
  id: string;
  name: string;
  email: string;
  team?: string;
  active: boolean;
}

interface UserSearchResponse {
  users: User[];
  total: number;
}

// Shared utility functions
async function makeApiRequest<T>(
  endpoint: string,
  method: "GET" | "POST" | "PUT" | "DELETE" = "GET",
  data?: unknown,
  params?: Record<string, unknown>,
  signal?: AbortSignal
): Promise<T> {
  const response = await axios<T>({
    method,
    url: `${API_BASE_URL}/${endpoint}`,
    data,
    params,
    signal,
    timeout: 30000,
    headers: {
      "Content-Type": "application/json",
      "Accept": "application/json"
    }
  });
  return response.data;
}

function handleApiError(error: unknown): string {
  if (error instanceof AxiosError) {
    if (error.response) {
      switch (error.response.status) {
        case 404:
          return "Error: Resource not found. Please check the ID is correct.";
        case 403:
          return "Error: Permission denied. You don't have access to this resource.";
        case 429:
          return "Error: Rate limit exceeded. Please wait before making more requests.";
        default:
          return `Error: API request failed with status ${error.response.status}`;
      }
    } else if (error.code === "ECONNABORTED") {
      return "Error: Request timed out. Please try again.";
    }
  }
  return `Error: Unexpected error occurred: ${error instanceof Error ? error.message : String(error)}`;
}

// Server factory: builds a fresh McpServer with every tool registered.
// serveStdio calls it once per connection; createMcpHandler calls it once per HTTP request.
function createServer(): McpServer {
  const server = new McpServer({
    name: "example-mcp-server",
    version: "1.0.0"
  });

  server.registerTool(
    "example_search_users",
    {
      title: "Search Example Users",
      description: `[Full description as shown above]`,
      inputSchema: UserSearchInputSchema,
      annotations: {
        readOnlyHint: true,
        destructiveHint: false,
        idempotentHint: true,
        openWorldHint: true
      }
    },
    async (params, ctx) => {
      try {
        const data = await makeApiRequest<UserSearchResponse>(
          "users/search",
          "GET",
          undefined,
          { q: params.query, limit: params.limit, offset: params.offset },
          ctx.mcpReq.signal
        );

        const users = data.users;
        const hasMore = data.total > params.offset + users.length;

        if (params.response_format === ResponseFormat.JSON) {
          const output = {
            total: data.total,
            count: users.length,
            offset: params.offset,
            users,
            has_more: hasMore,
            ...(hasMore ? { next_offset: params.offset + users.length } : {})
          };
          return {
            content: [{ type: "text", text: JSON.stringify(output, null, 2) }],
            structuredContent: output
          };
        }

        if (!users.length) {
          return {
            content: [{ type: "text", text: `No users found matching '${params.query}'` }]
          };
        }

        const lines = [`# User Search Results: '${params.query}'`, "",
          `Found ${data.total} users (showing ${users.length})`, ""];
        for (const user of users) {
          lines.push(`## ${user.name} (${user.id})`);
          lines.push(`- **Email**: ${user.email}`);
          if (user.team) lines.push(`- **Team**: ${user.team}`);
          lines.push("");
        }
        if (hasMore) {
          lines.push(`More results available: use offset=${params.offset + users.length}`);
        }

        let text = lines.join("\n");
        if (text.length > CHARACTER_LIMIT) {
          text = text.slice(0, CHARACTER_LIMIT) +
            "\n\n[Truncated. Use 'offset' or a narrower 'query' to see more.]";
        }

        return {
          content: [{ type: "text", text }]
        };
      } catch (error) {
        return {
          content: [{ type: "text", text: handleApiError(error) }],
          isError: true
        };
      }
    }
  );

  return server;
}

// For stdio (local):
function runStdio(): void {
  serveStdio(createServer);
  console.error("MCP server running via stdio");
}

// For streamable HTTP (remote):
function runHTTP(): void {
  const handler = createMcpHandler(createServer);
  const app = createMcpExpressApp();  // express() + express.json() + Host/Origin validation
  const nodeHandler = toNodeHandler(handler);
  app.all("/mcp", (req, res) => void nodeHandler(req, res, req.body));

  const port = parseInt(process.env.PORT || "3000");
  app.listen(port, "127.0.0.1", () => {
    console.error(`MCP server running on http://127.0.0.1:${port}/mcp`);
  });
}

if (!process.env.EXAMPLE_API_KEY) {
  console.error("ERROR: EXAMPLE_API_KEY environment variable is required");
  process.exit(1);
}

// Choose transport based on environment
if (process.env.TRANSPORT === "http") {
  runHTTP();
} else {
  runStdio();
}
```

---

## Advanced MCP Features

### Resource Registration

Expose data as resources for efficient, URI-based access. `registerResource` takes a name, a fixed URI or a `ResourceTemplate`, metadata, and a read callback:

```typescript
import { McpServer, ResourceTemplate } from "@modelcontextprotocol/server";

// Register a resource template; its list callback makes instances appear in resources/list
server.registerResource(
  "document",
  new ResourceTemplate("file://documents/{name}", {
    list: async () => {
      const documents = await getAvailableDocuments();
      return {
        resources: documents.map(doc => ({
          uri: `file://documents/${doc.name}`,
          name: doc.name,
          mimeType: "text/plain",
          description: doc.description
        }))
      };
    }
  }),
  {
    title: "Document Resource",
    description: "Access documents by name",
    mimeType: "text/plain"
  },
  // URI template variables arrive parsed as the second argument
  async (uri, { name }) => {
    const content = await loadDocument(String(name));
    return {
      contents: [{
        uri: uri.href,
        mimeType: "text/plain",
        text: content
      }]
    };
  }
);

// Register a resource at a fixed URI
server.registerResource(
  "config",
  "config://app",
  { title: "Application Config", mimeType: "application/json" },
  async uri => ({ contents: [{ uri: uri.href, text: JSON.stringify(await loadConfig()) }] })
);
```

Pass `{ list: undefined }` for a template whose instances cannot be enumerated. If a template variable becomes a filesystem path, resolve it with `realpath` and reject anything outside your root before reading.

**When to use Resources vs Tools:**
- **Resources**: For data access with simple URI-based parameters
- **Tools**: For complex operations requiring validation and business logic
- **Resources**: When data is relatively static or template-based
- **Tools**: When operations have side effects or complex workflows

### Transport Options

The TypeScript SDK supports two main transport mechanisms. Both take the same `createServer` factory.

#### Streamable HTTP (Recommended for Remote Servers)

```typescript
import { createMcpHandler } from "@modelcontextprotocol/server";
import { createMcpExpressApp } from "@modelcontextprotocol/express";
import { toNodeHandler } from "@modelcontextprotocol/node";

// Builds a fresh server from the factory for every request: stateless, scales horizontally
const handler = createMcpHandler(createServer);

const app = createMcpExpressApp();
const nodeHandler = toNodeHandler(handler);
app.all("/mcp", (req, res) => void nodeHandler(req, res, req.body));

app.listen(3000, "127.0.0.1");
```

- `createMcpHandler` holds no state between requests; create connection pools and caches once at module scope, not inside the factory
- It serves 2026-07-28 clients and 2025-era clients from the same factory by default, with no sessions for either. 2026-07-28 clients get a single JSON response unless a handler sends a notification mid-call; 2025-era clients get each response as a single SSE event
- `createMcpExpressApp()` validates `Host` and `Origin` headers for localhost binds (DNS rebinding protection). When deploying publicly, bind all interfaces and name the hosts you serve: `createMcpExpressApp({ host: "0.0.0.0", allowedHosts: ["mcp.example.com"] })`
- The handler verifies no tokens. Put `requireBearerAuth({ verifier })` from `@modelcontextprotocol/express` in front of the route; handlers then read `ctx.http?.authInfo`. See the [authorization docs](https://ts.sdk.modelcontextprotocol.io/v2/serving/authorization.md)
- On web-standard runtimes (Cloudflare Workers, Deno, Bun), `export default handler` is the whole mount, with no adapter packages; see the [web-standard docs](https://ts.sdk.modelcontextprotocol.io/v2/serving/web-standard.md) for Host/Origin validation there
- Hono and Fastify adapters are `@modelcontextprotocol/hono` and `@modelcontextprotocol/fastify`

#### stdio (For Local Integrations)

```typescript
import { serveStdio } from "@modelcontextprotocol/server/stdio";

serveStdio(createServer);
console.error("MCP server running via stdio");  // stderr: stdout carries the protocol
```

Never write to stdout from a stdio server (`console.log`): it corrupts the JSON-RPC stream. Use `console.error`.

**Transport selection:**
- **Streamable HTTP**: Web services, remote access, multiple clients
- **stdio**: Command-line tools, local development, subprocess integration

### Notification Support

Notify clients when server state changes. The handles returned by `registerTool`, `registerResource`, and `registerPrompt` send the matching `list_changed` notification automatically:

```typescript
const exportTool = server.registerTool(
  "example_export_data",
  { description: "Export data (requires an export-enabled plan)" },
  async () => ({ content: [{ type: "text", text: "Export started" }] })
);

exportTool.disable();  // Sends notifications/tools/list_changed
exportTool.enable();   // Sends it again; update() and remove() do too

// Explicit sends, when the change happens outside the registration API
server.sendToolListChanged();
server.sendResourceListChanged();
```

Behind `createMcpHandler` each request has its own server instance, so publish through the handler instead:

```typescript
handler.notify.toolsChanged();
handler.notify.resourcesChanged();
```

Use notifications sparingly - only when server capabilities genuinely change.

---

## Migrating a v1 Server

To move an existing `@modelcontextprotocol/sdk` server to v2, run the official codemod at the package root, then fix what it marks:

```bash
npx @modelcontextprotocol/codemod@latest v1-to-v2 .
grep -rn '@mcp-codemod-error' .   # Spots the codemod could not rewrite safely
npx tsc --noEmit
```

The codemod rewrites imports, `package.json`, registration calls, and handler context access. Check that `zod` ends up at `^4.2.0` or later, then run your formatter and tests. The full guide is at `https://ts.sdk.modelcontextprotocol.io/v2/migration/upgrade-to-v2.md`.

---

## Code Best Practices

### Code Composability and Reusability

Your implementation MUST prioritize composability and code reuse:

1. **Extract Common Functionality**:
   - Create reusable helper functions for operations used across multiple tools
   - Build shared API clients for HTTP requests instead of duplicating code
   - Centralize error handling logic in utility functions
   - Extract business logic into dedicated functions that can be composed
   - Extract shared markdown or JSON field selection & formatting functionality

2. **Avoid Duplication**:
   - NEVER copy-paste similar code between tools
   - If you find yourself writing similar logic twice, extract it into a function
   - Common operations like pagination, filtering, field selection, and formatting should be shared
   - Authentication/authorization logic should be centralized

## Building and Running

Always build your TypeScript code before running:

```bash
# Build the project
npm run build

# Run the server
npm start

# Development with auto-reload
npm run dev

# Exercise a stdio server's tools without a host
npx @modelcontextprotocol/inspector node dist/index.js
```

Always ensure `npm run build` completes successfully before considering the implementation complete.

For scripted tests, connect a `Client` from `@modelcontextprotocol/client` to the server in-process or over stdio; see `https://ts.sdk.modelcontextprotocol.io/v2/testing.md`.

## Quality Checklist

Before finalizing your Node/TypeScript MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names reflect natural task subdivisions
- [ ] Response formats optimize for agent context efficiency
- [ ] Human-readable identifiers used where appropriate
- [ ] Error messages guide agents toward correct usage

### Implementation Quality
- [ ] FOCUSED IMPLEMENTATION: Most important and valuable tools implemented
- [ ] All tools registered with `registerTool` inside the `createServer()` factory
- [ ] All tools include `title`, `description`, `inputSchema`, and `annotations`
- [ ] Annotations correctly set (readOnlyHint, destructiveHint, idempotentHint, openWorldHint)
- [ ] All `inputSchema` values are Zod object schemas (`z.strictObject` / `z.object`), not raw shapes
- [ ] All Zod schemas have proper constraints and descriptive error messages
- [ ] Tools with `outputSchema` return matching `structuredContent` on every successful call
- [ ] Results with `structuredContent` also include that data serialized as JSON in a text block
- [ ] All tools have comprehensive descriptions with explicit input/output types
- [ ] Error paths return `isError: true` with clear, actionable messages

### TypeScript Quality
- [ ] TypeScript interfaces are defined for all data structures
- [ ] Strict TypeScript is enabled in tsconfig.json
- [ ] No use of `any` type - use `unknown` or proper types instead
- [ ] All async functions have explicit Promise<T> return types
- [ ] Error handling uses proper type guards (e.g., `axios.isAxiosError`, `z.ZodError`)

### Advanced Features (where applicable)
- [ ] Resources registered for appropriate data endpoints
- [ ] Appropriate transport configured (`serveStdio` or `createMcpHandler`)
- [ ] HTTP servers keep Host/Origin validation and add bearer auth when exposed publicly
- [ ] Notifications implemented for dynamic server capabilities
- [ ] `ctx.mcpReq.signal` passed to long-running upstream requests

### Project Configuration
- [ ] Package.json depends on `@modelcontextprotocol/server` (not `@modelcontextprotocol/sdk`) and `zod` `^4.2.0` or later
- [ ] No imports from `@modelcontextprotocol/sdk/...` or `zod/v3`
- [ ] Build script produces working JavaScript in dist/ directory
- [ ] Main entry point is properly configured as dist/index.js
- [ ] Server name follows format: `{service}-mcp-server`
- [ ] tsconfig.json properly configured with strict mode

### Code Quality
- [ ] Pagination is properly implemented where applicable
- [ ] Large responses check CHARACTER_LIMIT constant and truncate with clear messages
- [ ] Filtering options are provided for potentially large result sets
- [ ] All network operations handle timeouts and connection errors gracefully
- [ ] Common functionality is extracted into reusable functions
- [ ] Return types are consistent across similar operations

### Testing and Build
- [ ] `npm run build` completes successfully without errors
- [ ] dist/index.js created and runs with `node dist/index.js`
- [ ] All imports resolve correctly
- [ ] Tools list and run in MCP Inspector: `npx @modelcontextprotocol/inspector node dist/index.js`
- [ ] Sample tool calls work as expected
