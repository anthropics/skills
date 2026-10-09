# Node/TypeScript MCP Server Implementation Guide (SDK v2)

This guide covers building MCP servers with **v2 of the MCP TypeScript SDK** (`@modelcontextprotocol/server`), the current stable release. If the project already depends on the v1 package `@modelcontextprotocol/sdk`, use the [v1 guide](./node_mcp_server.md) or migrate first (see [Migrating a v1 Server](#migrating-a-v1-server)).

Code patterns are adapted from the [MCP TypeScript SDK examples](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples) (Apache-2.0). The full v2 documentation index is `https://ts.sdk.modelcontextprotocol.io/v2/llms.txt`; every page is also served as markdown at its `.md` URL.

---

## Quick Reference

### Install

```bash
npm install @modelcontextprotocol/server zod
npm install @modelcontextprotocol/express @modelcontextprotocol/node express   # Streamable HTTP only
npm install -D @modelcontextprotocol/client typescript tsx @types/node @types/express
```

### A Server in One Screen

```typescript
import { McpServer } from "@modelcontextprotocol/server";
import { serveStdio } from "@modelcontextprotocol/server/stdio";
import * as z from "zod/v4";

function createServer(): McpServer {
  const server = new McpServer({ name: "example-mcp-server", version: "1.0.0" });

  server.registerTool(
    "example_greet",
    {
      title: "Greet",
      description: "Greet someone by name",
      inputSchema: z.object({ name: z.string().describe("Who to greet") }),
      annotations: { readOnlyHint: true }
    },
    async ({ name }) => ({ content: [{ type: "text", text: `Hello, ${name}!` }] })
  );

  return server;
}

serveStdio(createServer);
console.error("example-mcp-server running on stdio"); // stderr: stdout carries the protocol
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

Do not use imports from `@modelcontextprotocol/sdk/...`, raw-shape schemas, Zod 3 or `zod/v3`, or hand-wired `StreamableHTTPServerTransport` instances in a v2 server.

---

## Project Setup

```
{service}-mcp-server/
├── package.json
├── tsconfig.json
├── README.md
├── src/
│   ├── index.ts          # createServer() factory and transport selection
│   ├── api.ts            # Upstream API client and error messages
│   ├── tools/            # One registerXxxTools(server) function per domain
│   └── constants.ts      # API_BASE_URL, CHARACTER_LIMIT
├── scripts/
│   └── smoke.ts          # Self-check client (see Verify Your Server)
└── dist/                 # Build output (entry point: dist/index.js)
```

Name the package and server `{service}-mcp-server` (lowercase, hyphens, no version numbers), e.g. `github-mcp-server`, `jira-mcp-server`.

### package.json

```json
{
  "name": "{service}-mcp-server",
  "version": "1.0.0",
  "description": "MCP server for the {Service} API",
  "type": "module",
  "bin": { "{service}-mcp-server": "dist/index.js" },
  "files": ["dist"],
  "scripts": {
    "build": "tsc",
    "start": "node dist/index.js",
    "dev": "tsx watch src/index.ts",
    "smoke": "tsx scripts/smoke.ts"
  },
  "engines": { "node": ">=20" },
  "dependencies": {
    "@modelcontextprotocol/express": "^2.0.2",
    "@modelcontextprotocol/node": "^2.1.1",
    "@modelcontextprotocol/server": "^2.3.1",
    "express": "^5.1.0",
    "zod": "^4.2.0"
  },
  "devDependencies": {
    "@modelcontextprotocol/client": "^2.3.1",
    "@types/express": "^5.0.0",
    "@types/node": "^24.0.0",
    "tsx": "^4.19.2",
    "typescript": "^5.9.3"
  }
}
```

- `bin` plus the `#!/usr/bin/env node` line at the top of `src/index.ts` let hosts launch the server with `npx -y {service}-mcp-server`
- A stdio-only server can drop `express`, `@types/express`, and the two adapter packages
- Keep `zod` at `^4.2.0` or later: v2 does not support Zod 3, and Zod 4.0–4.1 drops `.describe()` text from the advertised schemas

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
    "sourceMap": true
  },
  "include": ["src/**/*"]
}
```

---

## The Server Factory

Write a `createServer()` function that builds a fresh `McpServer` and registers every tool, resource, and prompt on it. You never call it yourself: the transport entry points do.

- `serveStdio(createServer)` calls it once for the stdio connection
- `createMcpHandler(createServer)` calls it once **per HTTP request**, so the HTTP server keeps no state between requests and scales horizontally as-is
- Register everything inside the factory, never on a shared instance outside it
- Keep the factory cheap: create API clients, connection pools, caches, and configuration once at module scope and close over them
- Behind `createMcpHandler`, the factory receives the request context: `createMcpHandler(({ authInfo }) => ...)` builds an instance for one authenticated caller

One file can serve both transports; the [complete example](#complete-example) picks one from the `TRANSPORT` environment variable.

## Calling the Upstream API

Put the upstream API client at module scope, in one `apiRequest` helper that every tool calls. Node 20+ has `fetch` built in. The core of the [complete example](#complete-example)'s helper:

```typescript
const response = await fetch(url, {
  headers: { Authorization: `Bearer ${API_KEY}`, Accept: "application/json" },
  // Aborts when the client cancels the call, or after 30 seconds
  signal: AbortSignal.any([signal, AbortSignal.timeout(30_000)])
});
if (!response.ok) throw new Error(httpErrorMessage(response.status));
```

- Send whatever the API requires (API key, `User-Agent`, version header) here, in one place
- Tool handlers pass `ctx.mcpReq.signal`, so a cancelled call also cancels its upstream request
- Map HTTP statuses and timeouts to messages that say how to recover (`httpErrorMessage` in the complete example): "Rate limit exceeded. Wait a minute before making more requests."
- Tool handlers can let these errors propagate: the SDK turns anything a tool handler throws into an `isError: true` result whose text is the error's `message`

---

## Designing Tools

### Names and Descriptions

- Use snake_case, action-oriented names with a service prefix: `slack_send_message`, `github_create_issue`, `asana_list_tasks`
- The `description` is what the model reads to decide when and how to call the tool. Say what it does, what it returns, when to use a sibling tool instead, and give one or two example requests. JSDoc comments are not extracted
- Give every tool a `title` (display name), `description`, `inputSchema` (if it takes arguments), and `annotations`

### Annotations

Annotations are hints for clients, for example to auto-approve read-only tools or to confirm destructive ones. They never change how the SDK runs the tool.

| Annotation | Set to `true` when the tool... |
|---|---|
| `readOnlyHint` | does not modify anything |
| `destructiveHint` | may delete or overwrite data |
| `idempotentHint` | can be repeated with the same arguments with no extra effect |
| `openWorldHint` | talks to an external system (most API tools) |

### Input Schemas

`inputSchema` is a Zod object schema: `z.object({...})`, or `z.strictObject({...})` to reject unknown arguments. From that one schema the SDK derives the JSON Schema clients see, validates arguments before your handler runs, and infers the handler's argument types (no annotation needed).

```typescript
const SearchInput = z.strictObject({
  query: z.string().min(2).max(200).describe("Text to match against user names and emails"),
  limit: z.number().int().min(1).max(100).default(20).describe("Maximum number of users to return"),
  offset: z.number().int().min(0).default(0).describe("Number of matches to skip, for pagination"),
  response_format: z.enum(ResponseFormat).default(ResponseFormat.MARKDOWN)
    .describe("'markdown' for readable text, 'json' for structured data")
});
```

- `.describe()` text becomes the argument's JSON Schema `description`, the only documentation the model gets for it
- Fields with `.default()` are optional for the caller and always present in the handler's arguments
- Arguments that fail validation never reach the handler; the client gets an `isError: true` result such as `Input validation error: Invalid arguments for tool example_search_users: query: Too small: expected string to have >=2 characters`
- Zod 4 replaced some v3 APIs: `z.strictObject({...})` instead of `.strict()`, `z.enum(MyTsEnum)` instead of `z.nativeEnum`, and `z.email()` / `z.url()` / `z.uuid()` instead of `z.string().email()` and similar

### Output: Markdown, JSON, and structuredContent

Let the caller choose the format with a `response_format` argument:

- **Markdown** (default): readable text for the model. Headers and lists, human-readable dates, display names with IDs in parentheses, no verbose metadata
- **JSON**: complete data for programmatic use, with consistent field names

When a result includes `structuredContent`, the spec says it SHOULD also include the same data serialized as JSON in a text block. So:

- In JSON mode, return the data as `structuredContent` and its `JSON.stringify` as the text
- In Markdown mode, return only the Markdown text
- Declare `outputSchema` only on tools whose output is always JSON. With an `outputSchema`, every successful result must include matching `structuredContent`, or the SDK replaces it with an output validation error
- The advertised `outputSchema` disallows extra fields, so build `structuredContent` from the schema, e.g. `UserSchema.parse(raw)`, which also validates the upstream data

### Pagination

List and search tools take `limit` and `offset` and return where the next page starts:

```typescript
const page = {
  total: data.total,
  count: users.length,
  offset,
  users,
  has_more: hasMore,
  ...(hasMore ? { next_offset: nextOffset } : {})
};
```

In Markdown mode, end the text with how to get more, e.g. `More results: call again with offset=20.`

### Character Limit

Cap responses with a `CHARACTER_LIMIT` (25,000 characters is a good default). Stay under it by returning **fewer items**, never by cutting text: `next_offset` then points at the first item left out, and the JSON text still matches `structuredContent`.

```typescript
let users = data.users;
while (users.length > 1 && JSON.stringify(users).length > CHARACTER_LIMIT) {
  users = users.slice(0, Math.ceil(users.length / 2));
}
const nextOffset = offset + users.length;
const hasMore = data.total > nextOffset;
```

### Errors

MCP has two error channels:

- **Tool errors** are tool results with `isError: true`. The model reads them, so the text should say how to recover. A tool handler produces them by returning `isError: true`, or by throwing: the thrown error's `message` becomes the result text
- **Protocol errors** are JSON-RPC error responses handled by the client application; the model never sees them. Resource and prompt callbacks have no `isError` channel, so they throw `ProtocolError` (see [Resources and Prompts](#resources-and-prompts))

---

## Complete Example

One file, two tools, both transports. `example_search_users` shows pagination, the character limit, and the two output formats; `example_get_user` shows an `outputSchema`.

```typescript
#!/usr/bin/env node
/**
 * MCP server for the Example API.
 * Serves stdio by default, Streamable HTTP when TRANSPORT=http.
 */
import { createMcpExpressApp } from "@modelcontextprotocol/express";
import { toNodeHandler } from "@modelcontextprotocol/node";
import { createMcpHandler, McpServer } from "@modelcontextprotocol/server";
import { serveStdio } from "@modelcontextprotocol/server/stdio";
import * as z from "zod/v4";

const API_BASE_URL = "https://api.example.com/v1";
const API_KEY = process.env.EXAMPLE_API_KEY;
const CHARACTER_LIMIT = 25_000;

if (!API_KEY) {
  console.error("EXAMPLE_API_KEY environment variable is required");
  process.exit(1);
}

// ---- Upstream API client: module scope, shared by every server instance ----

async function apiRequest<T>(
  path: string,
  params: Record<string, string | number>,
  signal: AbortSignal
): Promise<T> {
  const url = new URL(`${API_BASE_URL}/${path}`);
  for (const [key, value] of Object.entries(params)) url.searchParams.set(key, String(value));

  let response: Response;
  try {
    response = await fetch(url, {
      headers: { Authorization: `Bearer ${API_KEY}`, Accept: "application/json" },
      // Aborts when the client cancels the call, or after 30 seconds
      signal: AbortSignal.any([signal, AbortSignal.timeout(30_000)])
    });
  } catch (error) {
    if (error instanceof DOMException && error.name === "TimeoutError") {
      throw new Error("The Example API did not respond within 30 seconds. Try again, or narrow the query.");
    }
    throw error;
  }
  if (!response.ok) throw new Error(httpErrorMessage(response.status));
  return (await response.json()) as T;
}

// Thrown errors reach the model as the tool result's text, so say how to recover
function httpErrorMessage(status: number): string {
  switch (status) {
    case 401:
      return "The Example API rejected the API key. Check that EXAMPLE_API_KEY is valid.";
    case 403:
      return "Permission denied: this API key cannot access that resource.";
    case 404:
      return "Not found. Check the ID; example_search_users returns valid user IDs.";
    case 429:
      return "Rate limit exceeded. Wait a minute before making more requests.";
    default:
      return `The Example API returned HTTP ${status}.`;
  }
}

// ---- Schemas and formatting ----

enum ResponseFormat {
  MARKDOWN = "markdown",
  JSON = "json"
}

const UserSchema = z.object({
  id: z.string(),
  name: z.string(),
  email: z.string(),
  team: z.string().optional(),
  active: z.boolean()
});

type User = z.infer<typeof UserSchema>;

interface UserPage {
  users: User[];
  total: number;
}

function formatUser(user: User): string {
  const lines = [`## ${user.name} (${user.id})`, `- Email: ${user.email}`];
  if (user.team) lines.push(`- Team: ${user.team}`);
  if (!user.active) lines.push("- Inactive");
  return lines.join("\n");
}

// ---- Server factory: serveStdio calls it per connection, createMcpHandler per HTTP request ----

function createServer(): McpServer {
  const server = new McpServer({ name: "example-mcp-server", version: "1.0.0" });

  server.registerTool(
    "example_search_users",
    {
      title: "Search Users",
      description: `Search Example users by name or email.

Returns one page of matches. When more matches exist, the result says so and gives next_offset; call again with that offset for the next page.

Examples:
  - "Find people on the marketing team" -> query="marketing"
  - "Look up john@acme.com" -> query="john@acme.com"
Use example_get_user instead when you already have a user ID.`,
      inputSchema: z.strictObject({
        query: z.string().min(2).max(200).describe("Text to match against user names and emails"),
        limit: z.number().int().min(1).max(100).default(20).describe("Maximum number of users to return"),
        offset: z.number().int().min(0).default(0).describe("Number of matches to skip, for pagination"),
        response_format: z.enum(ResponseFormat).default(ResponseFormat.MARKDOWN)
          .describe("'markdown' for readable text, 'json' for structured data")
      }),
      annotations: { readOnlyHint: true, destructiveHint: false, idempotentHint: true, openWorldHint: true }
    },
    async ({ query, limit, offset, response_format }, ctx) => {
      const data = await apiRequest<UserPage>("users/search", { q: query, limit, offset }, ctx.mcpReq.signal);

      // Stay under CHARACTER_LIMIT by returning fewer users; next_offset then points at the first one left out
      let users = data.users;
      while (users.length > 1 && JSON.stringify(users).length > CHARACTER_LIMIT) {
        users = users.slice(0, Math.ceil(users.length / 2));
      }
      const nextOffset = offset + users.length;
      const hasMore = data.total > nextOffset;
      const page = {
        total: data.total,
        count: users.length,
        offset,
        users,
        has_more: hasMore,
        ...(hasMore ? { next_offset: nextOffset } : {})
      };

      if (response_format === ResponseFormat.JSON) {
        return {
          content: [{ type: "text", text: JSON.stringify(page, null, 2) }],
          structuredContent: page
        };
      }
      if (users.length === 0) {
        return { content: [{ type: "text", text: `No users match '${query}'. Try a shorter or different query.` }] };
      }
      const lines = [`# Users matching '${query}'`, `Showing ${users.length} of ${data.total}.`, ""];
      lines.push(users.map(formatUser).join("\n\n"));
      if (hasMore) lines.push("", `More results: call again with offset=${nextOffset}.`);
      return { content: [{ type: "text", text: lines.join("\n") }] };
    }
  );

  server.registerTool(
    "example_get_user",
    {
      title: "Get User",
      description: "Get one Example user by ID. Use example_search_users to find IDs.",
      inputSchema: z.strictObject({
        user_id: z.string().min(1).describe("User ID, e.g. 'U123456789'")
      }),
      outputSchema: UserSchema,
      annotations: { readOnlyHint: true, destructiveHint: false, idempotentHint: true, openWorldHint: true }
    },
    async ({ user_id }, ctx) => {
      const raw = await apiRequest<unknown>(`users/${encodeURIComponent(user_id)}`, {}, ctx.mcpReq.signal);
      const user = UserSchema.parse(raw); // Validates the upstream data and drops fields outside the schema
      return {
        content: [{ type: "text", text: JSON.stringify(user, null, 2) }],
        structuredContent: user
      };
    }
  );

  return server;
}

// ---- Transport selection ----

if (process.env.TRANSPORT === "http") {
  const handler = createMcpHandler(createServer);
  const app = createMcpExpressApp(); // express.json() plus Host/Origin checks for localhost
  const nodeHandler = toNodeHandler(handler);
  app.all("/mcp", (req, res) => void nodeHandler(req, res, req.body));

  const port = Number(process.env.PORT ?? 3000);
  app.listen(port, "127.0.0.1", () => {
    console.error(`example-mcp-server listening on http://127.0.0.1:${port}/mcp`);
  });
} else {
  serveStdio(createServer);
  console.error("example-mcp-server running on stdio");
}
```

---

## Serving

### stdio (Local Servers)

`serveStdio(createServer)` reads requests on stdin and writes responses on stdout. Never write to stdout yourself: one `console.log` corrupts the JSON-RPC stream. Log with `console.error`.

### Streamable HTTP (Remote Servers)

`createMcpHandler(createServer)` returns a web-standard handler; `toNodeHandler` adapts it to Express:

```typescript
const handler = createMcpHandler(createServer);
const app = createMcpExpressApp();
const nodeHandler = toNodeHandler(handler);
app.all("/mcp", (req, res) => void nodeHandler(req, res, req.body));
app.listen(3000, "127.0.0.1");
```

- It serves clients on the 2026-07-28 protocol revision and older 2025-era clients from the same factory, with no sessions for either
- `createMcpExpressApp()` installs `express.json()` and validates `Host` and `Origin` headers on localhost binds, which blocks DNS rebinding attacks. When binding all interfaces, name the hosts you serve: `createMcpExpressApp({ host: "0.0.0.0", allowedHosts: ["mcp.example.com"] })`
- Hono and Fastify adapters are `@modelcontextprotocol/hono` and `@modelcontextprotocol/fastify`
- On web-standard runtimes (Cloudflare Workers, Deno, Bun), `export default handler` is the whole mount; put Host/Origin checks in front as described in the [web-standard docs](https://ts.sdk.modelcontextprotocol.io/v2/serving/web-standard.md)

### Authentication

The handler verifies no tokens. For a server exposed beyond localhost, put `requireBearerAuth` in front of the route:

```typescript
import { createMcpExpressApp, requireBearerAuth, type OAuthTokenVerifier } from "@modelcontextprotocol/express";
import { OAuthError, OAuthErrorCode, type AuthInfo } from "@modelcontextprotocol/server";

const serverUrl = new URL("https://mcp.example.com/mcp");

const verifier: OAuthTokenVerifier = {
  async verifyAccessToken(token): Promise<AuthInfo> {
    // Replace with JWT verification or token introspection against your authorization server
    const claims = await verifyWithYourAuthServer(token);
    if (!claims) throw new OAuthError(OAuthErrorCode.InvalidToken, "Unknown or expired token");
    return {
      token,
      clientId: claims.clientId,
      scopes: claims.scopes,
      expiresAt: claims.exp, // Required: tokens without an expiry are rejected
      resource: new URL(claims.aud) // Compared with expectedResource below
    };
  }
};

const app = createMcpExpressApp({ host: "0.0.0.0", allowedHosts: ["mcp.example.com"] });
const requireAuth = requireBearerAuth({ verifier, requiredScopes: ["mcp"], expectedResource: serverUrl });
app.all("/mcp", requireAuth, (req, res) => void nodeHandler(req, res, req.body));
```

- `expectedResource` accepts only tokens issued for this server, so a token meant for another service is refused
- The verified `AuthInfo` reaches the factory as `createMcpHandler(({ authInfo }) => ...)` and tool handlers as `ctx.http?.authInfo` (undefined on stdio)
- Serving OAuth discovery metadata and per-tool scopes are covered by the [oauth](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/oauth) and [scoped-tools](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/scoped-tools) examples and the [authorization docs](https://ts.sdk.modelcontextprotocol.io/v2/serving/authorization.md)

**Transport selection:** stdio for local tools a host launches as a subprocess; Streamable HTTP for remote services and multiple clients.

---

## Resources and Prompts

Resources expose read-only data at a URI that the client application reads and attaches as context. Prompts are message templates a user invokes by name. Tools are for anything the model should call, including operations with side effects.

```typescript
import { completable, ProtocolError, ProtocolErrorCode, ResourceNotFoundError, ResourceTemplate } from "@modelcontextprotocol/server";

// A resource at a fixed URI
server.registerResource(
  "example-teams",
  "example://teams",
  { title: "Teams", description: "Every team in the Example workspace", mimeType: "application/json" },
  async (uri, ctx) => {
    const teams = await apiRequest<unknown>("teams", {}, ctx.mcpReq.signal);
    return { contents: [{ uri: uri.href, mimeType: "application/json", text: JSON.stringify(teams) }] };
  }
);

// A URI template: the matched variables arrive as the second argument
server.registerResource(
  "example-user",
  new ResourceTemplate("example://users/{userId}", { list: undefined }),
  { title: "User profile", description: "One Example user by ID", mimeType: "application/json" },
  async (uri, { userId }, ctx) => {
    if (!/^U\d+$/.test(String(userId))) {
      throw new ProtocolError(ProtocolErrorCode.InvalidParams, `User IDs look like U123, got "${userId}"`);
    }
    const user = await apiRequest<unknown>(`users/${userId}`, {}, ctx.mcpReq.signal).catch(() => null);
    if (!user) throw new ResourceNotFoundError(uri.href);
    return { contents: [{ uri: uri.href, mimeType: "application/json", text: JSON.stringify(user) }] };
  }
);

// A prompt; completable() lets clients autocomplete the argument as the user types
const TEAMS = ["engineering", "marketing", "sales"];

server.registerPrompt(
  "example_team_report",
  {
    title: "Team report",
    description: "Summarize who is on a team",
    argsSchema: z.object({
      team: completable(z.string().describe("Team name"), value => TEAMS.filter(team => team.startsWith(value)))
    })
  },
  async ({ team }) => ({
    messages: [
      {
        role: "user",
        content: { type: "text", text: `Use example_search_users to find everyone on the ${team} team, then summarize the team in a short table.` }
      }
    ]
  })
);
```

- Give a template a `list` callback that returns `{ resources: [...] }` to make its instances appear in `resources/list`; `{ list: undefined }` leaves them readable but unlisted
- If a template variable becomes a filesystem path, resolve it with `realpath` and reject anything outside your root before reading

## Notifications

The handles returned by `registerTool`, `registerResource`, and `registerPrompt` send the matching `list_changed` notification when you change them:

```typescript
const exportTool = server.registerTool(
  "example_export_data",
  { description: "Export workspace data (export-enabled plans only)" },
  async () => ({ content: [{ type: "text", text: "Export started" }] })
);
exportTool.disable(); // Sends notifications/tools/list_changed
exportTool.enable(); // So do enable(), update(), and remove()
```

Behind `createMcpHandler` each request has its own server instance, so publish changes through the handler instead: `handler.notify.toolsChanged()`, `handler.notify.resourcesChanged()`. Send notifications only when the server's capabilities actually change.

---

## Verify Your Server

Write a self-check script that starts the built server, calls its tools as a client would, and exits non-zero on any failure. Run it after every change, along with `npm run build`; adapt the tool names and assertions to your server.

```typescript
/**
 * Self-check: starts the built server over stdio, calls its tools, and exits non-zero on any failure.
 * Run with: npm run build && npm run smoke
 */
import { strict as assert } from "node:assert";
import { Client } from "@modelcontextprotocol/client";
import { getDefaultEnvironment, StdioClientTransport } from "@modelcontextprotocol/client/stdio";

const client = new Client({ name: "smoke-test", version: "1.0.0" });
await client.connect(
  new StdioClientTransport({
    command: "node",
    args: ["dist/index.js"],
    // The child gets only a safe default environment; pass the server's own variables explicitly
    env: { ...getDefaultEnvironment(), EXAMPLE_API_KEY: process.env.EXAMPLE_API_KEY ?? "" }
  })
);

const { tools } = await client.listTools();
assert.deepEqual(tools.map(tool => tool.name).sort(), ["example_get_user", "example_search_users"]);

const search = await client.callTool({
  name: "example_search_users",
  arguments: { query: "john", limit: 5, response_format: "json" }
});
assert.ok(!search.isError, `search failed: ${JSON.stringify(search.content)}`);
const page = search.structuredContent as { users: { id: string }[]; total: number };
assert.ok(Array.isArray(page.users), "search should return a users array");

if (page.users.length > 0) {
  const user = await client.callTool({ name: "example_get_user", arguments: { user_id: page.users[0].id } });
  assert.ok(!user.isError, `get_user failed: ${JSON.stringify(user.content)}`);
}

// Invalid arguments must come back as a tool error the model can read
const invalid = await client.callTool({ name: "example_search_users", arguments: { query: "j" } });
assert.equal(invalid.isError, true, "a one-character query should be rejected");

await client.close();
console.error("Smoke test passed");
```

- Call read-only tools with realistic arguments; check that one invalid input is rejected
- `StdioClientTransport` gives the child process only a safe default environment (`PATH`, `HOME`, and similar), so pass API keys and other settings in `env`
- For an HTTP server, start it (`TRANSPORT=http npm start`) and connect with `new StreamableHTTPClientTransport(new URL("http://127.0.0.1:3000/mcp"))` from `@modelcontextprotocol/client` instead
- For manual exploration, `npx @modelcontextprotocol/inspector node dist/index.js` opens an interactive UI
- More test patterns, including in-process tests without a subprocess: `https://ts.sdk.modelcontextprotocol.io/v2/testing.md`

---

## More Features

Each linked example is a runnable server and client pair from the SDK repository:

| To... | See |
|---|---|
| Report progress, send log messages, and handle cancellation in long-running tools | [streaming](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/streaming) |
| Ask the user for input mid-call (elicitation) | [elicitation](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/elicitation) |
| Notify subscribed clients when resources change | [subscriptions](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/subscriptions) |
| Add OAuth login (authorization code flow) | [oauth](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/oauth) |
| Accept machine-to-machine OAuth (client credentials) | [oauth-client-credentials](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/oauth-client-credentials) |
| Require different scopes for different tools | [scoped-tools](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/scoped-tools) |
| Serve on Hono or another web-standard runtime | [hono](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/hono), [bearer-auth-web](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/bearer-auth-web) |
| Run sessionful 2025-era HTTP deployments | [standalone-get](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/standalone-get), [sse-polling](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/sse-polling) |
| See every server feature in one reference server | [todos-server](https://github.com/modelcontextprotocol/typescript-sdk/tree/main/examples/todos-server) |

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

## Quality Checklist

### Tool Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names are snake_case with a service prefix
- [ ] Every tool has a `title`, a `description` that says when to use it, and correct `annotations`
- [ ] Inputs are Zod object schemas with constraints and `.describe()` text; `z.strictObject` where unknown arguments should be rejected
- [ ] List and search tools paginate with `limit` / `offset` and return `next_offset`
- [ ] Responses stay under `CHARACTER_LIMIT` by returning fewer items
- [ ] Results with `structuredContent` also include that data serialized as JSON text; `outputSchema` only on always-JSON tools
- [ ] Error messages say what went wrong and how to recover

### Implementation
- [ ] Everything is registered inside the `createServer()` factory; shared clients live at module scope
- [ ] Upstream requests pass `ctx.mcpReq.signal` and have a timeout
- [ ] Strict TypeScript; no `any`; upstream data validated where it feeds `structuredContent`
- [ ] Nothing writes to stdout in a stdio server
- [ ] HTTP servers keep Host/Origin validation, and add bearer auth when exposed beyond localhost

### Project
- [ ] `package.json` depends on `@modelcontextprotocol/server` (not `@modelcontextprotocol/sdk`) and `zod` `^4.2.0` or later
- [ ] No imports from `@modelcontextprotocol/sdk/...` or `zod/v3`
- [ ] `bin` points at `dist/index.js`, and `src/index.ts` starts with `#!/usr/bin/env node`

### Verification
- [ ] `npm run build` completes without errors
- [ ] The self-check script passes against the built server
