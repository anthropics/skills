# MCP Protocol Deep Dive

## What Is MCP

The Model Context Protocol (MCP) is an open, JSON-RPC 2.0-based protocol that standardizes how
LLM applications (clients/hosts) connect to context providers and tool servers. Anthropic released
it in November 2024. In December 2025 it moved to the Linux Foundation's Agentic AI Foundation for
neutral governance. Every major AI platform — OpenAI, Google, Microsoft — has adopted it.

The core premise: instead of every AI application building bespoke integrations with every data
source and tool, MCP provides a universal adapter layer. An MCP server built once works with
Claude Desktop, Cursor, Windsurf, VS Code Copilot, and any other MCP-compatible host.

## Protocol Foundation: JSON-RPC 2.0

MCP uses JSON-RPC 2.0 as its wire format. Every message is one of:

**Request** (expects response):
```json
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "method": "tools/call",
  "params": { "name": "get_weather", "arguments": { "city": "NYC" } }
}
```

**Response** (reply to request):
```json
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "result": { "content": [{ "type": "text", "text": "72°F, sunny" }] }
}
```

**Error Response**:
```json
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "error": { "code": -32600, "message": "Invalid Request", "data": "..." }
}
```

**Notification** (no response expected):
```json
{
  "jsonrpc": "2.0",
  "method": "notifications/tools/list_changed"
}
```

Standard JSON-RPC error codes apply: -32700 (Parse error), -32600 (Invalid Request), -32601
(Method not found), -32602 (Invalid params), -32603 (Internal error). MCP-specific tool errors
are returned inside the `result` object with `isError: true`, not as JSON-RPC error responses.

## Architecture: Client-Server-Host Model

MCP defines three roles:

- **Host**: The LLM application (Claude Desktop, Cursor). Hosts contain one or more clients and
  present the LLM interface to users.
- **Client**: Lives inside the host; maintains a 1:1 connection with one MCP server. Handles
  protocol, transport, and capability negotiation.
- **Server**: A process (local or remote) that exposes tools, resources, and/or prompts. Servers
  are stateless or stateful depending on transport choice.

One host can connect to many servers via many clients simultaneously. This is how Claude Desktop
aggregates tools from filesystem, GitHub, PostgreSQL, and custom servers at once.

## Protocol Lifecycle

Every MCP session follows a strict four-phase lifecycle:

### Phase 1: Initialization

Client sends `initialize` request:
```json
{
  "method": "initialize",
  "params": {
    "protocolVersion": "2025-03-26",
    "capabilities": {
      "roots": { "listChanged": true },
      "sampling": {}
    },
    "clientInfo": { "name": "claude-desktop", "version": "1.0" }
  }
}
```

Server responds with its own capabilities:
```json
{
  "result": {
    "protocolVersion": "2025-03-26",
    "capabilities": {
      "tools": { "listChanged": true },
      "resources": { "subscribe": true, "listChanged": true },
      "prompts": { "listChanged": true },
      "logging": {}
    },
    "serverInfo": { "name": "my-server", "version": "1.0.0" }
  }
}
```

### Phase 2: Initialized Notification

Client sends `notifications/initialized` to signal it is ready. Server must not send requests
before this notification arrives.

### Phase 3: Operation

Normal bidirectional operation. Client makes requests (tools/list, tools/call, resources/list,
resources/read, prompts/list, prompts/get, sampling/createMessage). Server sends notifications
(list_changed, resources/updated, progress, cancelled, logging).

### Phase 4: Shutdown

Either side can close the transport. No explicit shutdown message is required.

## Capabilities Negotiation

Capabilities are declared during initialization and act as feature flags. Neither side should
use features the other did not declare:

| Capability | Direction | Meaning |
|---|---|---|
| `tools` | Server | Exposes tools/list and tools/call |
| `tools.listChanged` | Server | Will send notifications/tools/list_changed |
| `resources` | Server | Exposes resources/list and resources/read |
| `resources.subscribe` | Server | Supports resources/subscribe |
| `resources.listChanged` | Server | Will send notifications/resources/list_changed |
| `prompts` | Server | Exposes prompts/list and prompts/get |
| `prompts.listChanged` | Server | Will send notifications/prompts/list_changed |
| `logging` | Server | Accepts logging/setLevel |
| `sampling` | Client | Can handle sampling/createMessage requests |
| `roots` | Client | Provides roots/list |
| `roots.listChanged` | Client | Will send notifications/roots/list_changed |

## Transport Mechanisms

### 1. stdio Transport

**How it works**: The host launches the MCP server as a subprocess. Communication uses
`stdin`/`stdout`. The server reads JSON-RPC messages from stdin and writes responses to stdout.
Stderr is for logging ONLY — any non-JSON-RPC content on stdout breaks the protocol.

**Use when**: Local servers, developer tools, Claude Desktop integration, subprocess execution.
This is the overwhelmingly dominant transport for tool servers today.

**Configuration in Claude Desktop** (`claude_desktop_config.json`):
```json
{
  "mcpServers": {
    "filesystem": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-filesystem", "/Users/me/Documents"],
      "env": { "API_KEY": "secret" }
    }
  }
}
```

**Security**: Inherits the process security context. API keys passed via env vars. No network
exposure. Single-client by design.

### 2. Streamable HTTP Transport (Current Standard for Remote)

Introduced in the 2025-03-26 spec, replacing the older HTTP+SSE transport. This is the
recommended transport for any remote/multi-client server.

**How it works**:
- All messages go to a single HTTP endpoint (e.g., `POST /mcp`).
- Client sends JSON-RPC as `application/json` POST body.
- Server can respond with `application/json` (simple response) or upgrade to
  `text/event-stream` (SSE stream) for streaming responses or server-initiated messages.
- Client can also GET the endpoint to open a persistent SSE channel for server-initiated messages.

**Stateless mode** (recommended for scalability): Create a new transport instance per request.
No session state on the server.

**Stateful mode**: Use `sessionIdGenerator` to maintain session identity across requests,
enabling server-initiated notifications.

**TypeScript implementation**:
```typescript
import { StreamableHTTPServerTransport } from "@modelcontextprotocol/sdk/server/streamableHttp.js";
import express from "express";

const app = express();
app.use(express.json());

app.post('/mcp', async (req, res) => {
  const transport = new StreamableHTTPServerTransport({
    sessionIdGenerator: undefined,  // undefined = stateless
    enableJsonResponse: true        // return JSON not SSE when possible
  });
  res.on('close', () => transport.close());
  await server.connect(transport);
  await transport.handleRequest(req, res, req.body);
});
```

**Security**: Supports standard HTTP auth (Bearer tokens, API keys in headers). OAuth 2.1 is
the mandated auth mechanism for public-facing remote servers (see Security guide).

**DNS rebinding protection**: Local HTTP servers must validate the `Origin` header and bind to
`127.0.0.1`, not `0.0.0.0`.

### 3. Legacy HTTP+SSE Transport (Deprecated)

Used a separate POST endpoint for client-to-server messages and a GET SSE endpoint for
server-to-client messages. The 2025-03-26 spec replaced this with Streamable HTTP.
Avoid for new implementations.

### 4. WebSocket

Not in the official specification but supported by some ecosystem implementations. Provides
true bidirectional streaming. The Python SDK exposes a WebSocket transport option.
Use only when true bidirectional real-time communication is required and cannot be achieved
with Streamable HTTP.

### Transport Selection Matrix

| Need | Transport |
|---|---|
| Local tool, single user, Claude Desktop | stdio |
| Remote API, multiple clients | Streamable HTTP |
| Cloud deployment, scalable | Streamable HTTP (stateless) |
| Real-time bidirectional, legacy | WebSocket |
| Legacy compatibility | HTTP+SSE (avoid for new work) |
