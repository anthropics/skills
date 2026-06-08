# MCP Advanced Patterns, Performance, Debugging, and Comparisons

## Advanced Patterns

### Multi-Tool Orchestration

MCP servers work best when tools are composable. Design tools at the right granularity:

**Too fine-grained** (forces model to make many round trips):
- `github_get_issue_title`, `github_get_issue_body`, `github_get_issue_assignees` (3 tools)

**Too coarse-grained** (inflexible, poor error isolation):
- `github_do_everything` (1 tool that does too much)

**Right granularity**:
- `github_get_issue` (full issue details in one call)
- `github_list_issues` (paginated list)
- `github_create_issue`, `github_update_issue`, `github_close_issue`

For orchestrating sequences across multiple servers, the LLM client (not the MCP server)
is responsible for chaining tool calls. Servers should be stateless and atomic.

### Stateful vs Stateless Servers

**Stateless** (recommended for HTTP transport):
- Each request is independent
- No server-side session state
- Horizontally scalable
- Simpler to reason about
- Use `sessionIdGenerator: undefined` in Streamable HTTP transport

**Stateful** (use with stdio or when sessions are needed):
- Server maintains state across calls within a session
- Required for: long-running processes, streaming subscriptions, authenticated sessions
- Use `sessionIdGenerator: () => randomUUID()` in Streamable HTTP

```typescript
// Stateful HTTP server example
const sessions = new Map<string, SessionState>();

app.post('/mcp', async (req, res) => {
  const transport = new StreamableHTTPServerTransport({
    sessionIdGenerator: () => randomUUID(),
    onsessioninitialized: (sessionId) => {
      sessions.set(sessionId, initializeSession());
    }
  });
  // Session ID available via transport.sessionId after connect
});
```

### Parallel Tool Calls

Modern MCP clients can call multiple tools simultaneously when the LLM determines calls are
independent. Design tools to support this:

- Make tools truly atomic (no cross-tool state dependencies)
- Return immediately rather than polling internally
- Handle concurrent connections in HTTP servers (use async throughout)

For Python servers, ensure all I/O is async (never use `requests`, use `httpx.AsyncClient`).
For TypeScript, ensure no synchronous blocking code in handlers.

### Response Truncation

Prevent context window overflow with consistent truncation:

```typescript
const CHARACTER_LIMIT = 25_000;

function truncateResponse(data: any[], total: number, offset: number): string {
  let result = JSON.stringify({ total, items: data, offset });
  if (result.length > CHARACTER_LIMIT) {
    const halfData = data.slice(0, Math.ceil(data.length / 2));
    result = JSON.stringify({
      total, items: halfData, offset,
      truncated: true,
      truncation_message: `Response truncated. Use offset=${offset + halfData.length} for next page.`
    });
  }
  return result;
}
```

### Resource Subscriptions (Real-Time Updates)

```typescript
// Server declares subscribe capability
const server = new McpServer({
  capabilities: { resources: { subscribe: true } }
});

// Handle subscription requests
server.setRequestHandler(SubscribeRequestSchema, async ({ params }) => {
  const { uri } = params;
  subscribeToChanges(uri, async () => {
    await server.notification({
      method: "notifications/resources/updated",
      params: { uri }
    });
  });
  return {};
});
```

### Cancellation Handling

```typescript
server.setRequestHandler(CallToolRequestSchema, async (request, { signal }) => {
  // Check cancellation at checkpoints
  if (signal.aborted) {
    throw new Error("Request cancelled");
  }

  const result = await longRunningOperation();

  if (signal.aborted) {
    return { isError: true, content: [{ type: "text", text: "Cancelled" }] };
  }

  return { content: [{ type: "text", text: result }] };
});
```

### Sampling in Practice (Agentic Servers)

```python
# Server-side: request LLM completion for classification
@mcp.tool()
async def classify_and_route(document: str, ctx: Context) -> str:
    """Classify a document and route it to the correct handler."""

    # Ask the host LLM to classify the document
    classification = await ctx.sample(
        messages=[{
            "role": "user",
            "content": f"Classify this document as 'bug', 'feature', or 'question':\n\n{document}"
        }],
        max_tokens=5,
        system_prompt="Respond with exactly one word: bug, feature, or question."
    )

    category = classification.strip().lower()

    if category == "bug":
        return await route_to_bugs(document)
    elif category == "feature":
        return await route_to_features(document)
    else:
        return await route_to_questions(document)
```

## Performance Optimization

### Connection Pooling (HTTP Clients)

Never create a new HTTP client per request. Use shared connection pools:

```python
# Bad: new client per tool call
@mcp.tool()
async def fetch_data(url: str) -> str:
    async with httpx.AsyncClient() as client:  # New connection every time
        return (await client.get(url)).text

# Good: shared client via lifespan
@asynccontextmanager
async def lifespan(app):
    async with httpx.AsyncClient(limits=httpx.Limits(max_connections=20)) as client:
        yield {"http": client}

mcp = FastMCP("my_mcp", lifespan=lifespan)

@mcp.tool()
async def fetch_data(url: str, ctx: Context) -> str:
    client = ctx.request_context.lifespan_state["http"]
    return (await client.get(url)).text
```

### Tool Definition Caching

Client-side: Cache the `tools/list` response rather than fetching on every interaction.
Invalidate only when `notifications/tools/list_changed` arrives.

Server-side: Compute tool descriptions and schemas at startup, not per-request.

### Rate Limiting (Production HTTP Servers)

Token bucket algorithm for bursty LLM tool call patterns:

```typescript
import { RateLimiter } from "limiter";

const limiter = new RateLimiter({
  tokensPerInterval: 100,
  interval: "minute",
  fireImmediately: true
});

app.post('/mcp', async (req, res) => {
  const remaining = await limiter.removeTokens(1);
  if (remaining < 0) {
    res.status(429).json({
      error: "rate_limited",
      retry_after: 60
    });
    return;
  }
  // ... handle request
});
```

### Timeout Configuration

```typescript
// MCP Inspector environment variables for timeouts:
// MCP_SERVER_REQUEST_TIMEOUT=30000
// MCP_REQUEST_TIMEOUT_RESET_ON_PROGRESS=true
// MCP_REQUEST_MAX_TOTAL_TIMEOUT=120000

// In your server, set reasonable timeouts on external calls:
const response = await axios.get(url, { timeout: 30_000 });

// For Claude Desktop, default tool timeout is 60 seconds
// Long-running tools should report progress to prevent timeout
```

## Debugging with MCP Inspector

MCP Inspector is the official interactive debugging tool for MCP servers.

### Launch

```bash
# Launch against a stdio server
npx @modelcontextprotocol/inspector node dist/index.js

# With environment variables
npx @modelcontextprotocol/inspector -e API_KEY=sk-... node dist/index.js arg1

# Connect to remote HTTP server
npx @modelcontextprotocol/inspector --transport streamable-http --url http://localhost:3000/mcp

# Docker
docker run --rm -p 127.0.0.1:6274:6274 ghcr.io/modelcontextprotocol/inspector:latest
```

Requirements: Node.js >= 22.7.5. UI at http://localhost:6274.

### Features

- **Transport-agnostic**: Connects to stdio, SSE, and Streamable HTTP servers
- **Tool invocation UI**: Form-based parameter input with JSON display
- **Resource navigation**: Browse and read resources hierarchically
- **Prompt testing**: Test prompts with streaming response visualization
- **Notification stream**: Watch server-sent notifications in real time
- **Request/response history**: Full JSON log of all protocol messages
- **Config export**: Generate `mcp.json` for Claude Desktop/Cursor

### Security (Inspector-Specific)

- Generates a random session token on startup; printed to console
- All proxy requests require `Authorization: Bearer <token>` header
- Binds to localhost only by default
- DNS rebinding protection via Origin header validation

### Debugging Workflow

1. Run `npx @modelcontextprotocol/inspector node dist/index.js`
2. Select transport (STDIO for local, Streamable HTTP for URL)
3. Connect to verify initialization handshake succeeds
4. Check "Capabilities" tab to verify declared capabilities match server code
5. Invoke each tool with test parameters; verify response format
6. Check "Notifications" tab during tool calls for progress/log messages
7. Test error cases: invalid params, missing required fields, API errors

### Common Failure Modes

| Symptom | Likely Cause | Fix |
|---|---|---|
| Inspector can't connect | Server writes to stdout (not stderr) | Move all logs to stderr |
| "Method not found" | Wrong API (using deprecated handlers) | Switch to registerTool/registerResource |
| Tool appears but fails | Schema mismatch between definition and handler | Validate with Zod/Pydantic in handler |
| Timeout on every call | Synchronous blocking in async handler | Use async I/O throughout |
| Initialization fails | Protocol version mismatch | Set protocolVersion to "2025-03-26" |
| Auth errors on HTTP | Missing/wrong Authorization header | Check Bearer token format |
| Empty tool list | Forgot to await server.connect() | Ensure connect() is awaited before serving |

### Logging Best Practices

```typescript
// TypeScript: all logs to stderr
console.error("[INFO] Server started");
console.error("[DEBUG] Tool called:", toolName);
console.error("[ERROR] API call failed:", error.message);

// NEVER: console.log() in stdio server — breaks JSON-RPC stream
```

```python
# Python: FastMCP automatically routes logs to stderr
import logging
logging.basicConfig(level=logging.DEBUG, stream=sys.stderr)
logger = logging.getLogger(__name__)
logger.info("Server started")
```

## MCP vs Other Integration Patterns

### MCP vs Native Function Calling (OpenAI, Anthropic)

| Dimension | MCP | Native Function Calling |
|---|---|---|
| **Schema location** | Server publishes once; clients discover | Each app maintains own copy |
| **Reusability** | One server, many clients | Per-app integration |
| **Discovery** | Runtime (tools/list) | Static (code/config) |
| **Transport** | stdio or HTTP | In-process |
| **Token cost** | Schema sent once per session | Schema sent every request |
| **Control** | Server controls schema | App controls schema |
| **Complexity** | Higher (separate process) | Lower (in-process) |
| **Best for** | Tools shared across many AI apps | App-specific, high-volume, least-privilege |

**Choose native function calling when**:
- High-volume production traffic (schema token cost matters)
- Fine-grained least-privilege control per request
- No need to share tools across AI apps
- Simple integrations where MCP overhead isn't justified

**Choose MCP when**:
- Tools should work with Claude Desktop, Cursor, and Windsurf all at once
- Rapid prototyping (schema generated automatically)
- Tools are maintained by a separate team/service
- Ecosystem interoperability is required

### MCP vs LangChain Tools

| Dimension | MCP | LangChain Tools |
|---|---|---|
| **Architecture** | Protocol (transport-agnostic) | Framework (in-process) |
| **Schema management** | Server-published, runtime discovery | Class-based, regenerated per call |
| **Multi-step orchestration** | Model decides; no built-in graph | LangGraph state machine, first-class |
| **Retry/fallback** | Must implement manually | Built-in callback system |
| **Memory** | Via resources/sampling | Built-in memory abstractions |
| **Observability** | Custom instrumentation needed | Built-in callback chain |
| **Token cost** | Low (schema cached per session) | Higher (framework overhead) |

**Choose MCP when**:
- Simple assistant with external tools
- Cross-client compatibility required
- Tools maintained as separate services
- 80% of use cases — it's simpler and covers most needs

**Choose LangChain when**:
- Complex multi-step agent with conditional branching
- Advanced RAG pipeline
- Built-in memory and conversation management needed
- LangGraph-style state machine for the agent
- Deep observability via LangSmith

**Integration**: LangChain can wrap MCP servers as LangChain Tools, giving you both.

### MCP vs OpenAI Plugins (Legacy)

OpenAI plugins (deprecated 2024) required a manifest file and specific OpenAPI format.
MCP supersedes this with:
- Transport flexibility (plugins were HTTP only)
- Richer primitives (resources, prompts, sampling, roots)
- Universal client support (not vendor-locked)
- Active governance and specification evolution

### When NOT to Use MCP

- One-off script that calls one API — just use the SDK directly
- High-throughput production pipeline where per-call latency matters — use native function calling
- Internal tool that only one AI app will ever use — function calling is simpler
- When you need the model to always use the exact schema you specify — native gives you control
