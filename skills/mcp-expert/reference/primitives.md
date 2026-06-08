# MCP Primitives Reference

MCP defines five primitives. Tools and Resources receive the most attention, but Sampling and
Roots are equally important for advanced agentic architectures.

## 1. Tools

Tools are the primary mechanism for LLMs to take actions: call APIs, query databases, run code,
send messages. They are analogous to POST endpoints — they may have side effects.

### Tool Definition Structure

```json
{
  "name": "github_create_issue",
  "description": "Create a new GitHub issue in a repository...",
  "inputSchema": {
    "type": "object",
    "properties": {
      "repo": { "type": "string", "description": "owner/repo format" },
      "title": { "type": "string", "description": "Issue title" },
      "body": { "type": "string", "description": "Issue body in Markdown" }
    },
    "required": ["repo", "title"]
  },
  "annotations": {
    "readOnlyHint": false,
    "destructiveHint": false,
    "idempotentHint": false,
    "openWorldHint": true
  }
}
```

### Tool Annotations (Risk Vocabulary)

Annotations inform clients how to handle confirmation dialogs and policy enforcement.
They are **hints only** — not enforced, not trusted from untrusted servers.

| Annotation | Type | Conservative Default | Meaning |
|---|---|---|---|
| `readOnlyHint` | boolean | `false` | If true, tool never writes/creates/deletes |
| `destructiveHint` | boolean | `true` | If true, modifications may be irreversible |
| `idempotentHint` | boolean | `false` | If true, calling twice = calling once |
| `openWorldHint` | boolean | `true` | If true, tool makes external HTTP calls |

Key constraints:
- `readOnlyHint: true` implies `destructiveHint` and `idempotentHint` are inapplicable.
- The defaults are conservative: an unannotated tool is treated as destructive and external.
- Mismatched annotations (server claims read-only but is destructive) break user trust but
  cannot be prevented by the protocol — this is a trust boundary issue.

### Tool Response Format

Tools return a `CallToolResult`:
```json
{
  "content": [
    { "type": "text", "text": "Created issue #42" },
    { "type": "image", "data": "<base64>", "mimeType": "image/png" },
    { "type": "resource", "resource": { "uri": "file:///path/to/file", "text": "..." } }
  ],
  "isError": false
}
```

For errors, set `isError: true` and put the error message in content — do NOT throw a JSON-RPC
error-level response for tool failures (that's for protocol errors, not business logic failures).

### outputSchema (Modern Pattern)

The TypeScript SDK v1.6+ supports `outputSchema` for structured tool responses alongside the
text content:
```typescript
server.registerTool("get_user", {
  description: "...",
  inputSchema: z.object({ id: z.string() }),
  outputSchema: z.object({ name: z.string(), email: z.string() })
}, async ({ id }) => {
  const user = await fetchUser(id);
  return {
    content: [{ type: "text", text: JSON.stringify(user) }],
    structuredContent: user  // Validated against outputSchema
  };
});
```

## 2. Resources

Resources expose read-only data to the LLM's context. Analogous to GET endpoints. They do not
execute side effects. The LLM reads resources to gain context.

### Resource Identification

Every resource has a URI. Common URI schemes:
- `file:///absolute/path/to/file.txt` — filesystem files
- `postgres://localhost/mydb/table/users` — database records
- `github://owner/repo/issues/42` — GitHub objects
- Custom schemes: `memory://conversations/recent`, `config://settings/app`

### Resource Definition

```json
{
  "uri": "file:///var/log/app.log",
  "name": "Application Log",
  "description": "Current application log file",
  "mimeType": "text/plain"
}
```

Supported MIME types: `text/plain`, `text/html`, `text/markdown`, `application/json`,
`application/pdf`, `image/png`, `image/jpeg`, and any valid MIME type.

### Static vs Dynamic Resources

**Static resources**: Listed at discovery time with fixed URIs.
```python
@mcp.resource("config://app/settings")
async def get_settings() -> str:
    return json.dumps(load_settings())
```

**Dynamic resources via URI templates**: Use RFC 6570 URI templates for parameterized resources.
```python
@mcp.resource("user://{user_id}/profile")
async def get_user_profile(user_id: str) -> str:
    user = await fetch_user(user_id)
    return json.dumps(user.profile)
```

### Resource Operations

- `resources/list` — List all available resources (supports pagination with cursor)
- `resources/read` — Read a specific resource by URI
- `resources/subscribe` — Subscribe to change notifications for a resource
- `notifications/resources/updated` — Server-sent when subscribed resource changes
- `notifications/resources/list_changed` — Server-sent when resource list changes

### Resource Response

```json
{
  "contents": [
    {
      "uri": "file:///data/report.json",
      "mimeType": "application/json",
      "text": "{\"revenue\": 1000000}"
    }
  ]
}
```

Binary content uses `blob` (base64-encoded) instead of `text`.

### Resources vs Tools

| Use Resources When | Use Tools When |
|---|---|
| Data is read-only | Operation has side effects |
| URI-addressable (template or static) | Requires complex input validation |
| Content is relatively static | Business logic involved |
| Multiple clients need same data | Requires authentication per call |

## 3. Prompts

Prompts are reusable, parameterized message templates exposed by servers. They are
**user-controlled** (shown in the client UI for users to select), unlike tools which are
**model-controlled** (the LLM decides when to call them).

### Prompt Definition

```json
{
  "name": "code_review",
  "description": "Review a pull request for quality issues",
  "arguments": [
    {
      "name": "language",
      "description": "Programming language (e.g., typescript, python)",
      "required": true
    },
    {
      "name": "focus",
      "description": "Review focus: 'security', 'performance', or 'all'",
      "required": false
    }
  ]
}
```

### Prompt Response

```json
{
  "description": "Code review prompt for TypeScript",
  "messages": [
    {
      "role": "user",
      "content": {
        "type": "text",
        "text": "Review this TypeScript code for security issues:\n\n{{code}}"
      }
    }
  ]
}
```

Messages can include text, images, and embedded resources. Prompts enable servers to provide
curated interaction patterns — for example, a database server might provide a "analyze_slow_queries"
prompt that structures the conversation for performance analysis.

### Dynamic Prompts

Prompt content can be dynamically generated at `prompts/get` time based on arguments:

```python
@mcp.prompt()
async def code_review(language: str, focus: str = "all") -> list[Message]:
    schema = await load_schema(language)
    return [
        UserMessage(f"Review this {language} code. Schema: {schema}. Focus: {focus}")
    ]
```

## 4. Sampling

Sampling is MCP's most distinctive and underused primitive. It **inverts the normal flow**:
instead of the client asking the server to do work, the **server asks the client's LLM to
generate text**. This enables "agentic servers" — servers that can reason and make decisions
internally.

### Use Cases

- A server that needs to classify a document before routing it
- A server performing multi-step reasoning where intermediate LLM calls are needed
- Servers that need to generate dynamic content (summaries, translations)
- Servers that implement ReAct-style reasoning loops internally

### Sampling Request (Server → Client)

The server sends:
```json
{
  "method": "sampling/createMessage",
  "params": {
    "messages": [
      { "role": "user", "content": { "type": "text", "text": "Classify: bug|feature|question" } }
    ],
    "modelPreferences": {
      "hints": [{ "name": "claude-3-5-haiku" }],
      "intelligencePriority": 0.3,
      "speedPriority": 0.8,
      "costPriority": 0.8
    },
    "systemPrompt": "You are a ticket classifier. Respond with exactly one word.",
    "maxTokens": 10
  }
}
```

The client's LLM processes the request and returns the completion. The **human must remain
in the loop** — hosts should display sampling requests for user approval before forwarding
to the LLM (critical for security against malicious servers).

### Model Preferences

`modelPreferences` lets servers express hints without hard-coding model names:
- `hints`: Preferred model names (best-effort, client may substitute)
- `intelligencePriority`: 0.0-1.0 (weight toward more capable models)
- `speedPriority`: 0.0-1.0 (weight toward faster models)
- `costPriority`: 0.0-1.0 (weight toward cheaper models)

## 5. Roots

Roots are a **client-side primitive** that servers can query to understand the host environment.
They represent "entry points" — typically filesystem directories that the host has open or that
the user has granted access to.

### Purpose

When an IDE like Cursor starts an MCP server, the server can ask "what projects/directories does
the user have open?" This allows the server to scope its operations to the user's actual
workspace rather than operating blindly.

### Roots/List Response

```json
{
  "roots": [
    {
      "uri": "file:///Users/alice/projects/my-app",
      "name": "my-app"
    },
    {
      "uri": "file:///Users/alice/projects/shared-lib",
      "name": "shared-lib"
    }
  ]
}
```

### Roots Change Notifications

If the client declared `roots.listChanged: true` during initialization, it will send
`notifications/roots/list_changed` when the user opens or closes projects. Servers should
re-query roots when this notification arrives.

### Security Note

Servers should treat roots as suggestions, not permissions. A malicious server could request
`file:///etc/passwd` even if no root points there. Access control must be enforced at the
host level, not inferred from roots alone.

## Pagination

Resources, tools, and prompts all support cursor-based pagination via `nextCursor`:

```json
// Request
{ "method": "tools/list", "params": { "cursor": "opaque-cursor-string" } }

// Response
{
  "result": {
    "tools": [...],
    "nextCursor": "next-page-cursor"  // absent if last page
  }
}
```

Iterate until `nextCursor` is absent. Cursors are opaque strings — do not parse them.

## Subscriptions and Notifications

Servers can push state changes to clients without being polled:

| Notification | Trigger |
|---|---|
| `notifications/tools/list_changed` | Server added/removed a tool |
| `notifications/resources/list_changed` | Resource list changed |
| `notifications/resources/updated` | Subscribed resource content changed |
| `notifications/prompts/list_changed` | Prompt list changed |
| `notifications/progress` | Long-running operation progress update |
| `notifications/cancelled` | Request was cancelled |
| `notifications/message` | Server log message |

## Cancellation

For long-running operations, either side may send a cancellation:
```json
{
  "method": "notifications/cancelled",
  "params": { "requestId": "req-456", "reason": "User cancelled" }
}
```

Upon receiving cancellation, the handler should stop processing and release resources.
The sender should stop waiting for the response but handle a late response gracefully.

## Progress Reporting

Servers report progress on long operations using the `_meta.progressToken` from the request:
```json
{
  "method": "notifications/progress",
  "params": {
    "progressToken": "tok-789",
    "progress": 0.65,
    "total": 1.0
  }
}
```

In FastMCP Python:
```python
@mcp.tool()
async def process_large_file(path: str, ctx: Context) -> str:
    await ctx.report_progress(0.0, "Starting...")
    data = await read_file(path)
    await ctx.report_progress(0.5, "Processing...")
    result = await process(data)
    await ctx.report_progress(1.0, "Done")
    return result
```
