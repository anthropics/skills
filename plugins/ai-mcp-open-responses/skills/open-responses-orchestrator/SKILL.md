---
name: open-responses-orchestrator
description: |
  Design and orchestrate flows using the Open Responses specification, including OpenAI Responses API
  compatibility. Enables multi-provider routing, request/response modeling, and integration as a
  backend for MCP tools and agents.
license: Complete terms in LICENSE.txt
---

# Open Responses Orchestration

## When to Use

Use this skill when:

- Designing request/response payloads following the Open Responses specification
- Building multi-provider routing systems that work with OpenAI, Anthropic, local models, or custom endpoints
- Migrating existing OpenAI Responses API implementations to Open Responses
- Creating backend services that expose Open Responses endpoints for MCP tools
- Orchestrating complex LLM workflows with streaming, tool use, and structured outputs

---

## Concepts

### Open Responses Overview

Open Responses is an open specification for LLM request/response handling that provides:

- **Provider Agnosticism**: Single API format that works across multiple LLM providers
- **Streaming Support**: Unified streaming format with server-sent events (SSE)
- **Tool Integration**: Standardized tool calling and response handling
- **Structured Outputs**: JSON schema-based output validation

### Request Structure

```json
{
  "model": "provider/model-name",
  "input": "User message or conversation array",
  "instructions": "System-level instructions",
  "tools": [...],
  "response_format": {
    "type": "json_schema",
    "json_schema": {...}
  },
  "stream": true
}
```

### Response Structure

```json
{
  "id": "resp_abc123",
  "object": "response",
  "created_at": 1234567890,
  "status": "completed",
  "output": [
    {
      "type": "message",
      "role": "assistant",
      "content": [...]
    }
  ],
  "usage": {
    "input_tokens": 100,
    "output_tokens": 50
  }
}
```

---

## Instructions

### Step 1: Define Your Request Model

Start by defining the structure of your Open Responses request:

```typescript
interface OpenResponsesRequest {
  model: string;
  input: string | ConversationMessage[];
  instructions?: string;
  tools?: ToolDefinition[];
  response_format?: ResponseFormat;
  stream?: boolean;
  metadata?: Record<string, unknown>;
}
```

### Step 2: Configure Provider Routing

Set up routing rules for different providers:

```yaml
# routing-config.yaml
providers:
  openai:
    base_url: "https://api.openai.com/v1"
    models:
      - "gpt-4o"
      - "gpt-4o-mini"
  anthropic:
    base_url: "https://api.anthropic.com/v1"
    models:
      - "claude-sonnet-4-20250514"
      - "claude-opus-4-20250514"
  local:
    base_url: "http://localhost:11434/v1"
    models:
      - "ollama/*"
      - "litellm/*"

routing_rules:
  - pattern: "openai/*"
    provider: openai
  - pattern: "anthropic/*"
    provider: anthropic
  - pattern: "local/*"
    provider: local
  - default: openai
```

### Step 3: Implement the Orchestrator

```typescript
// orchestrator.ts
import { OpenResponsesRequest, OpenResponsesResponse } from "./types";
import { routeToProvider } from "./routing";

export class OpenResponsesOrchestrator {
  async createResponse(
    request: OpenResponsesRequest
  ): Promise<OpenResponsesResponse> {
    // Validate request
    this.validateRequest(request);

    // Route to appropriate provider
    const provider = routeToProvider(request.model);

    // Transform request to provider format
    const providerRequest = provider.transformRequest(request);

    // Execute request
    const providerResponse = await provider.execute(providerRequest);

    // Transform response to Open Responses format
    return provider.transformResponse(providerResponse);
  }

  async *createStreamingResponse(
    request: OpenResponsesRequest
  ): AsyncGenerator<OpenResponsesEvent> {
    const provider = routeToProvider(request.model);
    const stream = provider.executeStream(
      provider.transformRequest({ ...request, stream: true })
    );

    for await (const chunk of stream) {
      yield provider.transformStreamEvent(chunk);
    }
  }
}
```

### Step 4: Integrate with MCP Server

Expose your orchestrator as MCP tools:

```typescript
// mcp-integration.ts
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { OpenResponsesOrchestrator } from "./orchestrator";

export function registerOpenResponsesTools(server: McpServer) {
  const orchestrator = new OpenResponsesOrchestrator();

  server.tool(
    "create_response",
    "Create a response using Open Responses API",
    {
      model: { type: "string", description: "Model identifier" },
      input: { type: "string", description: "User input" },
      instructions: { type: "string", description: "System instructions" },
    },
    async ({ model, input, instructions }) => {
      const response = await orchestrator.createResponse({
        model,
        input,
        instructions,
      });
      return {
        content: [{ type: "text", text: JSON.stringify(response, null, 2) }],
      };
    }
  );
}
```

### Step 5: Handle Tool Calls in Responses

```typescript
// tool-handler.ts
interface ToolCall {
  id: string;
  type: "function";
  function: {
    name: string;
    arguments: string;
  };
}

export async function processToolCalls(
  toolCalls: ToolCall[],
  toolRegistry: Map<string, ToolHandler>
): Promise<ToolResult[]> {
  return Promise.all(
    toolCalls.map(async (call) => {
      const handler = toolRegistry.get(call.function.name);
      if (!handler) {
        return {
          tool_call_id: call.id,
          output: JSON.stringify({ error: "Tool not found" }),
        };
      }
      const args = JSON.parse(call.function.arguments);
      const result = await handler(args);
      return {
        tool_call_id: call.id,
        output: JSON.stringify(result),
      };
    })
  );
}
```

---

## Migration from OpenAI Responses API

If migrating from pure OpenAI Responses API:

1. **Update model identifiers**: Change `gpt-4o` to `openai/gpt-4o`
2. **Add routing configuration**: Define provider mappings
3. **Update endpoints**: Point to your Open Responses server
4. **Test thoroughly**: Verify streaming, tool calls, and structured outputs

---

## Additional Resources

- **`templates/`** — JSON/YAML request/response examples and routing configurations
- **`reference/`** — Open Responses specification, schema definitions, and provider documentation

Use these resources for implementation guidance and API reference.
