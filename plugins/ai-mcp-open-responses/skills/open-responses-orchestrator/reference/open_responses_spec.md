# Open Responses Specification Reference

## Overview

Open Responses is an open specification for unified LLM request/response handling across multiple providers. It provides a standardized API format compatible with OpenAI's Responses API while enabling multi-provider routing.

---

## API Endpoints

### Create Response

```
POST /v1/responses
```

Creates a new response from the model.

#### Request Headers

```http
Content-Type: application/json
Authorization: Bearer <api_key>
X-Request-ID: <optional_request_id>
```

#### Request Body

```json
{
  "model": "string",
  "input": "string | array",
  "instructions": "string | null",
  "tools": "array | null",
  "tool_choice": "auto | none | required | object | null",
  "parallel_tool_calls": "boolean",
  "response_format": "object | null",
  "temperature": "number | null",
  "top_p": "number | null",
  "max_output_tokens": "integer | null",
  "stream": "boolean",
  "metadata": "object | null",
  "store": "boolean",
  "truncation": "object | null"
}
```

---

## Field Specifications

### model (required)

The model identifier. Supports provider-prefixed format:

```
openai/gpt-4o
anthropic/claude-sonnet-4-20250514
local/llama-3.2-8b
ollama/codellama
litellm/gpt-4o-mini
```

### input (required)

Either a simple string or an array of conversation messages:

**String format:**
```json
{
  "input": "What is the capital of France?"
}
```

**Message array format:**
```json
{
  "input": [
    {
      "role": "user",
      "content": "What is the capital of France?"
    },
    {
      "role": "assistant",
      "content": "The capital of France is Paris."
    },
    {
      "role": "user",
      "content": "What is its population?"
    }
  ]
}
```

### instructions (optional)

System-level instructions for the model:

```json
{
  "instructions": "You are a helpful assistant specializing in geography. Always provide accurate, up-to-date information."
}
```

### tools (optional)

Array of tool definitions:

```json
{
  "tools": [
    {
      "type": "function",
      "function": {
        "name": "get_weather",
        "description": "Get current weather for a location",
        "parameters": {
          "type": "object",
          "properties": {
            "location": {
              "type": "string",
              "description": "City name or coordinates"
            },
            "units": {
              "type": "string",
              "enum": ["celsius", "fahrenheit"],
              "default": "celsius"
            }
          },
          "required": ["location"]
        }
      }
    }
  ]
}
```

### tool_choice (optional)

Controls tool usage:

- `"auto"` - Model decides whether to use tools (default)
- `"none"` - Model will not use any tools
- `"required"` - Model must use at least one tool
- Object specifying a specific tool:

```json
{
  "tool_choice": {
    "type": "function",
    "function": {
      "name": "get_weather"
    }
  }
}
```

### response_format (optional)

Controls output format:

**Text format (default):**
```json
{
  "response_format": {
    "type": "text"
  }
}
```

**JSON Schema format:**
```json
{
  "response_format": {
    "type": "json_schema",
    "json_schema": {
      "name": "weather_response",
      "strict": true,
      "schema": {
        "type": "object",
        "properties": {
          "temperature": { "type": "number" },
          "conditions": { "type": "string" },
          "humidity": { "type": "number" }
        },
        "required": ["temperature", "conditions"],
        "additionalProperties": false
      }
    }
  }
}
```

---

## Response Format

### Synchronous Response

```json
{
  "id": "resp_abc123def456",
  "object": "response",
  "created_at": 1699564800,
  "model": "openai/gpt-4o",
  "status": "completed",
  "output": [
    {
      "type": "message",
      "id": "msg_xyz789",
      "role": "assistant",
      "content": [
        {
          "type": "text",
          "text": "The capital of France is Paris."
        }
      ]
    }
  ],
  "usage": {
    "input_tokens": 15,
    "output_tokens": 8,
    "total_tokens": 23
  },
  "metadata": {}
}
```

### Response with Tool Calls

```json
{
  "id": "resp_abc123def456",
  "object": "response",
  "created_at": 1699564800,
  "model": "openai/gpt-4o",
  "status": "requires_action",
  "output": [
    {
      "type": "message",
      "id": "msg_xyz789",
      "role": "assistant",
      "content": [
        {
          "type": "tool_use",
          "id": "call_abc123",
          "name": "get_weather",
          "input": {
            "location": "Paris",
            "units": "celsius"
          }
        }
      ]
    }
  ],
  "usage": {
    "input_tokens": 25,
    "output_tokens": 15,
    "total_tokens": 40
  }
}
```

---

## Streaming Format

### Event Types

```
event: response.created
event: response.in_progress
event: response.output_item.added
event: response.content_part.added
event: response.output_text.delta
event: response.output_text.done
event: response.content_part.done
event: response.output_item.done
event: response.completed
event: response.failed
event: error
```

### Example Stream

```
event: response.created
data: {"id":"resp_abc123","object":"response","status":"in_progress"}

event: response.output_text.delta
data: {"delta":"The"}

event: response.output_text.delta
data: {"delta":" capital"}

event: response.output_text.delta
data: {"delta":" of France is Paris."}

event: response.completed
data: {"id":"resp_abc123","object":"response","status":"completed","usage":{"input_tokens":15,"output_tokens":8}}
```

---

## Error Responses

### Error Object

```json
{
  "error": {
    "type": "invalid_request_error",
    "code": "invalid_model",
    "message": "The model 'invalid/model' is not supported.",
    "param": "model"
  }
}
```

### Error Types

| Type | Description |
|------|-------------|
| `invalid_request_error` | Request validation failed |
| `authentication_error` | Invalid or missing API key |
| `permission_error` | Insufficient permissions |
| `not_found_error` | Resource not found |
| `rate_limit_error` | Rate limit exceeded |
| `api_error` | Internal server error |
| `overloaded_error` | Service temporarily overloaded |

### HTTP Status Codes

| Code | Meaning |
|------|---------|
| 200 | Success |
| 400 | Bad Request |
| 401 | Unauthorized |
| 403 | Forbidden |
| 404 | Not Found |
| 429 | Rate Limited |
| 500 | Internal Error |
| 503 | Service Unavailable |

---

## Provider Routing

### Routing Configuration

```yaml
routing:
  rules:
    - pattern: "openai/*"
      provider: openai
      endpoint: https://api.openai.com/v1
    - pattern: "anthropic/*"
      provider: anthropic
      endpoint: https://api.anthropic.com/v1
    - pattern: "local/*"
      provider: ollama
      endpoint: http://localhost:11434
    - pattern: "*"
      provider: openai  # Default fallback
```

### Request Transformation

Each provider requires specific transformations:

**OpenAI:** Native format, minimal transformation
**Anthropic:** Convert `input` to `messages`, map `instructions` to system prompt
**Ollama:** Convert to chat completion format, adjust parameters

---

## Rate Limiting

### Headers

```http
X-RateLimit-Limit: 1000
X-RateLimit-Remaining: 999
X-RateLimit-Reset: 1699568400
Retry-After: 60
```

### Best Practices

1. Implement exponential backoff on 429 responses
2. Cache responses where appropriate
3. Use request deduplication for identical inputs
4. Monitor usage through the `/v1/usage` endpoint
