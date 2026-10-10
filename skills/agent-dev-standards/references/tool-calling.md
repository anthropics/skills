# Tool Calling

Tool schema design and error recovery patterns for Agent tools.

## Tool Schema Design

Every tool must have a typed JSON Schema:

`json
{
  "name": "search_documents",
  "description": "Search indexed documents by query string",
  "parameters": {
    "type": "object",
    "properties": {
      "query": {
        "type": "string",
        "description": "Search query, max 200 characters"
      },
      "limit": {
        "type": "integer",
        "description": "Max results to return, 1 to 20",
        "minimum": 1,
        "maximum": 20
      }
    },
    "required": ["query"]
  }
}
`

Key rules:
- Every parameter must have description, type, and constraints (minimum, maximum, enum).
- Required fields listed explicitly in required array.
- Description tells WHEN to use this tool, not just what it does.

## Error Recovery Patterns

Every tool must define 4 outcomes:

| Outcome | Signal | Recovery |
|---------|--------|----------|
| Success | Returns expected data | Normal flow continues |
| Partial | Returns partial data + warning | Flag to agent, continue with caveat |
| Retryable | Network timeout, rate limit | Retry with exponential backoff (max 3 attempts) |
| Terminal | Invalid input, auth failure | Abort chain, report error to agent |

`python
# Example: retryable error handler
def search_documents(query: str, limit: int = 10):
    for attempt in range(3):
        try:
            result = client.search(query, size=limit)
            return {"status": "success", "data": result}
        except TimeoutError:
            if attempt < 2:
                time.sleep(2 ** attempt)  # backoff: 1s, 2s, 4s
                continue
            return {"status": "retryable", "error": "timeout after 3 attempts"}
        except AuthError:
            return {"status": "terminal", "error": "auth failure"}
`

## Orchestration Principles

1. Tools are single-responsibility: one tool, one job.
2. Tool chains must have circuit breaker: abort after N consecutive failures.
3. Tool output must be structured (JSON), not free text.
4. Every tool call logged with latency, token cost, and result status.
