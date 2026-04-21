---
name: api-documentation-writer
description: Generate API reference documentation from source code. Extracts endpoints, parameters, and response schemas, then produces tested documentation with working examples. Use when the user asks to document an API.
license: Apache-2.0
---

# API Documentation Writer

## Step 1: Discover endpoints

Find all API endpoints in the codebase. Use Grep to search for route definitions:

```bash
# Express / Koa / Hono
grep -rn "router\.\(get\|post\|put\|patch\|delete\)" --include="*.ts" --include="*.js" src/

# FastAPI / Flask / Django
grep -rn "@app\.\(get\|post\|put\|patch\|delete\)\|@router\.\|path(" --include="*.py" src/

# Go (net/http, chi, gin, echo)
grep -rn "HandleFunc\|\.GET\|\.POST\|\.PUT\|\.DELETE" --include="*.go" .

# Spring Boot
grep -rn "@GetMapping\|@PostMapping\|@PutMapping\|@DeleteMapping\|@RequestMapping" --include="*.java" src/
```

Read each file to extract: HTTP method, path, path parameters, query parameters, request body schema, response schema, and auth requirements.

## Step 2: Find existing documentation

Check for existing docs to update rather than overwrite:

```bash
find . -name "openapi*" -o -name "swagger*" -o -name "API*" -o -name "api-docs*" | head -20
```

If an OpenAPI/Swagger spec exists, use it as the source of truth and update it rather than creating separate docs.

## Step 3: Write documentation

For each endpoint, document in this order:

```markdown
### `METHOD /path/:param`

Brief description of what this endpoint does.

**Authentication:** Required (Bearer token) | Optional | None

**Parameters:**

| Name | In | Type | Required | Description |
|------|------|------|----------|-------------|
| id | path | string | yes | Resource identifier |
| limit | query | integer | no | Max results (default: 20, max: 100) |

**Request body:**
\`\`\`json
{
  "field": "value"
}
\`\`\`

**Response:** `200 OK`
\`\`\`json
{
  "id": "abc123",
  "created_at": "2024-01-15T09:00:00Z"
}
\`\`\`

**Errors:**

| Status | Description |
|--------|-------------|
| 400 | Invalid request body |
| 401 | Missing or invalid auth token |
| 404 | Resource not found |
```

## Step 4: Verify examples

For every request example you write, verify it would actually work:
1. Check that the URL path matches the route definition in code
2. Check that request body fields match the validation schema or type definition
3. Check that the response matches what the handler actually returns
4. Check that documented error codes match the error handling in code

If you can run the server locally, test examples with curl. If not, trace through the code to verify.

## Step 5: Write the overview sections

After documenting individual endpoints, add these sections at the top:

1. **Base URL** - Include all environments if known (production, staging)
2. **Authentication** - How to obtain and use credentials, with a working curl example
3. **Errors** - The standard error envelope format (most APIs have one)
4. **Pagination** - If any list endpoint is paginated, document the pattern once here
5. **Rate limits** - If applicable

## Gotchas

- Don't invent response fields. If you can't determine the exact response shape from code, say "Response schema TBD" rather than guessing.
- Auth is the #1 thing developers need to get right first. Put a complete, copy-pasteable auth example before anything else.
- If the API uses non-standard status codes or error formats, call that out prominently.
- Check for middleware that adds headers, wraps responses, or transforms errors globally — this affects every endpoint's documentation.
- Document rate limits per-endpoint if they differ. A blanket "rate limited" statement is useless.
- If request body fields have validation constraints (min/max length, regex patterns, enums), document them. These cause the most integration bugs.
