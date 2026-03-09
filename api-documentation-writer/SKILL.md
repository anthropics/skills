---
name: api-documentation-writer
description: Use this skill to generate comprehensive, developer-friendly API documentation with examples, covering endpoints, authentication, request/response formats, and error handling
license: Apache-2.0
---

# API Documentation Writer

Generate clear, comprehensive, and developer-friendly API documentation that helps users quickly understand and integrate with APIs.

## When to Use

Use this skill when:
- The user asks to "document the API" or "create API docs"
- The user wants to generate OpenAPI/Swagger documentation
- The user needs reference documentation for REST, GraphQL, or other APIs
- The user is building or updating an API and needs documentation
- The user wants to improve existing API documentation

## Documentation Generation Process

### Step 1: Gather Information

**Understand the API:**
1. Ask the user about the API type (REST, GraphQL, gRPC, etc.)
2. Identify where the API is defined:
   - Code files (routes, controllers, handlers)
   - OpenAPI/Swagger spec files
   - GraphQL schema files
   - Existing documentation

3. Use Glob and Grep to find relevant files:
   ```bash
   # Find route definitions
   - REST: Look for route decorators, router files
   - GraphQL: Look for schema definitions
   - gRPC: Look for .proto files
   ```

4. Read the API implementation files to understand:
   - Available endpoints/queries/mutations
   - Request parameters and body schemas
   - Response formats
   - Authentication requirements
   - Error handling

**Ask clarifying questions if needed:**
- What's the base URL for the API?
- What authentication methods are used?
- Are there rate limits?
- What environments are available (dev/staging/prod)?
- Are there SDK clients available?

### Step 2: Structure the Documentation

Organize documentation in this structure:

```markdown
# API Documentation

## Overview
- Brief description of what the API does
- Base URL(s)
- API version
- Key features

## Getting Started
- Prerequisites
- Authentication setup
- Quick start example
- Common use cases

## Authentication
- Supported methods (API keys, OAuth, JWT, etc.)
- How to obtain credentials
- How to include auth in requests
- Token refresh/expiration

## Endpoints (or Queries/Mutations for GraphQL)
- Organized by resource or feature
- Each endpoint fully documented

## Error Handling
- Common error codes
- Error response format
- Troubleshooting guide

## Rate Limiting
- Limits and quotas
- Headers to check
- How to handle rate limit errors

## SDKs and Tools
- Available client libraries
- Code generation tools
- Testing tools (Postman collections, etc.)

## Changelog
- API version history
- Breaking changes
- Deprecations
```

### Step 3: Document Each Endpoint

For REST APIs, document each endpoint with this template:

```markdown
### [HTTP Method] [Endpoint Path]

Brief description of what this endpoint does.

**Endpoint:** `[METHOD] /api/v1/resource/:id`

**Authentication:** Required/Optional - [Type]

**Parameters:**

Path Parameters:
| Name | Type | Required | Description |
|------|------|----------|-------------|
| id | string | Yes | The unique identifier |

Query Parameters:
| Name | Type | Required | Default | Description |
|------|------|----------|---------|-------------|
| limit | integer | No | 20 | Number of items to return |
| offset | integer | No | 0 | Number of items to skip |

**Request Headers:**
| Name | Type | Required | Description |
|------|------|----------|-------------|
| Authorization | string | Yes | Bearer token |
| Content-Type | string | Yes | Must be application/json |

**Request Body:**

```json
{
  "field1": "string",
  "field2": 123,
  "nested": {
    "field3": true
  }
}
```

Field descriptions:
- `field1` (string, required): Description
- `field2` (integer, optional): Description
- `nested.field3` (boolean, optional): Description

**Response:**

Success Response (200 OK):
```json
{
  "id": "abc123",
  "field1": "value",
  "createdAt": "2025-01-15T10:30:00Z"
}
```

Field descriptions:
- `id` (string): Unique identifier
- `field1` (string): Description
- `createdAt` (string): ISO 8601 timestamp

**Error Responses:**

| Status Code | Description | Response Body |
|-------------|-------------|---------------|
| 400 | Bad Request | `{"error": "Invalid input", "details": [...]}` |
| 401 | Unauthorized | `{"error": "Invalid or missing token"}` |
| 404 | Not Found | `{"error": "Resource not found"}` |
| 500 | Server Error | `{"error": "Internal server error"}` |

**Example Request:**

```bash
curl -X POST https://api.example.com/api/v1/resource \
  -H "Authorization: Bearer YOUR_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "field1": "example value",
    "field2": 42
  }'
```

**Example Response:**

```json
{
  "id": "abc123",
  "field1": "example value",
  "field2": 42,
  "createdAt": "2025-01-15T10:30:00Z"
}
```

**Notes:**
- Additional information
- Edge cases
- Related endpoints
```

### Step 4: Add Code Examples

Include examples in multiple languages:

```markdown
## Code Examples

### JavaScript/Node.js

```javascript
const response = await fetch('https://api.example.com/api/v1/resource', {
  method: 'POST',
  headers: {
    'Authorization': `Bearer ${token}`,
    'Content-Type': 'application/json'
  },
  body: JSON.stringify({
    field1: 'example value',
    field2: 42
  })
});

const data = await response.json();
console.log(data);
```

### Python

```python
import requests

headers = {
    'Authorization': f'Bearer {token}',
    'Content-Type': 'application/json'
}

data = {
    'field1': 'example value',
    'field2': 42
}

response = requests.post(
    'https://api.example.com/api/v1/resource',
    headers=headers,
    json=data
)

result = response.json()
print(result)
```

### cURL

```bash
curl -X POST https://api.example.com/api/v1/resource \
  -H "Authorization: Bearer YOUR_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "field1": "example value",
    "field2": 42
  }'
```
```

### Step 5: Document Authentication

Provide clear authentication guidance:

```markdown
## Authentication

This API uses [Bearer Token / API Key / OAuth 2.0] authentication.

### Obtaining Credentials

1. [Step-by-step process to get API credentials]
2. [Where to find them in the dashboard]
3. [How to generate tokens]

### Using Authentication

Include your credentials in the request header:

```
Authorization: Bearer YOUR_TOKEN_HERE
```

### Example

```bash
curl -H "Authorization: Bearer abc123xyz789" \
  https://api.example.com/api/v1/resource
```

### Token Expiration

- Access tokens expire after [duration]
- Refresh tokens are valid for [duration]
- Use the `/refresh` endpoint to get a new access token

### Security Best Practices

- Never commit tokens to version control
- Rotate tokens regularly
- Use environment variables for storing tokens
- Implement token refresh logic in your application
```

### Step 6: Error Handling Documentation

Document errors comprehensively:

```markdown
## Error Handling

All errors follow this format:

```json
{
  "error": {
    "code": "ERROR_CODE",
    "message": "Human-readable error message",
    "details": {
      "field": "Additional context"
    }
  }
}
```

### Common Error Codes

| Code | Status | Description | Solution |
|------|--------|-------------|----------|
| INVALID_REQUEST | 400 | Request validation failed | Check request format and required fields |
| UNAUTHORIZED | 401 | Missing or invalid authentication | Verify your token is valid |
| FORBIDDEN | 403 | Insufficient permissions | Contact admin for access |
| NOT_FOUND | 404 | Resource doesn't exist | Verify the resource ID |
| RATE_LIMITED | 429 | Too many requests | Implement backoff and retry |
| SERVER_ERROR | 500 | Internal server error | Contact support if persists |

### Handling Errors

**Retry Logic:**
- Implement exponential backoff for 5xx errors
- Don't retry 4xx errors (except 429)
- Maximum 3 retry attempts recommended

**Example Error Handling:**

```javascript
async function makeAPIRequest() {
  try {
    const response = await fetch(url, options);

    if (!response.ok) {
      const error = await response.json();

      if (response.status === 429) {
        // Rate limited - wait and retry
        const retryAfter = response.headers.get('Retry-After');
        await sleep(retryAfter * 1000);
        return makeAPIRequest(); // Retry
      }

      throw new Error(`API Error: ${error.error.message}`);
    }

    return await response.json();
  } catch (err) {
    console.error('Request failed:', err);
    throw err;
  }
}
```
```

### Step 7: Create Quick Start Guide

Include a quick start section:

```markdown
## Quick Start

Get started with the API in 5 minutes.

### 1. Get Your API Key

[Instructions to obtain API key]

### 2. Make Your First Request

```bash
curl https://api.example.com/api/v1/users \
  -H "Authorization: Bearer YOUR_TOKEN"
```

### 3. Handle the Response

```json
{
  "users": [
    {"id": "1", "name": "Alice"},
    {"id": "2", "name": "Bob"}
  ]
}
```

### 4. Next Steps

- Explore the [Endpoints](#endpoints) section
- Check out [Code Examples](#code-examples)
- Read about [Error Handling](#error-handling)
```

## For GraphQL APIs

Use a modified structure:

```markdown
### Query: [QueryName]

Description of what this query does.

**Arguments:**
| Name | Type | Required | Description |
|------|------|----------|-------------|
| id | ID! | Yes | User identifier |

**Returns:** `User`

**Example Query:**

```graphql
query GetUser($id: ID!) {
  user(id: $id) {
    id
    name
    email
    createdAt
  }
}
```

**Variables:**

```json
{
  "id": "abc123"
}
```

**Response:**

```json
{
  "data": {
    "user": {
      "id": "abc123",
      "name": "Alice",
      "email": "alice@example.com",
      "createdAt": "2025-01-15T10:30:00Z"
    }
  }
}
```
```

## Documentation Guidelines

- **Be clear and concise**: Use simple language
- **Provide examples**: Show don't just tell
- **Be consistent**: Use the same format throughout
- **Include edge cases**: Document limitations and special cases
- **Keep it updated**: Note when endpoints are deprecated
- **Use proper formatting**:
  - Code blocks with syntax highlighting
  - Tables for structured data
  - Clear headers and sections
- **Test examples**: Ensure all code examples work
- **Link related sections**: Help users navigate

## Output Formats

Generate documentation in the requested format:

- **Markdown** (.md) - For GitHub, GitLab, static site generators
- **OpenAPI 3.0** (.yaml/.json) - For Swagger UI, Redoc
- **HTML** - For custom documentation sites
- **Postman Collection** (.json) - For Postman import

Ask the user which format they prefer if not specified.

## Validation

Before finalizing:

1. **Completeness check:**
   - All endpoints documented
   - All parameters explained
   - Examples provided
   - Error cases covered

2. **Accuracy check:**
   - Examples are correct
   - Types match implementation
   - URLs are valid
   - Authentication details are right

3. **Clarity check:**
   - Language is clear
   - Structure is logical
   - Navigation is easy
   - Examples are realistic

## Error Handling

- If API code is not accessible, ask user for details
- If authentication is unclear, ask for clarification
- If examples can't be tested, note this in documentation
- If API structure is complex, suggest breaking docs into multiple files

## Example Use Cases

### Example 1: Document REST API from Express Routes

User: "Document my Express API in the routes/ folder"

Response:
1. Use Glob to find route files: `routes/**/*.js`
2. Read each route file
3. Extract endpoints, methods, parameters
4. Generate documentation following the template
5. Create markdown file with complete documentation

### Example 2: Generate OpenAPI Spec

User: "Create an OpenAPI spec for my API"

Response:
1. Analyze the API implementation
2. Generate OpenAPI 3.0 YAML structure
3. Include all endpoints, schemas, parameters
4. Add examples and descriptions
5. Validate the spec is valid OpenAPI format

### Example 3: Document GraphQL API

User: "Document my GraphQL schema"

Response:
1. Read the GraphQL schema file
2. Extract types, queries, mutations
3. Document each operation with examples
4. Include authentication requirements
5. Provide example queries with variables
