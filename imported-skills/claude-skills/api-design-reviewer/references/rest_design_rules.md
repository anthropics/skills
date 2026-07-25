# REST API Design Rules Reference

## Core Principles

### 1. Resources, Not Actions
REST APIs should focus on **resources** (nouns) rather than **actions** (verbs). The HTTP methods provide the actions.

```
✅ Good:
GET    /users           # Get all users
GET    /users/123       # Get user 123
POST   /users           # Create new user
PUT    /users/123       # Update user 123
DELETE /users/123       # Delete user 123

❌ Bad:
POST   /getUsers
POST   /createUser
POST   /updateUser/123
POST   /deleteUser/123
```

### 2. Hierarchical Resource Structure
Use hierarchical URLs to represent resource relationships:

```
/users/123/orders/456/items/789
```

But avoid excessive nesting (max 3-4 levels):

```
❌ Too deep: /companies/123/departments/456/teams/789/members/012/tasks/345
✅ Better:   /tasks/345?member=012&team=789
```

## Resource Naming Conventions

### URLs Should Use Kebab-Case
```
✅ Good:
/user-profiles
/order-items
/shipping-addresses

❌ Bad:
/userProfiles
/user_profiles
/orderItems
```

### Collections vs Individual Resources
```
Collection:   /users
Individual:   /users/123
Sub-resource: /users/123/orders
```

### Pluralization Rules
- Use **plural nouns** for collections: `/users`, `/orders`
- Use **singular nouns** for single resources: `/user-profile`, `/current-session`
- Be consistent throughout your API

## HTTP Methods Usage

### GET - Safe and Idempotent
- **Purpose**: Retrieve data
- **Safe**: No side effects
- **Idempotent**: Multiple calls return same result
- **Request Body**: Should not have one
- **Cacheable**: Yes

```
GET /users/123
GET /users?status=active&limit=10
```

### POST - Not Idempotent
- **Purpose**: Create resources, non-idempotent operations
- **Safe**: No
- **Idempotent**: No
- **Request Body**: Usually required
- **Cacheable**: Generally no

```
POST /users              # Create new user
POST /users/123/activate # Activate user (action)
```

### PUT - Idempotent
- **Purpose**: Create or completely replace a resource
- **Safe**: No
- **Idempotent**: Yes
- **Request Body**: Required (complete resource)
- **Cacheable**: No

```
PUT /users/123  # Replace entire user resource
```

### PATCH - Partial Update
- **Purpose**: Partially update a resource
- **Safe**: No
- **Idempotent**: Not necessarily
- **Request Body**: Required (partial resource)
- **Cacheable**: No

```
PATCH /users/123  # Update only specified fields
```

### DELETE - Idempotent
- **Purpose**: Remove a resource
- **Safe**: No
- **Idempotent**: Yes (same result if called multiple times)
- **Request Body**: Usually not needed
- **Cacheable**: No

```
DELETE /users/123
```

## Status Codes

### Success Codes (2xx)
- **200 OK**: Standard success response
- **201 Created**: Resource created successfully (POST)
- **202 Accepted**: Request accepted for processing (async)
- **204 No Content**: Success with no response body (DELETE, PUT)

### Redirection Codes (3xx)
- **301 Moved Permanently**: Resource permanently moved
- **302 Found**: Temporary redirect
- **304 Not Modified**: Use cached version

### Client Error Codes (4xx)
- **400 Bad Request**: Invalid request syntax or data
- **401 Unauthorized**: Authentication required
- **403 Forbidden**: Access denied (user authenticated but not authorized)
- **404 Not Found**: Resource not found
- **405 Method Not Allowed**: HTTP method not supported
- **409 Conflict**: Resource conflict (duplicates, version mismatch)
- **422 Unprocessable Entity**: Valid syntax but semantic errors
- **429 Too Many Requests**: Rate limit exceeded

### Server Error Codes (5xx)
- **500 Internal Server Error**: Unexpected server error
- **502 Bad Gateway**: Invalid response from upstream server
- **503 Service Unavailable**: Server temporarily unavailable
- **504 Gateway Timeout**: Upstream server timeout

## URL Design Patterns

### Query Parameters for Filtering
```
GET /users?status=active
GET /users?role=admin&department=engineering
GET /orders?created_after=2024-01-01&status=pending
```

### Pagination Parameters
```
# Offset-based
GET /users?offset=20&limit=10

# Cursor-based
GET /users?cursor=eyJpZCI6MTIzfQ&limit=10

# Page-based
GET /users?page=3&page_size=10
```

### Sorting Parameters
```
GET /users?sort=created_at          # Ascending
GET /users?sort=-created_at         # Descending (prefix with -)
GET /users?sort=last_name,first_name # Multiple fields
```

### Field Selection
```
GET /users?fields=id,name,email
GET /users/123?include=orders,profile
GET /users/123?exclude=internal_notes
```

### Search Parameters
```
GET /users?q=john
GET /products?search=laptop&category=electronics
```

## Response Format Standards

### Consistent Response Structure
```json
{
  "data": {
    "id": 123,
    "name": "John Doe",
    "email": "john@example.com"
  },
  "meta": {
    "timestamp": "2024-02-16T13:00:00Z",
    "version": "1.0"
  }
}
```

### Collection Responses
```json
{
  "data": [
    {"id": 1, "name": "Item 1"},
    {"id": 2, "name": "Item 2"}
  ],
  "pagination": {
    "total": 150,
    "page": 1,
    "pageSize": 10,
    "totalPages": 15,
    "hasNext": true,
    "hasPrev": false
  },
  "meta": {
    "timestamp": "2024-02-16T13:00:00Z"
  }
}
```

### Error Response Format
```json
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "The request contains invalid parameters",
    "details": [
      {
        "field": "email",
        "code": "INVALID_FORMAT",
        "message": "Email address is not valid"
      }
    ],
    "requestId": "req-123456",
    "timestamp": "2024-02-16T13:00:00Z"
  }
}
```

## Field Naming Conventions

### Use camelCase for JSON Fields
```json
✅ Good:
{
  "firstName": "John",
  "lastName": "Doe",
  "createdAt": "2024-02-16T13:00:00Z",
  "isActive": true
}

❌ Bad:
{
  "first_name": "John",
  "LastName": "Doe",
  "created-at": "2024-02-16T13:00:00Z"
}
```

### Boolean Fields
Use positive, clear names with "is", "has", "can", or "should" prefixes:

```json
✅ Good:
{
  "isActive": true,
  "hasPermission": false,
  "canEdit": true,
  "shouldNotify": false
}

❌ Bad:
{
  "active": true,
  "disabled": false,  // Double negative
  "permission": false // Unclear meaning
}
```

### Date/Time Fields
- Use ISO 8601 format: `2024-02-16T13:00:00Z`
- Include timezone information
- Use consistent field naming:

```json
{
  "createdAt": "2024-02-16T13:00:00Z",
  "updatedAt": "2024-02-16T13:30:00Z",
  "deletedAt": null,
  "publishedAt": "2024-02-16T14:00:00Z"
}
```

## Content Negotiation

### Accept Headers
```
Accept: application/json
Accept: application/xml
Accept: application/json; version=1
```

### Content-Type Headers
```
Content-Type: application/json
Content-Type: application/json; charset=utf-8
Content-Type: multipart/form-data
```

### Versioning via Headers
```
Accept: application/vnd.myapi.v1+json
API-Version: 1.0
```

## Caching Guidelines

### Cache-Control Headers
```
Cache-Control: public, max-age=3600        # Cache for 1 hour
Cache-Control: private, max-age=0          # Don't cache
Cache-Control: no-cache, must-revalidate   # Always validate
```

### ETags for Conditional Requests
```
HTTP/1.1 200 OK
ETag: "123456789"
Last-Modified: Wed, 21 Oct 2015 07:28:00 GMT

# Client subsequent request:
If-None-Match: "123456789"
If-Modified-Since: Wed, 21 Oct 2015 07:28:00 GMT
```

## Security Headers

### Authentication
```
Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...
Authorization: Basic dXNlcjpwYXNzd29yZA==
Authorization: Api-Key abc123def456
```

### CORS Headers
```
Access-Control-Allow-Origin: https://example.com
Access-Control-Allow-Methods: GET, POST, PUT, DELETE
Access-Control-Allow-Headers: Content-Type, Authorization
```

## Rate Limiting

### Rate Limit Headers
```
X-RateLimit-Limit: 1000
X-RateLimit-Remaining: 999
X-RateLimit-Reset: 1640995200
X-RateLimit-Window: 3600
```

### Rate Limit Exceeded Response
```json
HTTP/1.1 429 Too Many Requests
Retry-After: 3600

{
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "API rate limit exceeded",
    "details": {
      "limit": 1000,
      "window": "1 hour",
      "retryAfter": 3600
    }
  }
}
```

## Hypermedia (HATEOAS)

### Links in Responses
```json
{
  "id": 123,
  "name": "John Doe",
  "email": "john@example.com",
  "_links": {
    "self": {
      "href": "/users/123"
    },
    "orders": {
      "href": "/users/123/orders"
    },
    "edit": {
      "href": "/users/123",
      "method": "PUT"
    },
    "delete": {
      "href": "/users/123",
      "method": "DELETE"
    }
  }
}
```

### Link Relations
- **self**: Link to the resource itself
- **edit**: Link to edit the resource
- **delete**: Link to delete the resource
- **related**: Link to related resources
- **next/prev**: Pagination links

## Common Anti-Patterns to Avoid

### 1. Verbs in URLs
```
❌ Bad: /api/getUser/123
✅ Good: GET /api/users/123
```

### 2. Inconsistent Naming
```
❌ Bad: /user-profiles and /userAddresses
✅ Good: /user-profiles and /user-addresses
```

### 3. Deep Nesting
```
❌ Bad: /companies/123/departments/456/teams/789/members/012
✅ Good: /team-members/012?team=789
```

### 4. Ignoring HTTP Status Codes
```
❌ Bad: Always return 200 with error info in body
✅ Good: Use appropriate status codes (404, 400, 500, etc.)
```

### 5. Exposing Internal Structure
```
❌ Bad: /api/database_table_users
✅ Good: /api/users
```

### 6. No Versioning Strategy
```
❌ Bad: Breaking changes without version management
✅ Good: /api/v1/users or Accept: application/vnd.api+json;version=1
```

### 7. Inconsistent Error Responses
```
❌ Bad: Different error formats for different endpoints
✅ Good: Standardized error response structure
```

## Best Practices Summary

1. **Use nouns for resources, not verbs**
2. **Leverage HTTP methods correctly**
3. **Maintain consistent naming conventions**
4. **Implement proper error handling**
5. **Use appropriate HTTP status codes**
6. **Design for cacheability**
7. **Implement security from the start**
8. **Plan for versioning**
9. **Provide comprehensive documentation**
10. **Follow HATEOAS principles when applicable**

## Further Reading

- [RFC 7231 - HTTP/1.1 Semantics and Content](https://tools.ietf.org/html/rfc7231)
- [RFC 6570 - URI Template](https://tools.ietf.org/html/rfc6570)
- [OpenAPI Specification](https://swagger.io/specification/)
- [REST API Design Best Practices](https://www.restapitutorial.com/)
- [HTTP Status Code Definitions](https://httpstatuses.com/)