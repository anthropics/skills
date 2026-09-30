# REST API Best Practices

Comprehensive guide to designing RESTful APIs following industry standards and battle-tested patterns.

## Table of Contents
1. [Resource Naming](#resource-naming)
2. [HTTP Methods](#http-methods)
3. [Status Codes](#status-codes)
4. [Request & Response Design](#request--response-design)
5. [URL Design](#url-design)
6. [Versioning](#versioning)
7. [Filtering, Sorting, Pagination](#filtering-sorting-pagination)
8. [HATEOAS](#hateoas)

---

## Resource Naming

### Use Plural Nouns
Resources represent collections; use plural nouns consistently.

```
✅ GOOD:
GET /users
GET /users/123
GET /orders
GET /products

❌ BAD:
GET /user
GET /getUser/123
GET /order
GET /product
```

### Use Kebab-Case for URLs
```
✅ GOOD:
/api/user-profiles
/api/order-items

❌ BAD:
/api/userProfiles  (camelCase)
/api/user_profiles (snake_case)
```

### Hierarchy and Nesting
Limit nesting to 2 levels maximum. Deeper hierarchies make URLs unwieldy.

```
✅ GOOD:
/users/123/orders
/orders/456/items

✅ BETTER (when relationship is clear):
/order-items?order_id=456

❌ BAD (too deep):
/users/123/orders/456/items/789/reviews
```

### Use Descriptive Names
Resource names should be self-explanatory.

```
✅ GOOD:
/api/invoices
/api/customers
/api/subscriptions

❌ BAD:
/api/inv
/api/cust
/api/subs
```

---

## HTTP Methods

### Standard CRUD Operations

| Method | Action | Idempotent | Safe | Success Codes |
|--------|--------|------------|------|---------------|
| GET | Read resource(s) | Yes | Yes | 200, 404 |
| POST | Create resource | No | No | 201, 400, 409 |
| PUT | Replace resource | Yes | No | 200, 201, 404 |
| PATCH | Update resource | No* | No | 200, 204, 404 |
| DELETE | Remove resource | Yes | No | 204, 404 |

*PATCH can be idempotent depending on implementation

### GET - Retrieve Resources
```http
GET /users/123
Response: 200 OK
{
  "id": 123,
  "name": "Alice",
  "email": "alice@example.com"
}
```

**Principles:**
- Never modify data
- Safe to retry
- Cacheable by default

### POST - Create New Resource
```http
POST /users
{
  "name": "Bob",
  "email": "bob@example.com"
}

Response: 201 Created
Location: /users/124
{
  "id": 124,
  "name": "Bob",
  "email": "bob@example.com",
  "created_at": "2024-11-01T10:30:00Z"
}
```

**Principles:**
- Returns 201 with Location header
- Include created resource in response
- Not idempotent (multiple POSTs create multiple resources)
- Use Idempotency-Key header to make it idempotent

### PUT - Full Resource Replacement
```http
PUT /users/123
{
  "name": "Alice Updated",
  "email": "alice.new@example.com"
}

Response: 200 OK
{
  "id": 123,
  "name": "Alice Updated",
  "email": "alice.new@example.com",
  "updated_at": "2024-11-01T11:00:00Z"
}
```

**Principles:**
- Replaces entire resource
- Idempotent (same request = same result)
- Can create resource if it doesn't exist (returns 201)
- Missing fields should be set to defaults/null

### PATCH - Partial Update
```http
PATCH /users/123
{
  "email": "alice.newer@example.com"
}

Response: 200 OK
{
  "id": 123,
  "name": "Alice Updated",  # Unchanged
  "email": "alice.newer@example.com",
  "updated_at": "2024-11-01T11:30:00Z"
}
```

**Principles:**
- Only updates provided fields
- Can be idempotent with proper design
- Use JSON Patch (RFC 6902) for complex updates
- Return updated resource

### DELETE - Remove Resource
```http
DELETE /users/123

Response: 204 No Content
```

**Principles:**
- Idempotent (deleting twice has same effect)
- 204 No Content on success (no body)
- 404 if resource doesn't exist (debatable: some prefer 204)
- Consider soft deletes for audit trails

### Avoid Action-Based URLs
```
❌ BAD:
POST /api/users/123/activate
POST /api/orders/456/cancel
POST /api/sendEmail

✅ GOOD:
PATCH /api/users/123 {"status": "active"}
PATCH /api/orders/456 {"status": "cancelled"}
POST /api/emails
```

---

## Status Codes

### Success Codes (2xx)

| Code | Meaning | When to Use |
|------|---------|-------------|
| 200 OK | Success | GET, PATCH, PUT with response body |
| 201 Created | Resource created | POST creating new resource |
| 202 Accepted | Async processing | Long-running operations queued |
| 204 No Content | Success, no body | DELETE, PUT/PATCH with no response |

### Client Error Codes (4xx)

| Code | Meaning | When to Use |
|------|---------|-------------|
| 400 Bad Request | Malformed request | Invalid JSON, wrong content type |
| 401 Unauthorized | Not authenticated | Missing/invalid auth token |
| 403 Forbidden | Not authorized | Valid auth but insufficient permissions |
| 404 Not Found | Resource missing | Resource ID doesn't exist |
| 405 Method Not Allowed | Wrong HTTP method | POST to read-only resource |
| 409 Conflict | Conflict with current state | Duplicate resource, version conflict |
| 422 Unprocessable Entity | Validation failed | Valid JSON but business rule violation |
| 429 Too Many Requests | Rate limited | Client exceeded rate limit |

### Server Error Codes (5xx)

| Code | Meaning | When to Use |
|------|---------|-------------|
| 500 Internal Server Error | Generic error | Unexpected server failure |
| 502 Bad Gateway | Upstream failure | Proxy/gateway error |
| 503 Service Unavailable | Temporarily unavailable | Maintenance, overload |
| 504 Gateway Timeout | Upstream timeout | Upstream service too slow |

### Status Code Examples

**Validation Error:**
```http
POST /users
{
  "name": "",
  "email": "invalid-email"
}

Response: 422 Unprocessable Entity
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "Request validation failed",
    "details": [
      {"field": "name", "issue": "must not be empty"},
      {"field": "email", "issue": "must be valid email format"}
    ]
  }
}
```

**Resource Conflict:**
```http
POST /users
{
  "email": "existing@example.com"
}

Response: 409 Conflict
{
  "error": {
    "code": "EMAIL_ALREADY_EXISTS",
    "message": "A user with this email already exists",
    "conflicting_resource": "/users/123"
  }
}
```

**Rate Limit Exceeded:**
```http
GET /api/users

Response: 429 Too Many Requests
Retry-After: 60
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 0
X-RateLimit-Reset: 1635724860

{
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "Rate limit exceeded. Try again in 60 seconds."
  }
}
```

---

## Request & Response Design

### Content Negotiation
```http
Request:
Accept: application/json
Accept-Language: en-US
Accept-Encoding: gzip, br

Response:
Content-Type: application/json; charset=utf-8
Content-Language: en-US
Content-Encoding: br
```

### JSON Response Structure

**Single Resource:**
```json
{
  "id": 123,
  "name": "Alice",
  "email": "alice@example.com",
  "created_at": "2024-01-01T00:00:00Z",
  "updated_at": "2024-11-01T10:00:00Z"
}
```

**Collection:**
```json
{
  "data": [
    {"id": 1, "name": "Alice"},
    {"id": 2, "name": "Bob"}
  ],
  "pagination": {
    "total": 1523,
    "limit": 50,
    "offset": 100,
    "next": "/users?offset=150&limit=50",
    "previous": "/users?offset=50&limit=50"
  }
}
```

**Error Response:**
```json
{
  "error": {
    "code": "RESOURCE_NOT_FOUND",
    "message": "User with ID 999 not found",
    "request_id": "req_abc123def456",
    "timestamp": "2024-11-01T10:30:00Z",
    "path": "/api/users/999",
    "documentation_url": "https://api.example.com/docs/errors"
  }
}
```

### Field Naming Conventions

**Use snake_case for JSON (recommended):**
```json
{
  "user_id": 123,
  "first_name": "Alice",
  "created_at": "2024-01-01T00:00:00Z"
}
```

**OR camelCase (also acceptable, but be consistent):**
```json
{
  "userId": 123,
  "firstName": "Alice",
  "createdAt": "2024-01-01T00:00:00Z"
}
```

**Never mix conventions!**

### Timestamps
Always use ISO 8601 format with UTC timezone:
```json
{
  "created_at": "2024-11-01T10:30:00Z",
  "updated_at": "2024-11-01T15:45:30.123Z"
}
```

### Nulls vs Omission
Decide on a convention:

**Option 1: Include null values**
```json
{
  "id": 123,
  "name": "Alice",
  "middle_name": null,
  "phone": null
}
```

**Option 2: Omit null values (saves bandwidth)**
```json
{
  "id": 123,
  "name": "Alice"
}
```

Choose one and be consistent. Document the behavior.

---

## URL Design

### API Base URL
```
✅ GOOD:
https://api.example.com/v1/users
https://example.com/api/v1/users

❌ BAD:
https://example.com/api.php?type=users
https://example.com/services/userservice
```

### Path Parameters vs Query Parameters

**Path Parameters:** For resource identification
```
GET /users/123
GET /orders/456/items/789
```

**Query Parameters:** For filtering, sorting, pagination
```
GET /users?role=admin&status=active
GET /products?category=electronics&sort=price&order=asc
GET /orders?page=2&limit=50
```

### Complex Queries

**Filtering:**
```
GET /products?category=electronics&min_price=100&max_price=500
GET /users?created_after=2024-01-01&status=active
```

**Sorting:**
```
GET /products?sort=price          # Ascending
GET /products?sort=-price         # Descending
GET /products?sort=price,-rating  # Multiple fields
```

**Field Selection:**
```
GET /users?fields=id,name,email
GET /users?include=profile,preferences
GET /users?exclude=sensitive_data
```

**Full-Text Search:**
```
GET /products/search?q=laptop&category=electronics
GET /users/search?q=alice
```

---

## Versioning

### URL Path Versioning (Recommended)
```
https://api.example.com/v1/users
https://api.example.com/v2/users
```

**Pros:**
- Explicit and visible
- Easy to route and cache
- Browser-testable

**Cons:**
- URLs change between versions

### Header Versioning
```http
GET /api/users
API-Version: 2024-11-01

or

GET /api/users
Accept: application/vnd.example.v2+json
```

**Pros:**
- Clean URLs
- RESTful (content negotiation)

**Cons:**
- Less visible
- Harder to test manually

### Best Practices
- Version from day one
- Use major versions only (`v1`, `v2`, not `v1.2.3`)
- Support N and N-1 versions simultaneously
- Deprecate old versions with clear timeline
- Document breaking vs non-breaking changes

---

## Filtering, Sorting, Pagination

### Filtering

**Simple Filters:**
```
GET /products?category=electronics
GET /users?role=admin&status=active
GET /orders?customer_id=123
```

**Range Filters:**
```
GET /products?min_price=100&max_price=500
GET /users?created_after=2024-01-01&created_before=2024-12-31
GET /orders?total_gte=1000
```

**Advanced Filters (URL-encoded):**
```
GET /products?filter[category]=electronics&filter[price][gte]=100
```

### Sorting

**Single Field:**
```
GET /products?sort=price
GET /products?sort=-created_at  # Descending
```

**Multiple Fields:**
```
GET /products?sort=category,price
GET /products?sort=category,-price
```

### Pagination

**Offset-Based:**
```
GET /users?offset=100&limit=50

Response:
{
  "data": [...],
  "pagination": {
    "offset": 100,
    "limit": 50,
    "total": 1523,
    "next": "/users?offset=150&limit=50",
    "previous": "/users?offset=50&limit=50"
  }
}
```

**Cursor-Based (Recommended for large datasets):**
```
GET /users?cursor=eyJpZCI6MTIzfQ&limit=50

Response:
{
  "data": [...],
  "pagination": {
    "next_cursor": "eyJpZCI6MTczfQ",
    "has_more": true,
    "limit": 50
  }
}
```

**Page-Based:**
```
GET /users?page=3&per_page=50

Response:
{
  "data": [...],
  "pagination": {
    "page": 3,
    "per_page": 50,
    "total_pages": 31,
    "total_items": 1523
  }
}
```

---

## HATEOAS

Hypermedia as the Engine of Application State: Include links to related resources.

### Basic Example
```json
{
  "id": 123,
  "name": "Alice",
  "email": "alice@example.com",
  "_links": {
    "self": {"href": "/users/123"},
    "orders": {"href": "/users/123/orders"},
    "profile": {"href": "/users/123/profile"}
  }
}
```

### HAL Format
```json
{
  "id": 123,
  "name": "Alice",
  "_links": {
    "self": {"href": "/users/123"},
    "orders": {"href": "/users/123/orders"}
  },
  "_embedded": {
    "orders": [
      {
        "id": 456,
        "total": 99.99,
        "_links": {
          "self": {"href": "/orders/456"}
        }
      }
    ]
  }
}
```

### Benefits
- Self-documenting
- Clients can navigate API without hardcoding URLs
- Evolvable (URLs can change)

---

## Caching

### Cache-Control Headers
```http
# Immutable static content
Cache-Control: public, max-age=31536000, immutable

# Frequently accessed data
Cache-Control: public, max-age=300, stale-while-revalidate=60

# Private user data
Cache-Control: private, max-age=0, must-revalidate

# Never cache
Cache-Control: no-store
```

### ETags
```http
GET /users/123
Response:
ETag: "33a64df551425fcc55e4d42a148795d9"
Cache-Control: max-age=60

# Conditional request
GET /users/123
If-None-Match: "33a64df551425fcc55e4d42a148795d9"

# Not modified
Response: 304 Not Modified
```

---

## Security Headers

```http
# CORS
Access-Control-Allow-Origin: https://example.com
Access-Control-Allow-Methods: GET, POST, PUT, DELETE
Access-Control-Allow-Headers: Authorization, Content-Type
Access-Control-Max-Age: 86400

# Security
Strict-Transport-Security: max-age=31536000; includeSubDomains
X-Content-Type-Options: nosniff
X-Frame-Options: DENY
Content-Security-Policy: default-src 'self'

# Rate Limiting
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 42
X-RateLimit-Reset: 1635724800
```

---

## Complete Example

```http
POST /api/v1/users HTTP/1.1
Host: api.example.com
Content-Type: application/json
Accept: application/json
Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...
Idempotency-Key: unique-client-key-123

{
  "email": "alice@example.com",
  "name": "Alice Smith",
  "role": "user"
}

HTTP/1.1 201 Created
Content-Type: application/json; charset=utf-8
Location: /api/v1/users/123
ETag: "abc123def456"
X-Request-ID: req_xyz789
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 99

{
  "id": 123,
  "email": "alice@example.com",
  "name": "Alice Smith",
  "role": "user",
  "status": "active",
  "created_at": "2024-11-01T10:30:00Z",
  "updated_at": "2024-11-01T10:30:00Z",
  "_links": {
    "self": {"href": "/api/v1/users/123"},
    "orders": {"href": "/api/v1/users/123/orders"},
    "profile": {"href": "/api/v1/users/123/profile"}
  }
}
```

---

## Summary

**Key Takeaways:**
1. Use plural nouns for resources
2. HTTP methods map to CRUD operations
3. Status codes communicate outcome precisely
4. Consistent JSON structure across API
5. Version from day one (URL path recommended)
6. Paginate all collections
7. Cache appropriately with ETags and Cache-Control
8. Include HATEOAS links for discoverability
9. Secure with authentication, rate limiting, CORS
10. Document everything with OpenAPI

Following these practices creates APIs that are intuitive, scalable, and maintainable.
