# Common API Anti-Patterns and How to Avoid Them

## Introduction

This document outlines common anti-patterns in REST API design that can lead to poor developer experience, maintenance nightmares, and scalability issues. Each anti-pattern is accompanied by examples and recommended solutions.

## 1. Verb-Based URLs (The RPC Trap)

### Anti-Pattern
Using verbs in URLs instead of treating endpoints as resources.

```
❌ Bad Examples:
POST /api/getUsers
POST /api/createUser
GET  /api/deleteUser/123
POST /api/updateUserPassword
GET  /api/calculateOrderTotal/456
```

### Why It's Bad
- Violates REST principles
- Makes the API feel like RPC instead of REST
- HTTP methods lose their semantic meaning
- Reduces cacheability
- Harder to understand resource relationships

### Solution
```
✅ Good Examples:
GET    /api/users                    # Get users
POST   /api/users                    # Create user
DELETE /api/users/123               # Delete user
PATCH  /api/users/123/password      # Update password
GET    /api/orders/456/total        # Get order total
```

## 2. Inconsistent Naming Conventions

### Anti-Pattern
Mixed naming conventions across the API.

```json
❌ Bad Examples:
{
  "user_id": 123,           // snake_case
  "firstName": "John",      // camelCase
  "last-name": "Doe",       // kebab-case
  "EMAIL": "john@example.com", // UPPER_CASE
  "IsActive": true          // PascalCase
}
```

### Why It's Bad
- Confuses developers
- Increases cognitive load
- Makes code generation difficult
- Reduces API adoption

### Solution
```json
✅ Choose one convention and stick to it (camelCase recommended):
{
  "userId": 123,
  "firstName": "John",
  "lastName": "Doe",
  "email": "john@example.com",
  "isActive": true
}
```

## 3. Ignoring HTTP Status Codes

### Anti-Pattern
Always returning HTTP 200 regardless of the actual result.

```json
❌ Bad Example:
HTTP/1.1 200 OK
{
  "status": "error",
  "code": 404,
  "message": "User not found"
}
```

### Why It's Bad
- Breaks HTTP semantics
- Prevents proper error handling by clients
- Breaks caching and proxies
- Makes monitoring and debugging harder

### Solution
```json
✅ Good Example:
HTTP/1.1 404 Not Found
{
  "error": {
    "code": "USER_NOT_FOUND",
    "message": "User with ID 123 not found",
    "requestId": "req-abc123"
  }
}
```

## 4. Overly Complex Nested Resources

### Anti-Pattern
Creating deeply nested URL structures that are hard to navigate.

```
❌ Bad Example:
/companies/123/departments/456/teams/789/members/012/projects/345/tasks/678/comments/901
```

### Why It's Bad
- URLs become unwieldy
- Creates tight coupling between resources
- Makes independent resource access difficult
- Complicates authorization logic

### Solution
```
✅ Good Examples:
/tasks/678                    # Direct access to task
/tasks/678/comments          # Task comments
/users/012/tasks             # User's tasks
/projects/345?team=789       # Project filtering
```

## 5. Inconsistent Error Response Formats

### Anti-Pattern
Different error response structures across endpoints.

```json
❌ Bad Examples:
# Endpoint 1
{"error": "Invalid email"}

# Endpoint 2  
{"success": false, "msg": "User not found", "code": 404}

# Endpoint 3
{"errors": [{"field": "name", "message": "Required"}]}
```

### Why It's Bad
- Makes error handling complex for clients
- Reduces code reusability
- Poor developer experience

### Solution
```json
✅ Standardized Error Format:
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "The request contains invalid data",
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

## 6. Missing or Poor Pagination

### Anti-Pattern
Returning all results in a single response or inconsistent pagination.

```json
❌ Bad Examples:
# No pagination (returns 10,000 records)
GET /api/users

# Inconsistent pagination parameters
GET /api/users?page=1&size=10
GET /api/orders?offset=0&limit=20
GET /api/products?start=0&count=50
```

### Why It's Bad
- Can cause performance issues
- May overwhelm clients
- Inconsistent pagination parameters confuse developers
- No way to estimate total results

### Solution
```json
✅ Good Example:
GET /api/users?page=1&pageSize=10

{
  "data": [...],
  "pagination": {
    "page": 1,
    "pageSize": 10,
    "total": 150,
    "totalPages": 15,
    "hasNext": true,
    "hasPrev": false
  }
}
```

## 7. Exposing Internal Implementation Details

### Anti-Pattern
URLs and field names that reflect database structure or internal architecture.

```
❌ Bad Examples:
/api/user_table/123
/api/db_orders
/api/legacy_customer_data
/api/temp_migration_users

Response fields:
{
  "user_id_pk": 123,
  "internal_ref_code": "usr_abc",
  "db_created_timestamp": 1645123456
}
```

### Why It's Bad
- Couples API to internal implementation
- Makes refactoring difficult
- Exposes unnecessary technical details
- Reduces API longevity

### Solution
```
✅ Good Examples:
/api/users/123
/api/orders
/api/customers

Response fields:
{
  "id": 123,
  "referenceCode": "usr_abc",
  "createdAt": "2024-02-16T13:00:00Z"
}
```

## 8. Overloading Single Endpoint

### Anti-Pattern
Using one endpoint for multiple unrelated operations based on request parameters.

```
❌ Bad Example:
POST /api/user-actions
{
  "action": "create_user",
  "userData": {...}
}

POST /api/user-actions  
{
  "action": "delete_user",
  "userId": 123
}

POST /api/user-actions
{
  "action": "send_email",
  "userId": 123,
  "emailType": "welcome"
}
```

### Why It's Bad
- Breaks REST principles
- Makes documentation complex
- Complicates client implementation
- Reduces discoverability

### Solution
```
✅ Good Examples:
POST   /api/users              # Create user
DELETE /api/users/123         # Delete user  
POST   /api/users/123/emails   # Send email to user
```

## 9. Lack of Versioning Strategy

### Anti-Pattern
Making breaking changes without version management.

```
❌ Bad Examples:
# Original API
{
  "name": "John Doe",
  "age": 30
}

# Later (breaking change with no versioning)
{
  "firstName": "John",
  "lastName": "Doe", 
  "birthDate": "1994-02-16"
}
```

### Why It's Bad
- Breaks existing clients
- Forces all clients to update simultaneously
- No graceful migration path
- Reduces API stability

### Solution
```
✅ Good Examples:
# Version 1
GET /api/v1/users/123
{
  "name": "John Doe",
  "age": 30
}

# Version 2 (with both versions supported)
GET /api/v2/users/123
{
  "firstName": "John",
  "lastName": "Doe",
  "birthDate": "1994-02-16",
  "age": 30  // Backwards compatibility
}
```

## 10. Poor Error Messages

### Anti-Pattern
Vague, unhelpful, or technical error messages.

```json
❌ Bad Examples:
{"error": "Something went wrong"}
{"error": "Invalid input"}
{"error": "SQL constraint violation: FK_user_profile_id"}
{"error": "NullPointerException at line 247"}
```

### Why It's Bad
- Doesn't help developers fix issues
- Increases support burden
- Poor developer experience
- May expose sensitive information

### Solution
```json
✅ Good Examples:
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "The email address is required and must be in a valid format",
    "details": [
      {
        "field": "email",
        "code": "REQUIRED",
        "message": "Email address is required"
      }
    ]
  }
}
```

## 11. Ignoring Content Negotiation

### Anti-Pattern
Hard-coding response format without considering client preferences.

```
❌ Bad Example:
# Always returns JSON regardless of Accept header
GET /api/users/123
Accept: application/xml
# Returns JSON anyway
```

### Why It's Bad
- Reduces API flexibility
- Ignores HTTP standards
- Makes integration harder for diverse clients

### Solution
```
✅ Good Example:
GET /api/users/123
Accept: application/xml

HTTP/1.1 200 OK
Content-Type: application/xml

<?xml version="1.0"?>
<user>
  <id>123</id>
  <name>John Doe</name>
</user>
```

## 12. Stateful API Design

### Anti-Pattern
Maintaining session state on the server between requests.

```
❌ Bad Example:
# Step 1: Initialize session
POST /api/session/init

# Step 2: Set context (requires step 1)
POST /api/session/set-user/123

# Step 3: Get data (requires steps 1 & 2)
GET /api/session/user-data
```

### Why It's Bad
- Breaks REST statelessness principle
- Reduces scalability
- Makes caching difficult
- Complicates error recovery

### Solution
```
✅ Good Example:
# Self-contained requests
GET /api/users/123/data
Authorization: Bearer jwt-token-with-context
```

## 13. Inconsistent HTTP Method Usage

### Anti-Pattern
Using HTTP methods inappropriately or inconsistently.

```
❌ Bad Examples:
GET  /api/users/123/delete    # DELETE operation with GET
POST /api/users/123/get       # GET operation with POST
PUT  /api/users               # Creating with PUT on collection
GET  /api/users/search        # Search with side effects
```

### Why It's Bad
- Violates HTTP semantics
- Breaks caching and idempotency expectations
- Confuses developers and tools

### Solution
```
✅ Good Examples:
DELETE /api/users/123         # Delete with DELETE
GET    /api/users/123         # Get with GET
POST   /api/users             # Create on collection
GET    /api/users?q=search    # Safe search with GET
```

## 14. Missing Rate Limiting Information

### Anti-Pattern
Not providing rate limiting information to clients.

```
❌ Bad Example:
HTTP/1.1 429 Too Many Requests
{
  "error": "Rate limit exceeded"
}
```

### Why It's Bad
- Clients don't know when to retry
- No information about current limits
- Difficult to implement proper backoff strategies

### Solution
```
✅ Good Example:
HTTP/1.1 429 Too Many Requests
X-RateLimit-Limit: 1000
X-RateLimit-Remaining: 0
X-RateLimit-Reset: 1640995200
Retry-After: 3600

{
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "API rate limit exceeded",
    "retryAfter": 3600
  }
}
```

## 15. Chatty API Design

### Anti-Pattern
Requiring multiple API calls to accomplish common tasks.

```
❌ Bad Example:
# Get user profile requires 4 API calls
GET /api/users/123           # Basic info
GET /api/users/123/profile   # Profile details
GET /api/users/123/settings  # User settings
GET /api/users/123/stats     # User statistics
```

### Why It's Bad
- Increases latency
- Creates network overhead
- Makes mobile apps inefficient
- Complicates client implementation

### Solution
```
✅ Good Examples:
# Single call with expansion
GET /api/users/123?include=profile,settings,stats

# Or provide composite endpoints
GET /api/users/123/dashboard

# Or batch operations
POST /api/batch
{
  "requests": [
    {"method": "GET", "url": "/users/123"},
    {"method": "GET", "url": "/users/123/profile"}
  ]
}
```

## 16. No Input Validation

### Anti-Pattern
Accepting and processing invalid input without proper validation.

```json
❌ Bad Example:
POST /api/users
{
  "email": "not-an-email",
  "age": -5,
  "name": ""
}

# API processes this and fails later or stores invalid data
```

### Why It's Bad
- Leads to data corruption
- Security vulnerabilities
- Difficult to debug issues
- Poor user experience

### Solution
```json
✅ Good Example:
POST /api/users
{
  "email": "not-an-email",
  "age": -5,
  "name": ""
}

HTTP/1.1 400 Bad Request
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "The request contains invalid data",
    "details": [
      {
        "field": "email",
        "code": "INVALID_FORMAT",
        "message": "Email must be a valid email address"
      },
      {
        "field": "age",
        "code": "INVALID_RANGE",
        "message": "Age must be between 0 and 150"
      },
      {
        "field": "name",
        "code": "REQUIRED",
        "message": "Name is required and cannot be empty"
      }
    ]
  }
}
```

## 17. Synchronous Long-Running Operations

### Anti-Pattern
Blocking the client with long-running operations in synchronous endpoints.

```
❌ Bad Example:
POST /api/reports/generate
# Client waits 30 seconds for response
```

### Why It's Bad
- Poor user experience
- Timeouts and connection issues
- Resource waste on client and server
- Doesn't scale well

### Solution
```
✅ Good Example:
# Async pattern
POST /api/reports
HTTP/1.1 202 Accepted
Location: /api/reports/job-123
{
  "jobId": "job-123",
  "status": "processing",
  "estimatedCompletion": "2024-02-16T13:05:00Z"
}

# Check status
GET /api/reports/job-123
{
  "jobId": "job-123",
  "status": "completed",
  "result": "/api/reports/download/report-456"
}
```

## Prevention Strategies

### 1. API Design Reviews
- Implement mandatory design reviews
- Use checklists based on these anti-patterns
- Include multiple stakeholders

### 2. API Style Guides
- Create and enforce API style guides
- Use linting tools for consistency
- Regular training for development teams

### 3. Automated Testing
- Test for common anti-patterns
- Include contract testing
- Monitor API usage patterns

### 4. Documentation Standards
- Require comprehensive API documentation
- Include examples and error scenarios
- Keep documentation up-to-date

### 5. Client Feedback
- Regularly collect feedback from API consumers
- Monitor API usage analytics
- Conduct developer experience surveys

## Conclusion

Avoiding these anti-patterns requires:
- Understanding REST principles
- Consistent design standards
- Regular review and refactoring
- Focus on developer experience
- Proper tooling and automation

Remember: A well-designed API is an asset that grows in value over time, while a poorly designed API becomes a liability that hampers development and adoption.