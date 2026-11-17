# API Design Review Checklist

Use this checklist when conducting API design reviews. Check off items as you review them.

---

## Pre-Review Context

- [ ] API type identified (REST, GraphQL, gRPC, WebSocket)
- [ ] Review scope defined (new API, changes, pre-launch audit)
- [ ] API specifications located and loaded
- [ ] Business context understood (use case, scale, SLAs)
- [ ] Target clients identified (web, mobile, third-party)

---

## Authentication & Authorization

### Authentication
- [ ] Authentication scheme clearly defined (OAuth2, JWT, API Keys, mTLS)
- [ ] Token format and structure documented
- [ ] Token expiration configured (≤ 1 hour for access tokens)
- [ ] Refresh token strategy implemented
- [ ] No credentials in URLs (use headers/body)
- [ ] Rate limiting on auth endpoints (prevent brute force)
- [ ] Multi-factor authentication supported (for sensitive operations)
- [ ] Password requirements enforced (min 12 chars, complexity)
- [ ] Passwords hashed with bcrypt/argon2 (never plaintext)

### Authorization
- [ ] Authorization checks on ALL sensitive endpoints
- [ ] Ownership verification for user resources
- [ ] Role-based access control (RBAC) implemented
- [ ] Principle of least privilege applied
- [ ] Admin operations require admin role verification
- [ ] Authorization happens server-side (never client-side)
- [ ] Default deny policy (explicit grants required)

**Priority:** P0 (Critical)

---

## Resource Design (REST)

- [ ] Resources use plural nouns (`/users`, not `/user`)
- [ ] HTTP verbs used correctly (GET, POST, PUT, PATCH, DELETE)
- [ ] GET requests are safe (no side effects) and idempotent
- [ ] PUT and DELETE are idempotent
- [ ] No action-based URLs (use resource + verb pattern)
- [ ] Resource hierarchy limited to 2 levels
- [ ] Consistent naming convention (snake_case or camelCase)
- [ ] URL parameters for filtering, path parameters for IDs

**Priority:** P1 (High)

---

## Error Handling

- [ ] Standardized error format across ALL endpoints
- [ ] Appropriate HTTP status codes used consistently
- [ ] Machine-readable error codes for programmatic handling
- [ ] Human-readable messages without exposing internals
- [ ] Validation errors specify which fields failed
- [ ] Request ID included in all responses
- [ ] Stack traces excluded from production responses
- [ ] Error documentation available

**Standard Error Format:**
```json
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "Invalid request parameters",
    "details": [...],
    "request_id": "req_abc123",
    "documentation_url": "https://api.example.com/docs/errors"
  }
}
```

**Priority:** P0 (Critical)

---

## Pagination & Data Loading

- [ ] ALL collection endpoints implement pagination
- [ ] Default page size reasonable (10-50 items)
- [ ] Maximum page size enforced (≤ 100-200)
- [ ] Cursor-based pagination for large/growing datasets
- [ ] Pagination response format consistent
- [ ] Filtering parameters documented and validated
- [ ] Sorting parameters validated
- [ ] Field selection supported (`?fields=id,name`)
- [ ] Total count optional (expensive query)

**Priority:** P0 (Critical) - Unbounded collections can crash API

---

## Versioning

- [ ] Versioning strategy defined and documented
- [ ] Version specified in every request (URL or header)
- [ ] Breaking vs non-breaking changes policy documented
- [ ] Deprecation timeline and process clear
- [ ] Multiple versions supportable simultaneously
- [ ] Support for N and N-1 versions planned
- [ ] Deprecation headers used (`Deprecation`, `Sunset`)

**Recommended:** URL path versioning (`/v1/`, `/v2/`)

**Priority:** P0 (Critical) - Essential from day one

---

## Idempotency & Retries

- [ ] POST/PATCH/DELETE support idempotency keys
- [ ] Idempotency-Key header accepted
- [ ] Duplicate requests return cached response (within TTL)
- [ ] Optimistic locking with ETags or version fields
- [ ] 409 Conflict for concurrent modifications
- [ ] Retry-After header for 429/503 responses
- [ ] Idempotency behavior documented

**Priority:** P1 (High) - Prevents duplicate charges/orders

---

## Performance & Scalability

### Database
- [ ] N+1 queries prevented (eager loading, dataloaders)
- [ ] Database indexes on foreign keys and filtered columns
- [ ] Connection pooling configured
- [ ] Query optimization verified (use EXPLAIN)

### Caching
- [ ] Cache-Control headers configured appropriately
- [ ] ETag support for conditional requests
- [ ] Application-level caching strategy defined
- [ ] Cache invalidation strategy documented
- [ ] Compression enabled (gzip, brotli)

### Response Optimization
- [ ] Response size limits enforced
- [ ] Field selection supported
- [ ] Large responses paginated
- [ ] Timeout configured on external calls

**Priority:** P1 (High)

---

## Data Validation & Security

### Input Validation
- [ ] All inputs validated (type, format, length, range)
- [ ] SQL injection prevention (parameterized queries/ORMs)
- [ ] XSS prevention (output encoding, CSP headers)
- [ ] Field length limits enforced
- [ ] Type validation on all fields
- [ ] Enum values validated
- [ ] Request size limits enforced (e.g., max 10MB)

### File Uploads
- [ ] File type whitelist (not blacklist)
- [ ] File size limits enforced
- [ ] Content-type verification (check actual content)
- [ ] Virus scanning (production)
- [ ] Files stored outside web root
- [ ] Randomized filenames

### Sensitive Data
- [ ] No sensitive data in URLs
- [ ] Passwords never in plaintext
- [ ] API keys/tokens in environment variables
- [ ] Sensitive fields excluded from responses
- [ ] PII redacted from logs
- [ ] HTTPS enforced everywhere

**Priority:** P0 (Critical) - Security vulnerabilities

---

## Rate Limiting

- [ ] Rate limiting implemented per IP
- [ ] Rate limiting per authenticated user
- [ ] Different limits for different endpoints
- [ ] Stricter limits on auth endpoints
- [ ] Stricter limits on expensive operations
- [ ] Rate limit headers in responses
- [ ] Retry-After header when rate limited

**Headers:**
```
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 42
X-RateLimit-Reset: 1635724800
Retry-After: 45
```

**Priority:** P1 (High) - Prevents abuse

---

## Documentation

- [ ] OpenAPI/Swagger spec available and accurate
- [ ] Every endpoint has description
- [ ] Request/response examples for each endpoint
- [ ] Authentication requirements clearly stated
- [ ] Error responses documented with codes
- [ ] Rate limits documented
- [ ] Interactive documentation available (Swagger UI, Redoc)
- [ ] Changelog maintained for API changes
- [ ] Migration guides for breaking changes

**Priority:** P1 (High) - Essential for API consumers

---

## GraphQL-Specific

(Skip if not GraphQL)

- [ ] Query depth limiting implemented (max 5-7 levels)
- [ ] Query complexity scoring implemented
- [ ] Pagination on ALL list fields (connections pattern)
- [ ] DataLoader pattern for batching
- [ ] Proper nullable vs non-nullable field design
- [ ] Field deprecation instead of removal
- [ ] Input validation on mutations
- [ ] Field-level authorization

**Priority:** P0 (Critical) - Prevents DoS

---

## Security (OWASP API Top 10)

- [ ] Broken Object Level Authorization (BOLA) prevented
- [ ] Broken Authentication protected
- [ ] Broken Object Property Level Authorization (mass assignment) prevented
- [ ] Unrestricted Resource Consumption limited
- [ ] Broken Function Level Authorization prevented
- [ ] Unrestricted Access to Sensitive Business Flows protected
- [ ] Server Side Request Forgery (SSRF) prevented
- [ ] Security Misconfiguration addressed
- [ ] Improper Inventory Management handled
- [ ] Unsafe Consumption of APIs protected

**Priority:** P0 (Critical)

---

## Monitoring & Logging

### Logging
- [ ] Authentication attempts logged
- [ ] Authorization failures logged
- [ ] Security events logged
- [ ] Request IDs in all logs
- [ ] Correlation IDs for distributed tracing
- [ ] Sensitive data NOT logged (passwords, tokens)

### Monitoring
- [ ] Latency tracked (P50, P95, P99)
- [ ] Error rates monitored (4xx, 5xx)
- [ ] Throughput monitored (requests/second)
- [ ] Resource usage tracked (CPU, memory, connections)
- [ ] Cache hit rate monitored
- [ ] Alerts configured for anomalies

### Observability
- [ ] Distributed tracing implemented
- [ ] Health check endpoint available
- [ ] Metrics endpoint exposed (Prometheus)
- [ ] Dashboards created

**Priority:** P1 (High) - Can't debug what you can't see

---

## Testing

- [ ] Unit tests for business logic
- [ ] Integration tests for database operations
- [ ] API contract tests
- [ ] Security tests (injection, XSS, auth bypass)
- [ ] Load tests at expected scale
- [ ] Different user role testing
- [ ] Error condition testing
- [ ] Edge case testing

**Priority:** P1 (High)

---

## Production Readiness

- [ ] Load testing completed at 2x expected traffic
- [ ] Disaster recovery plan documented
- [ ] Rollback procedure tested
- [ ] Circuit breakers on external dependencies
- [ ] Graceful degradation strategy
- [ ] Database migrations tested
- [ ] Backup and restore tested
- [ ] Runbooks created for common issues
- [ ] On-call rotation defined
- [ ] Incident response process documented

**Priority:** P0 (Critical) - Before launch

---

## Special API Types

### Public API (Additional)
- [ ] Excellent documentation (primary support channel)
- [ ] Formal SLA defined
- [ ] Aggressive rate limiting
- [ ] Security hardened (assume malicious actors)
- [ ] Developer support channel available

### Mobile Backend (Additional)
- [ ] Response sizes minimized (bandwidth)
- [ ] Offline support considered
- [ ] Push notifications instead of polling
- [ ] Graceful degradation for old app versions
- [ ] Field selection mandatory

### Microservices (Additional)
- [ ] Circuit breakers implemented
- [ ] Retry logic with exponential backoff
- [ ] Aggressive timeouts (fail fast)
- [ ] Service mesh considerations
- [ ] Contract testing between services

---

## Review Sign-off

### Critical Issues (P0)
- [ ] All P0 issues identified
- [ ] All P0 issues resolved or have mitigation plan
- [ ] No security vulnerabilities remain

### Important Issues (P1)
- [ ] All P1 issues documented
- [ ] Remediation timeline established

### Summary
- [ ] Overall assessment recorded
- [ ] Top 3 issues highlighted
- [ ] Recommendations prioritized
- [ ] Follow-up review scheduled (if needed)

---

## Approval

- [ ] **Ready for Launch** - All critical issues resolved
- [ ] **Ready with Minor Issues** - Can launch with P2/P3 issues
- [ ] **Needs Work** - P1 issues must be addressed
- [ ] **Major Concerns** - P0 issues block launch

**Reviewer:** _______________
**Date:** _______________
**Next Review:** _______________

---

## Notes

(Add any additional observations, concerns, or recommendations)

