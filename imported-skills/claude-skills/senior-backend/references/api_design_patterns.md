# API Design Patterns

Concrete patterns for REST and GraphQL API design with examples.

## Patterns Index

1. [REST vs GraphQL Decision](#1-rest-vs-graphql-decision)
2. [Resource Naming Conventions](#2-resource-naming-conventions)
3. [API Versioning Strategies](#3-api-versioning-strategies)
4. [Error Handling Patterns](#4-error-handling-patterns)
5. [Pagination Patterns](#5-pagination-patterns)
6. [Authentication Patterns](#6-authentication-patterns)
7. [Rate Limiting Design](#7-rate-limiting-design)
8. [Idempotency Patterns](#8-idempotency-patterns)

---

## 1. REST vs GraphQL Decision

### When to Use REST

| Scenario | Why REST |
|----------|----------|
| Simple CRUD operations | Less complexity, widely understood |
| Public APIs | Better caching, easier documentation |
| File uploads/downloads | Native HTTP support |
| Microservices communication | Simpler service-to-service calls |
| Caching is critical | HTTP caching built-in |

### When to Use GraphQL

| Scenario | Why GraphQL |
|----------|-------------|
| Mobile apps with bandwidth constraints | Request only needed fields |
| Complex nested data | Single request for related data |
| Rapidly changing frontend requirements | Frontend-driven queries |
| Multiple client types | Each client queries what it needs |
| Real-time subscriptions needed | Built-in subscription support |

### Hybrid Approach

```
┌─────────────────────────────────────────────────────┐
│                    API Gateway                       │
├─────────────────────────────────────────────────────┤
│  /api/v1/*  →  REST (Public API, webhooks)          │
│  /graphql   →  GraphQL (Mobile apps, dashboards)    │
│  /files/*   →  REST (File uploads/downloads)        │
└─────────────────────────────────────────────────────┘
```

---

## 2. Resource Naming Conventions

### REST Endpoint Patterns

```
# Collections (plural nouns)
GET    /users              # List users
POST   /users              # Create user
GET    /users/{id}         # Get user
PUT    /users/{id}         # Replace user
PATCH  /users/{id}         # Update user
DELETE /users/{id}         # Delete user

# Nested resources
GET    /users/{id}/orders          # User's orders
POST   /users/{id}/orders          # Create order for user
GET    /users/{id}/orders/{orderId} # Specific order

# Actions (when CRUD doesn't fit)
POST   /users/{id}/activate        # Activate user
POST   /orders/{id}/cancel         # Cancel order
POST   /payments/{id}/refund       # Refund payment

# Filtering, sorting, pagination
GET    /users?status=active&sort=-created_at&limit=20&offset=40
GET    /orders?user_id=123&status=pending
```

### Naming Rules

| Rule | Good | Bad |
|------|------|-----|
| Use plural nouns | `/users` | `/user` |
| Use lowercase | `/user-profiles` | `/userProfiles` |
| Use hyphens | `/order-items` | `/order_items` |
| No verbs in URLs | `POST /orders` | `POST /createOrder` |
| No file extensions | `/users/123` | `/users/123.json` |

---

## 3. API Versioning Strategies

### Strategy Comparison

| Strategy | Example | Pros | Cons |
|----------|---------|------|------|
| URL Path | `/api/v1/users` | Explicit, easy routing | URL changes |
| Header | `Accept: application/vnd.api+json;version=1` | Clean URLs | Hidden version |
| Query Param | `/users?version=1` | Easy to test | Pollutes query string |

### Recommended: URL Path Versioning

```typescript
// Express routing
import v1Routes from './routes/v1';
import v2Routes from './routes/v2';

app.use('/api/v1', v1Routes);
app.use('/api/v2', v2Routes);
```

### Deprecation Strategy

```typescript
// Add deprecation headers
app.use('/api/v1', (req, res, next) => {
  res.set('Deprecation', 'true');
  res.set('Sunset', 'Sat, 01 Jun 2025 00:00:00 GMT');
  res.set('Link', '</api/v2>; rel="successor-version"');
  next();
}, v1Routes);
```

### Breaking vs Non-Breaking Changes

**Non-breaking (safe):**
- Adding new endpoints
- Adding optional fields
- Adding new enum values at end

**Breaking (requires new version):**
- Removing endpoints or fields
- Renaming fields
- Changing field types
- Changing required/optional status

---

## 4. Error Handling Patterns

### Standard Error Response Format

```json
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "Request validation failed",
    "details": [
      {
        "field": "email",
        "code": "INVALID_FORMAT",
        "message": "Must be a valid email address"
      },
      {
        "field": "age",
        "code": "OUT_OF_RANGE",
        "message": "Must be between 18 and 120"
      }
    ],
    "documentation_url": "https://api.example.com/docs/errors#validation"
  },
  "meta": {
    "request_id": "req_abc123",
    "timestamp": "2024-01-15T10:30:00Z"
  }
}
```

### Error Codes by Category

```typescript
// Client errors (4xx)
const ClientErrors = {
  VALIDATION_ERROR: 400,
  INVALID_JSON: 400,
  AUTHENTICATION_REQUIRED: 401,
  INVALID_TOKEN: 401,
  TOKEN_EXPIRED: 401,
  PERMISSION_DENIED: 403,
  RESOURCE_NOT_FOUND: 404,
  METHOD_NOT_ALLOWED: 405,
  CONFLICT: 409,
  RATE_LIMIT_EXCEEDED: 429,
};

// Server errors (5xx)
const ServerErrors = {
  INTERNAL_ERROR: 500,
  DATABASE_ERROR: 500,
  EXTERNAL_SERVICE_ERROR: 502,
  SERVICE_UNAVAILABLE: 503,
};
```

### Error Handler Implementation

```typescript
// Express error handler
interface ApiError extends Error {
  code: string;
  statusCode: number;
  details?: Array<{ field: string; message: string }>;
}

const errorHandler: ErrorRequestHandler = (err: ApiError, req, res, next) => {
  const statusCode = err.statusCode || 500;
  const code = err.code || 'INTERNAL_ERROR';

  // Log server errors
  if (statusCode >= 500) {
    logger.error({ err, requestId: req.id }, 'Server error');
  }

  res.status(statusCode).json({
    error: {
      code,
      message: statusCode >= 500 ? 'An unexpected error occurred' : err.message,
      details: err.details,
      ...(process.env.NODE_ENV === 'development' && { stack: err.stack }),
    },
    meta: {
      request_id: req.id,
      timestamp: new Date().toISOString(),
    },
  });
};
```

---

## 5. Pagination Patterns

### Offset-Based Pagination

```
GET /users?limit=20&offset=40

Response:
{
  "data": [...],
  "pagination": {
    "total": 1250,
    "limit": 20,
    "offset": 40,
    "has_more": true
  }
}
```

**Pros:** Simple, supports random access
**Cons:** Inconsistent with concurrent inserts/deletes

### Cursor-Based Pagination

```
GET /users?limit=20&cursor=eyJpZCI6MTIzfQ==

Response:
{
  "data": [...],
  "pagination": {
    "limit": 20,
    "next_cursor": "eyJpZCI6MTQzfQ==",
    "prev_cursor": "eyJpZCI6MTIzfQ==",
    "has_more": true
  }
}
```

**Pros:** Consistent with real-time data, efficient
**Cons:** No random access, cursor encoding required

### Implementation Example

```typescript
// Cursor-based pagination
interface CursorPagination {
  limit: number;
  cursor?: string;
  direction?: 'forward' | 'backward';
}

async function paginatedQuery<T>(
  query: QueryBuilder,
  { limit, cursor, direction = 'forward' }: CursorPagination
): Promise<{ data: T[]; nextCursor?: string; hasMore: boolean }> {
  // Decode cursor
  const decoded = cursor ? JSON.parse(Buffer.from(cursor, 'base64').toString()) : null;

  // Apply cursor condition
  if (decoded) {
    query = direction === 'forward'
      ? query.where('id', '>', decoded.id)
      : query.where('id', '<', decoded.id);
  }

  // Fetch one extra to check if more exist
  const results = await query.limit(limit + 1).orderBy('id', direction === 'forward' ? 'asc' : 'desc');

  const hasMore = results.length > limit;
  const data = hasMore ? results.slice(0, -1) : results;

  // Encode next cursor
  const nextCursor = hasMore
    ? Buffer.from(JSON.stringify({ id: data[data.length - 1].id })).toString('base64')
    : undefined;

  return { data, nextCursor, hasMore };
}
```

---

## 6. Authentication Patterns

### JWT Authentication Flow

```
┌──────────┐      1. Login        ┌──────────┐
│  Client  │ ──────────────────▶  │  Server  │
└──────────┘                      └──────────┘
                                       │
     2. Return JWT                     │
◀────────────────────────────────────────
     {access_token, refresh_token}     │
                                       │
     3. API Request                    │
───────────────────────────────────────▶
     Authorization: Bearer {token}     │
                                       │
     4. Validate & Respond             │
◀────────────────────────────────────────
```

### JWT Implementation

```typescript
import jwt from 'jsonwebtoken';

interface TokenPayload {
  userId: string;
  email: string;
  roles: string[];
}

// Generate tokens
function generateTokens(user: User): { accessToken: string; refreshToken: string } {
  const payload: TokenPayload = {
    userId: user.id,
    email: user.email,
    roles: user.roles,
  };

  const accessToken = jwt.sign(payload, process.env.JWT_SECRET!, {
    expiresIn: '15m',
    algorithm: 'RS256',
  });

  const refreshToken = jwt.sign(
    { userId: user.id, tokenVersion: user.tokenVersion },
    process.env.JWT_REFRESH_SECRET!,
    { expiresIn: '7d', algorithm: 'RS256' }
  );

  return { accessToken, refreshToken };
}

// Middleware
const authenticate: RequestHandler = async (req, res, next) => {
  const authHeader = req.headers.authorization;
  if (!authHeader?.startsWith('Bearer ')) {
    return res.status(401).json({ error: { code: 'AUTHENTICATION_REQUIRED' } });
  }

  try {
    const token = authHeader.slice(7);
    const payload = jwt.verify(token, process.env.JWT_SECRET!) as TokenPayload;
    req.user = payload;
    next();
  } catch (err) {
    if (err instanceof jwt.TokenExpiredError) {
      return res.status(401).json({ error: { code: 'TOKEN_EXPIRED' } });
    }
    return res.status(401).json({ error: { code: 'INVALID_TOKEN' } });
  }
};
```

### API Key Authentication (Service-to-Service)

```typescript
// API key middleware
const apiKeyAuth: RequestHandler = async (req, res, next) => {
  const apiKey = req.headers['x-api-key'] as string;

  if (!apiKey) {
    return res.status(401).json({ error: { code: 'API_KEY_REQUIRED' } });
  }

  // Hash and lookup (never store plain API keys)
  const hashedKey = crypto.createHash('sha256').update(apiKey).digest('hex');
  const client = await db.apiClients.findByHashedKey(hashedKey);

  if (!client || !client.isActive) {
    return res.status(401).json({ error: { code: 'INVALID_API_KEY' } });
  }

  req.apiClient = client;
  next();
};
```

---

## 7. Rate Limiting Design

### Rate Limit Headers

```
HTTP/1.1 200 OK
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 95
X-RateLimit-Reset: 1705312800
Retry-After: 60
```

### Tiered Rate Limits

```typescript
const rateLimits = {
  anonymous: { requests: 60, window: '1m' },
  authenticated: { requests: 1000, window: '1h' },
  premium: { requests: 10000, window: '1h' },
};

// Implementation with Redis
import { RateLimiterRedis } from 'rate-limiter-flexible';

const createRateLimiter = (tier: keyof typeof rateLimits) => {
  const config = rateLimits[tier];
  return new RateLimiterRedis({
    storeClient: redisClient,
    keyPrefix: `ratelimit:${tier}`,
    points: config.requests,
    duration: parseDuration(config.window),
  });
};
```

### Rate Limit Response

```json
{
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "Too many requests",
    "details": {
      "limit": 100,
      "window": "1 minute",
      "retry_after": 45
    }
  }
}
```

---

## 8. Idempotency Patterns

### Idempotency Key Header

```
POST /payments
Idempotency-Key: payment_abc123_attempt1
Content-Type: application/json

{
  "amount": 1000,
  "currency": "USD"
}
```

### Implementation

```typescript
const idempotencyMiddleware: RequestHandler = async (req, res, next) => {
  const idempotencyKey = req.headers['idempotency-key'] as string;

  if (!idempotencyKey) {
    return next(); // Optional for some endpoints
  }

  // Check for existing response
  const cached = await redis.get(`idempotency:${idempotencyKey}`);
  if (cached) {
    const { statusCode, body } = JSON.parse(cached);
    return res.status(statusCode).json(body);
  }

  // Store response after processing
  const originalJson = res.json.bind(res);
  res.json = (body: any) => {
    redis.setex(
      `idempotency:${idempotencyKey}`,
      86400, // 24 hours
      JSON.stringify({ statusCode: res.statusCode, body })
    );
    return originalJson(body);
  };

  next();
};
```

---

## Quick Reference: HTTP Methods

| Method | Idempotent | Safe | Cacheable | Request Body |
|--------|------------|------|-----------|--------------|
| GET | Yes | Yes | Yes | No |
| HEAD | Yes | Yes | Yes | No |
| POST | No | No | Conditional | Yes |
| PUT | Yes | No | No | Yes |
| PATCH | No | No | No | Yes |
| DELETE | Yes | No | No | Optional |
| OPTIONS | Yes | Yes | No | No |
