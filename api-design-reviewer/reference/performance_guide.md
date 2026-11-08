# API Performance & Scaling Guide

Guide to building fast, scalable APIs that handle production load.

## Table of Contents
1. [Database Optimization](#database-optimization)
2. [Caching Strategies](#caching-strategies)
3. [Response Optimization](#response-optimization)
4. [Scaling Patterns](#scaling-patterns)
5. [Monitoring](#monitoring)

---

## Database Optimization

### N+1 Query Problem

**The Problem:**
```python
# ❌ BAD: N+1 queries
@app.get("/api/posts")
def get_posts():
    posts = db.query(Post).all()  # 1 query
    for post in posts:
        post.author = db.query(User).get(post.author_id)  # N queries
    return posts

# For 100 posts: 1 + 100 = 101 database queries!
```

**Solution: Eager Loading**
```python
# ✅ GOOD: 2 queries total
@app.get("/api/posts")
def get_posts():
    posts = db.query(Post).options(
        joinedload(Post.author)  # Eager load author
    ).all()
    return posts

# Total: 2 queries (posts + users)
```

**Solution: Batch Loading**
```python
# ✅ GOOD: Batch load related resources
@app.get("/api/posts")
def get_posts():
    posts = db.query(Post).all()  # 1 query
    author_ids = [p.author_id for p in posts]
    authors = db.query(User).filter(User.id.in_(author_ids)).all()  # 1 query
    author_map = {a.id: a for a in authors}

    for post in posts:
        post.author = author_map[post.author_id]

    return posts
```

### Database Indexes

```sql
-- ❌ Slow query without index
SELECT * FROM users WHERE email = 'alice@example.com';
-- Full table scan: O(n)

-- ✅ Fast with index
CREATE INDEX idx_users_email ON users(email);
SELECT * FROM users WHERE email = 'alice@example.com';
-- Index lookup: O(log n)
```

**Indexing Strategy:**
```sql
-- Primary key (automatic in most DBs)
CREATE TABLE users (
  id SERIAL PRIMARY KEY
);

-- Foreign keys (for joins)
CREATE INDEX idx_orders_user_id ON orders(user_id);

-- Frequently filtered columns
CREATE INDEX idx_users_status ON users(status);
CREATE INDEX idx_users_created_at ON users(created_at);

-- Composite index for multi-column queries
CREATE INDEX idx_orders_user_status ON orders(user_id, status);

-- Partial index (smaller, faster)
CREATE INDEX idx_active_users ON users(email) WHERE status = 'active';
```

**When to Index:**
- [ ] Primary keys (auto)
- [ ] Foreign keys (joins)
- [ ] Columns in WHERE clauses
- [ ] Columns in ORDER BY
- [ ] Columns in GROUP BY

**When NOT to Index:**
- [ ] Small tables (< 1000 rows)
- [ ] Columns with low cardinality (e.g., boolean)
- [ ] Frequently updated columns (index overhead)

### Query Optimization

```python
# ❌ BAD: Fetching all columns
users = db.query(User).all()

# ✅ GOOD: Select only needed columns
users = db.query(User.id, User.name, User.email).all()

# ❌ BAD: Loading entire collection
all_orders = user.orders  # Loads all orders into memory

# ✅ GOOD: Paginate
recent_orders = user.orders.order_by(Order.created_at.desc()).limit(10)

# ❌ BAD: Counting with full query
count = len(db.query(User).all())

# ✅ GOOD: Use COUNT
count = db.query(func.count(User.id)).scalar()
```

### Connection Pooling

```python
from sqlalchemy import create_engine
from sqlalchemy.pool import QueuePool

# ✅ GOOD: Connection pool configuration
engine = create_engine(
    "postgresql://user:pass@localhost/db",
    poolclass=QueuePool,
    pool_size=20,          # Normal connections
    max_overflow=10,       # Extra connections under load
    pool_timeout=30,       # Wait up to 30s for connection
    pool_recycle=3600,     # Recycle connections every hour
    pool_pre_ping=True     # Test connection before using
)
```

---

## Caching Strategies

### HTTP Caching

**ETag (Entity Tag):**
```python
from hashlib import md5

@app.get("/api/users/{id}")
def get_user(id: int, request: Request):
    user = db.query(User).get(id)
    user_json = user.to_json()

    # Generate ETag from content
    etag = md5(user_json.encode()).hexdigest()

    # Check If-None-Match header
    if request.headers.get("If-None-Match") == etag:
        return Response(status_code=304)  # Not Modified

    return Response(
        content=user_json,
        headers={
            "ETag": etag,
            "Cache-Control": "max-age=60"
        }
    )
```

**Cache-Control Headers:**
```python
@app.get("/api/products")
def get_products():
    products = db.query(Product).all()
    return Response(
        content=products,
        headers={
            # Cache for 5 minutes
            "Cache-Control": "public, max-age=300",
            # Or: private, no-cache, no-store, must-revalidate
        }
    )
```

### Application-Level Caching

**In-Memory Cache (Redis):**
```python
import redis
import json

cache = redis.Redis(host='localhost', port=6379, decode_responses=True)

@app.get("/api/user/{id}")
def get_user(id: int):
    # Try cache first
    cache_key = f"user:{id}"
    cached = cache.get(cache_key)

    if cached:
        return json.loads(cached)

    # Cache miss: Query database
    user = db.query(User).get(id)
    user_dict = user.to_dict()

    # Store in cache (TTL: 5 minutes)
    cache.setex(cache_key, 300, json.dumps(user_dict))

    return user_dict
```

**Cache Invalidation:**
```python
@app.patch("/api/users/{id}")
def update_user(id: int, data: UserUpdate):
    # Update database
    user = db.query(User).get(id)
    user.name = data.name
    db.commit()

    # Invalidate cache
    cache.delete(f"user:{id}")

    return user
```

**Cache-Aside Pattern:**
```python
def get_user_with_cache(user_id: int):
    # 1. Check cache
    user = cache.get(f"user:{user_id}")
    if user:
        return user

    # 2. Cache miss: Load from DB
    user = db.query(User).get(user_id)

    # 3. Store in cache
    if user:
        cache.setex(f"user:{user_id}", 300, user.to_json())

    return user
```

### Caching Strategies

| Strategy | When to Use | TTL |
|----------|-------------|-----|
| **No Cache** | Sensitive data, real-time | 0 |
| **Short Cache** | User profiles, dashboards | 1-5 min |
| **Medium Cache** | Product listings, blog posts | 10-30 min |
| **Long Cache** | Static content, reference data | 1-24 hours |
| **Immutable** | Versioned assets (JS, CSS, images) | 1 year |

---

## Response Optimization

### Compression

```python
from fastapi.middleware.gzip import GZipMiddleware

app = FastAPI()
app.add_middleware(GZipMiddleware, minimum_size=1000)

# Compresses responses > 1KB
# Typical savings: 60-80% for JSON
```

**Compression Comparison:**
```
Original JSON: 100 KB
Gzip:          20 KB (80% reduction)
Brotli:        15 KB (85% reduction)
```

### Pagination

**Cursor-Based (Recommended):**
```python
@app.get("/api/users")
def get_users(cursor: Optional[str] = None, limit: int = 50):
    if limit > 100:
        raise HTTPException(400, "Maximum limit is 100")

    query = db.query(User).order_by(User.id)

    if cursor:
        # Decode cursor (base64-encoded last ID)
        last_id = decode_cursor(cursor)
        query = query.filter(User.id > last_id)

    users = query.limit(limit + 1).all()

    has_more = len(users) > limit
    if has_more:
        users = users[:limit]

    next_cursor = encode_cursor(users[-1].id) if has_more else None

    return {
        "data": users,
        "pagination": {
            "next_cursor": next_cursor,
            "has_more": has_more
        }
    }
```

### Field Selection (Sparse Fieldsets)

```python
@app.get("/api/users")
def get_users(fields: Optional[str] = None):
    query = db.query(User)

    if fields:
        # Parse: ?fields=id,name,email
        requested_fields = fields.split(',')
        # Select only requested columns
        columns = [getattr(User, f) for f in requested_fields if hasattr(User, f)]
        query = db.query(*columns)

    return query.all()

# Request: GET /api/users?fields=id,name
# Response size: 1 KB (vs 10 KB for full object)
```

### Response Streaming

```python
from fastapi.responses import StreamingResponse

@app.get("/api/large-report")
def get_large_report():
    def generate():
        for chunk in generate_report_chunks():
            yield json.dumps(chunk) + "\n"

    return StreamingResponse(
        generate(),
        media_type="application/x-ndjson"
    )
```

---

## Scaling Patterns

### Horizontal Scaling

**Load Balancing:**
```
       ┌─────────────┐
       │Load Balancer│
       └──────┬──────┘
              │
      ┌───────┼───────┐
      │       │       │
   ┌──▼─┐  ┌──▼─┐  ┌──▼─┐
   │API1│  │API2│  │API3│
   └────┘  └────┘  └────┘
```

**Session Stickiness:**
- Use stateless auth (JWT, not server sessions)
- Store sessions in Redis (shared across instances)
- Or: sticky sessions at load balancer level

### Caching Layer

```
┌──────┐     ┌─────┐     ┌────────┐
│Client│────▶│Redis│────▶│Database│
└──────┘     └─────┘     └────────┘
              (Cache)
```

### CDN for Static Assets

```
GET /static/app.js
┌──────┐     ┌─────┐     ┌────────┐
│Client│────▶│ CDN │────▶│ Origin │
└──────┘     └─────┘     └────────┘
             (Edge Cache)
```

### Read Replicas

```
                  ┌─────────┐
         Writes──▶│ Primary │
                  └────┬────┘
                       │ Replication
              ┌────────┼────────┐
              │        │        │
         ┌────▼───┬────▼───┬────▼───┐
Reads───▶│Replica1│Replica2│Replica3│
         └────────┴────────┴────────┘
```

### Database Sharding

```
Users A-M: Shard1
Users N-Z: Shard2

def get_shard(user_id):
    first_letter = user_id[0].upper()
    if 'A' <= first_letter <= 'M':
        return shard1
    else:
        return shard2
```

---

## Rate Limiting

### Token Bucket Algorithm

```python
import time
from collections import defaultdict

class TokenBucket:
    def __init__(self, capacity: int, refill_rate: float):
        self.capacity = capacity
        self.refill_rate = refill_rate  # tokens per second
        self.buckets = defaultdict(lambda: {
            'tokens': capacity,
            'last_refill': time.time()
        })

    def allow_request(self, key: str) -> bool:
        bucket = self.buckets[key]
        now = time.time()

        # Refill tokens based on time elapsed
        elapsed = now - bucket['last_refill']
        bucket['tokens'] = min(
            self.capacity,
            bucket['tokens'] + elapsed * self.refill_rate
        )
        bucket['last_refill'] = now

        # Check if request allowed
        if bucket['tokens'] >= 1:
            bucket['tokens'] -= 1
            return True
        return False

# Allow 100 requests per minute
limiter = TokenBucket(capacity=100, refill_rate=100/60)

@app.get("/api/data")
def get_data(request: Request):
    client_ip = request.client.host
    if not limiter.allow_request(client_ip):
        raise HTTPException(429, "Rate limit exceeded")
    return {"data": "..."}
```

### Redis-Based Rate Limiting

```python
def rate_limit(key: str, limit: int, window: int) -> bool:
    """
    key: Unique identifier (user ID, IP address)
    limit: Max requests
    window: Time window in seconds
    """
    current = cache.get(key) or 0

    if int(current) >= limit:
        return False  # Rate limited

    pipe = cache.pipeline()
    pipe.incr(key)
    pipe.expire(key, window)
    pipe.execute()

    return True

@app.get("/api/data")
def get_data(current_user: User):
    # 1000 requests per hour per user
    if not rate_limit(f"rate:{current_user.id}", 1000, 3600):
        raise HTTPException(429, "Rate limit exceeded")
    return {"data": "..."}
```

---

## Monitoring

### Key Metrics

**Latency:**
- P50 (median)
- P95 (95th percentile)
- P99 (99th percentile)

```python
from prometheus_client import Histogram

request_duration = Histogram(
    'api_request_duration_seconds',
    'API request duration',
    ['method', 'endpoint']
)

@app.middleware("http")
async def metrics_middleware(request: Request, call_next):
    start = time.time()
    response = await call_next(request)
    duration = time.time() - start

    request_duration.labels(
        method=request.method,
        endpoint=request.url.path
    ).observe(duration)

    return response
```

**Throughput:**
- Requests per second
- Requests per minute

**Error Rate:**
- 4xx errors (client errors)
- 5xx errors (server errors)

**Resource Usage:**
- CPU utilization
- Memory usage
- Database connections
- Cache hit rate

### Alerting Thresholds

| Metric | Warning | Critical |
|--------|---------|----------|
| P95 Latency | > 500ms | > 1000ms |
| Error Rate | > 1% | > 5% |
| CPU Usage | > 70% | > 90% |
| Memory Usage | > 80% | > 95% |
| Cache Hit Rate | < 80% | < 50% |

---

## Performance Checklist

**Database:**
- [ ] Indexes on foreign keys and frequently queried columns
- [ ] N+1 queries eliminated (use eager loading)
- [ ] Connection pooling configured
- [ ] Queries optimized (use EXPLAIN)
- [ ] Appropriate use of transactions

**Caching:**
- [ ] HTTP caching headers (ETag, Cache-Control)
- [ ] Application-level caching (Redis, Memcached)
- [ ] Cache invalidation strategy defined
- [ ] Cache hit rate monitored

**API Design:**
- [ ] Pagination on all collections (max 100 items)
- [ ] Field selection supported (?fields=id,name)
- [ ] Compression enabled (gzip, brotli)
- [ ] Response size limits enforced

**Scaling:**
- [ ] Stateless design (horizontal scaling ready)
- [ ] Rate limiting per user/IP
- [ ] CDN for static assets
- [ ] Read replicas for read-heavy workloads

**Monitoring:**
- [ ] Latency tracked (P50, P95, P99)
- [ ] Error rates monitored
- [ ] Resource usage dashboards
- [ ] Alerts configured for anomalies

---

## Load Testing

**Tools:**
- k6 (JavaScript-based, great for APIs)
- Apache JMeter (GUI-based, feature-rich)
- Gatling (Scala-based, enterprise-grade)
- Locust (Python-based, distributed)

**k6 Example:**
```javascript
import http from 'k6/http';
import { check, sleep } from 'k6';

export const options = {
  stages: [
    { duration: '2m', target: 100 },  // Ramp up to 100 users
    { duration: '5m', target: 100 },  // Stay at 100 users
    { duration: '2m', target: 200 },  // Ramp up to 200 users
    { duration: '5m', target: 200 },  // Stay at 200 users
    { duration: '2m', target: 0 },    // Ramp down
  ],
  thresholds: {
    http_req_duration: ['p(95)<500'], // 95% of requests < 500ms
    http_req_failed: ['rate<0.01'],   // Error rate < 1%
  },
};

export default function () {
  const res = http.get('https://api.example.com/users');
  check(res, {
    'status is 200': (r) => r.status === 200,
    'response time < 500ms': (r) => r.timings.duration < 500,
  });
  sleep(1);
}
```

---

**Remember:** Premature optimization is the root of all evil. Measure first, optimize second. Focus on bottlenecks that actually impact user experience.
