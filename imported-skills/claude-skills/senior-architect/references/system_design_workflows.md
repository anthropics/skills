# System Design Workflows

Step-by-step workflows for common system design tasks.

## Workflows Index

1. [System Design Interview Approach](#1-system-design-interview-approach)
2. [Capacity Planning Workflow](#2-capacity-planning-workflow)
3. [API Design Workflow](#3-api-design-workflow)
4. [Database Schema Design](#4-database-schema-design-workflow)
5. [Scalability Assessment](#5-scalability-assessment-workflow)
6. [Migration Planning](#6-migration-planning-workflow)

---

## 1. System Design Interview Approach

Use when designing a system from scratch or explaining architecture decisions.

### Step 1: Clarify Requirements (3-5 minutes)

**Functional requirements:**
- What are the core features?
- Who are the users?
- What actions can users take?

**Non-functional requirements:**
- Expected scale (users, requests/sec, data size)
- Latency requirements
- Availability requirements (99.9%? 99.99%?)
- Consistency requirements (strong? eventual?)

**Example questions to ask:**
```
- How many users? Daily active users?
- Read/write ratio?
- Data retention period?
- Geographic distribution?
- Peak vs average load?
```

### Step 2: Estimate Scale (2-3 minutes)

**Calculate key metrics:**
```
Users:        10M monthly active users
DAU:          1M daily active users
Requests:     100 req/user/day = 100M req/day
              = 1,200 req/sec (avg)
              = 3,600 req/sec (peak, 3x)

Storage:      1KB/request × 100M = 100GB/day
              = 36TB/year

Bandwidth:    100GB/day = 1.2 MB/sec (avg)
```

### Step 3: Design High-Level Architecture (5-10 minutes)

**Start with basic components:**
```
┌──────────┐     ┌──────────┐     ┌──────────┐
│  Client  │────▶│   API    │────▶│ Database │
└──────────┘     └──────────┘     └──────────┘
```

**Add components as needed:**
- Load balancer for traffic distribution
- Cache for read-heavy workloads
- CDN for static content
- Message queue for async processing
- Search index for complex queries

### Step 4: Deep Dive into Components (10-15 minutes)

**For each major component, discuss:**
- Why this technology choice?
- How does it handle failures?
- How does it scale?
- What are the trade-offs?

### Step 5: Address Bottlenecks (5 minutes)

**Common bottlenecks:**
- Database read/write capacity
- Network bandwidth
- Single points of failure
- Hot spots in data distribution

**Solutions:**
- Caching (Redis, Memcached)
- Database sharding
- Read replicas
- CDN for static content
- Async processing for non-critical paths

---

## 2. Capacity Planning Workflow

Use when estimating infrastructure requirements for a new system or feature.

### Step 1: Gather Requirements

| Metric | Current | 6 months | 1 year |
|--------|---------|----------|--------|
| Monthly active users | | | |
| Peak concurrent users | | | |
| Requests per second | | | |
| Data storage (GB) | | | |
| Bandwidth (Mbps) | | | |

### Step 2: Calculate Compute Requirements

**Web/API servers:**
```
Peak RPS:           3,600
Requests per server: 500 (conservative)
Servers needed:     3,600 / 500 = 8 servers

With redundancy (N+2): 10 servers
```

**CPU estimation:**
```
Per request: 50ms CPU time
Peak RPS:    3,600
CPU cores:   3,600 × 0.05 = 180 cores

With headroom (70% target utilization):
             180 / 0.7 = 257 cores
             = 32 servers × 8 cores
```

### Step 3: Calculate Storage Requirements

**Database storage:**
```
Records per day:    100,000
Record size:        2KB
Daily growth:       200MB

With indexes (2x):  400MB/day
Retention (1 year): 146GB

With replication (3x): 438GB
```

**File storage:**
```
Files per day:      10,000
Average file size:  500KB
Daily growth:       5GB

Retention (1 year): 1.8TB
```

### Step 4: Calculate Network Requirements

**Bandwidth:**
```
Response size:      10KB average
Peak RPS:           3,600
Outbound:           3,600 × 10KB = 36MB/s = 288 Mbps

With headroom (50%): 432 Mbps ≈ 500 Mbps connection
```

### Step 5: Document and Review

**Create capacity plan document:**
- Current requirements
- Growth projections
- Infrastructure recommendations
- Cost estimates
- Review triggers (when to re-evaluate)

---

## 3. API Design Workflow

Use when designing new APIs or refactoring existing ones.

### Step 1: Identify Resources

**List the nouns in your domain:**
```
E-commerce example:
- Users
- Products
- Orders
- Payments
- Reviews
```

### Step 2: Define Operations

**Map CRUD to HTTP methods:**
| Operation | HTTP Method | URL Pattern |
|-----------|-------------|-------------|
| List | GET | /resources |
| Get one | GET | /resources/{id} |
| Create | POST | /resources |
| Update | PUT/PATCH | /resources/{id} |
| Delete | DELETE | /resources/{id} |

### Step 3: Design Request/Response Formats

**Request example:**
```json
POST /api/v1/orders
Content-Type: application/json

{
  "customer_id": "cust-123",
  "items": [
    {"product_id": "prod-456", "quantity": 2}
  ],
  "shipping_address": {
    "street": "123 Main St",
    "city": "San Francisco",
    "state": "CA",
    "zip": "94102"
  }
}
```

**Response example:**
```json
HTTP/1.1 201 Created
Content-Type: application/json

{
  "id": "ord-789",
  "status": "pending",
  "customer_id": "cust-123",
  "items": [...],
  "total": 99.99,
  "created_at": "2024-01-15T10:30:00Z",
  "_links": {
    "self": "/api/v1/orders/ord-789",
    "customer": "/api/v1/customers/cust-123"
  }
}
```

### Step 4: Handle Errors Consistently

**Error response format:**
```json
HTTP/1.1 400 Bad Request
Content-Type: application/json

{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "Invalid request parameters",
    "details": [
      {
        "field": "quantity",
        "message": "must be greater than 0"
      }
    ]
  },
  "request_id": "req-abc123"
}
```

**Standard error codes:**
| HTTP Status | Use Case |
|-------------|----------|
| 400 | Validation errors |
| 401 | Authentication required |
| 403 | Permission denied |
| 404 | Resource not found |
| 409 | Conflict (duplicate, etc.) |
| 429 | Rate limit exceeded |
| 500 | Internal server error |

### Step 5: Document the API

**Include:**
- Authentication method
- Base URL and versioning
- Endpoints with examples
- Error codes and meanings
- Rate limits
- Pagination format

---

## 4. Database Schema Design Workflow

Use when designing a new database or major schema changes.

### Step 1: Identify Entities

**List the things you need to store:**
```
E-commerce:
- User (id, email, name, created_at)
- Product (id, name, price, stock)
- Order (id, user_id, status, total)
- OrderItem (id, order_id, product_id, quantity, price)
```

### Step 2: Define Relationships

**Relationship types:**
```
User ──1:N──▶ Order       (one user, many orders)
Order ──1:N──▶ OrderItem  (one order, many items)
Product ──1:N──▶ OrderItem (one product, many order items)
```

### Step 3: Choose Primary Keys

**Options:**
| Type | Pros | Cons |
|------|------|------|
| Auto-increment | Simple, ordered | Not distributed-friendly |
| UUID | Globally unique | Larger, random |
| ULID | Globally unique, sortable | Larger |

### Step 4: Add Indexes

**Index selection rules:**
```sql
-- Index columns used in WHERE clauses
CREATE INDEX idx_orders_user_id ON orders(user_id);

-- Index columns used in JOINs
CREATE INDEX idx_order_items_order_id ON order_items(order_id);

-- Index columns used in ORDER BY with WHERE
CREATE INDEX idx_orders_user_status ON orders(user_id, status);

-- Consider composite indexes for common queries
-- Query: SELECT * FROM orders WHERE user_id = ? AND status = 'active'
CREATE INDEX idx_orders_user_status ON orders(user_id, status);
```

### Step 5: Plan for Scale

**Partitioning strategies:**
```sql
-- Partition by date (time-series data)
CREATE TABLE events (
  id BIGINT,
  created_at TIMESTAMP,
  data JSONB
) PARTITION BY RANGE (created_at);

-- Partition by hash (distribute evenly)
CREATE TABLE users (
  id BIGINT,
  email VARCHAR(255)
) PARTITION BY HASH (id);
```

**Sharding considerations:**
- Shard key selection (user_id, tenant_id, etc.)
- Cross-shard query limitations
- Rebalancing strategy

---

## 5. Scalability Assessment Workflow

Use when evaluating if current architecture can handle growth.

### Step 1: Profile Current System

**Metrics to collect:**
```
Current load:
- Average requests/sec: ___
- Peak requests/sec: ___
- Average latency: ___ ms
- P99 latency: ___ ms
- Error rate: ___%

Resource utilization:
- CPU: ___%
- Memory: ___%
- Disk I/O: ___%
- Network: ___%
```

### Step 2: Identify Bottlenecks

**Check each layer:**
| Layer | Bottleneck Signs |
|-------|------------------|
| Web servers | High CPU, connection limits |
| Application | Slow requests, thread pool exhaustion |
| Database | Slow queries, lock contention |
| Cache | High miss rate, memory pressure |
| Network | Bandwidth saturation, latency |

### Step 3: Load Test

**Test scenarios:**
```
1. Baseline: Current production load
2. 2x load: Expected growth in 6 months
3. 5x load: Stress test
4. Spike: Sudden 10x for 5 minutes
```

**Tools:**
- k6, Locust, JMeter for HTTP
- pgbench for PostgreSQL
- redis-benchmark for Redis

### Step 4: Identify Scaling Strategy

**Vertical scaling (scale up):**
- Add more CPU, memory, disk
- Simpler but has limits
- Use when: Single server can handle more

**Horizontal scaling (scale out):**
- Add more servers
- Requires stateless design
- Use when: Need linear scaling

### Step 5: Create Scaling Plan

**Document:**
```
Trigger: When average CPU > 70% for 15 minutes

Action:
1. Add 2 more web servers
2. Update load balancer
3. Verify health checks pass

Rollback:
1. Remove added servers
2. Update load balancer
3. Investigate issue
```

---

## 6. Migration Planning Workflow

Use when migrating to new infrastructure, database, or architecture.

### Step 1: Assess Current State

**Document:**
- Current architecture diagram
- Data volumes
- Dependencies
- Integration points
- Performance baselines

### Step 2: Define Target State

**Document:**
- New architecture diagram
- Technology changes
- Expected improvements
- Success criteria

### Step 3: Plan Migration Strategy

**Strategies:**

| Strategy | Risk | Downtime | Complexity |
|----------|------|----------|------------|
| Big bang | High | Yes | Low |
| Blue-green | Medium | Minimal | Medium |
| Canary | Low | None | High |
| Strangler fig | Low | None | High |

**Strangler fig pattern (recommended for large systems):**
```
1. Add facade in front of old system
2. Route small percentage of traffic to new system
3. Gradually increase traffic to new system
4. Retire old system when 100% migrated
```

### Step 4: Create Rollback Plan

**For each step, define:**
```
Step: Migrate user service to new database

Rollback trigger:
- Error rate > 1%
- Latency > 500ms P99
- Data inconsistency detected

Rollback steps:
1. Route traffic back to old database
2. Sync any new data back
3. Investigate root cause

Rollback time estimate: 15 minutes
```

### Step 5: Execute with Checkpoints

**Migration checklist:**
```
□ Backup current system
□ Verify backup restoration works
□ Deploy new infrastructure
□ Run smoke tests on new system
□ Migrate small percentage (1%)
□ Monitor for 24 hours
□ Increase to 10%
□ Monitor for 24 hours
□ Increase to 50%
□ Monitor for 24 hours
□ Complete migration (100%)
□ Decommission old system
□ Document lessons learned
```

---

## Quick Reference

| Task | Start Here |
|------|------------|
| New system design | [System Design Interview Approach](#1-system-design-interview-approach) |
| Infrastructure sizing | [Capacity Planning](#2-capacity-planning-workflow) |
| New API | [API Design](#3-api-design-workflow) |
| Database design | [Database Schema Design](#4-database-schema-design-workflow) |
| Handle growth | [Scalability Assessment](#5-scalability-assessment-workflow) |
| System migration | [Migration Planning](#6-migration-planning-workflow) |
