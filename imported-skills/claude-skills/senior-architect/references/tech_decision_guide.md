# Technology Decision Guide

Decision frameworks and comparison matrices for common technology choices.

## Decision Frameworks Index

1. [Database Selection](#1-database-selection)
2. [Caching Strategy](#2-caching-strategy)
3. [Message Queue Selection](#3-message-queue-selection)
4. [Authentication Strategy](#4-authentication-strategy)
5. [Frontend Framework Selection](#5-frontend-framework-selection)
6. [Cloud Provider Selection](#6-cloud-provider-selection)
7. [API Style Selection](#7-api-style-selection)

---

## 1. Database Selection

### SQL vs NoSQL Decision Matrix

| Factor | Choose SQL | Choose NoSQL |
|--------|-----------|--------------|
| Data relationships | Complex, many-to-many | Simple, denormalized OK |
| Schema | Well-defined, stable | Evolving, flexible |
| Transactions | ACID required | Eventual consistency OK |
| Query patterns | Complex joins, aggregations | Key-value, document lookups |
| Scale | Vertical (some horizontal) | Horizontal first |
| Team expertise | Strong SQL skills | Document/KV experience |

### Database Type Selection

**Relational (SQL):**
| Database | Best For | Avoid When |
|----------|----------|------------|
| PostgreSQL | General purpose, JSON support, extensions | Simple key-value only |
| MySQL | Web applications, read-heavy | Complex queries, JSON-heavy |
| SQLite | Embedded, development, small apps | Concurrent writes, scale |

**Document (NoSQL):**
| Database | Best For | Avoid When |
|----------|----------|------------|
| MongoDB | Flexible schema, rapid iteration | Complex transactions |
| CouchDB | Offline-first, sync required | High throughput |

**Key-Value:**
| Database | Best For | Avoid When |
|----------|----------|------------|
| Redis | Caching, sessions, real-time | Persistence critical |
| DynamoDB | Serverless, auto-scaling | Complex queries |

**Wide-Column:**
| Database | Best For | Avoid When |
|----------|----------|------------|
| Cassandra | Write-heavy, time-series | Complex queries, small scale |
| ScyllaDB | Cassandra alternative, performance | Small datasets |

**Time-Series:**
| Database | Best For | Avoid When |
|----------|----------|------------|
| TimescaleDB | Time-series with SQL | Non-time-series data |
| InfluxDB | Metrics, monitoring | Relational queries |

**Search:**
| Database | Best For | Avoid When |
|----------|----------|------------|
| Elasticsearch | Full-text search, logs | Primary data store |
| Meilisearch | Simple search, fast setup | Complex analytics |

### Quick Decision Flow

```
Start
  │
  ├─ Need ACID transactions? ──Yes──► PostgreSQL/MySQL
  │
  ├─ Flexible schema needed? ──Yes──► MongoDB
  │
  ├─ Write-heavy (>50K/sec)? ──Yes──► Cassandra/ScyllaDB
  │
  ├─ Key-value access only? ──Yes──► Redis/DynamoDB
  │
  ├─ Time-series data? ──Yes──► TimescaleDB/InfluxDB
  │
  ├─ Full-text search? ──Yes──► Elasticsearch
  │
  └─ Default ──────────────────────► PostgreSQL
```

---

## 2. Caching Strategy

### Cache Type Selection

| Type | Use Case | Invalidation | Complexity |
|------|----------|--------------|------------|
| Read-through | Frequent reads, tolerance for stale | On write/TTL | Low |
| Write-through | Data consistency critical | Automatic | Medium |
| Write-behind | High write throughput | Async | High |
| Cache-aside | Fine-grained control | Application | Medium |

### Cache Technology Selection

| Technology | Best For | Limitations |
|------------|----------|-------------|
| Redis | General purpose, data structures | Memory cost |
| Memcached | Simple key-value, high throughput | No persistence |
| CDN (CloudFront, Fastly) | Static assets, edge caching | Dynamic content |
| Application cache | Per-instance, small data | Not distributed |

### Cache Patterns

**Cache-Aside (Lazy Loading):**
```
Read:
1. Check cache
2. If miss, read from DB
3. Store in cache
4. Return data

Write:
1. Write to DB
2. Invalidate cache
```

**Write-Through:**
```
Write:
1. Write to cache
2. Cache writes to DB
3. Return success

Read:
1. Read from cache (always hit)
```

**TTL Guidelines:**

| Data Type | Suggested TTL |
|-----------|---------------|
| User sessions | 24-48 hours |
| API responses | 1-5 minutes |
| Static content | 24 hours - 1 week |
| Database queries | 5-60 minutes |
| Feature flags | 1-5 minutes |

---

## 3. Message Queue Selection

### Queue Technology Comparison

| Feature | RabbitMQ | Kafka | SQS | Redis Streams |
|---------|----------|-------|-----|---------------|
| Throughput | Medium (10K/s) | Very High (100K+/s) | Medium | High |
| Ordering | Per-queue | Per-partition | FIFO optional | Per-stream |
| Durability | Configurable | Strong | Strong | Configurable |
| Replay | No | Yes | No | Yes |
| Complexity | Medium | High | Low | Low |
| Cost | Self-hosted | Self-hosted | Pay-per-use | Self-hosted |

### Decision Matrix

| Requirement | Recommendation |
|-------------|----------------|
| Simple task queue | SQS or Redis |
| Event streaming | Kafka |
| Complex routing | RabbitMQ |
| Log aggregation | Kafka |
| Serverless integration | SQS |
| Real-time analytics | Kafka |
| Request/reply pattern | RabbitMQ |

### When to Use Each

**RabbitMQ:**
- Complex routing logic (topic, fanout, headers)
- Request/reply patterns
- Priority queues
- Message acknowledgment critical

**Kafka:**
- Event sourcing
- High throughput requirements (>50K messages/sec)
- Message replay needed
- Stream processing
- Log aggregation

**SQS:**
- AWS-native applications
- Simple queue semantics
- Serverless architectures
- Don't want to manage infrastructure

**Redis Streams:**
- Already using Redis
- Moderate throughput
- Simple streaming needs
- Real-time features

---

## 4. Authentication Strategy

### Method Selection

| Method | Best For | Avoid When |
|--------|----------|------------|
| Session-based | Traditional web apps, server-rendered | Mobile apps, microservices |
| JWT | SPAs, mobile apps, microservices | Need immediate revocation |
| OAuth 2.0 | Third-party access, social login | Internal-only apps |
| API Keys | Server-to-server, simple auth | User authentication |
| mTLS | Service mesh, high security | Public APIs |

### JWT vs Sessions

| Factor | JWT | Sessions |
|--------|-----|----------|
| Scalability | Stateless, easy to scale | Requires session store |
| Revocation | Difficult (need blocklist) | Immediate |
| Payload | Can contain claims | Server-side only |
| Security | Token in client | Server-controlled |
| Mobile friendly | Yes | Requires cookies |

### OAuth 2.0 Flow Selection

| Flow | Use Case |
|------|----------|
| Authorization Code | Web apps with backend |
| Authorization Code + PKCE | SPAs, mobile apps |
| Client Credentials | Machine-to-machine |
| Device Code | Smart TVs, CLI tools |

**Avoid:** Implicit flow (deprecated), Resource Owner Password (legacy only)

### Token Lifetimes

| Token Type | Suggested Lifetime |
|------------|-------------------|
| Access token | 15-60 minutes |
| Refresh token | 7-30 days |
| API key | No expiry (rotate quarterly) |
| Session | 24 hours - 7 days |

---

## 5. Frontend Framework Selection

### Framework Comparison

| Factor | React | Vue | Angular | Svelte |
|--------|-------|-----|---------|--------|
| Learning curve | Medium | Low | High | Low |
| Ecosystem | Largest | Large | Complete | Growing |
| Performance | Good | Good | Good | Excellent |
| Bundle size | Medium | Small | Large | Smallest |
| TypeScript | Good | Good | Native | Good |
| Job market | Largest | Growing | Enterprise | Niche |

### Decision Matrix

| Requirement | Recommendation |
|-------------|----------------|
| Large team, enterprise | Angular |
| Startup, rapid iteration | React or Vue |
| Performance critical | Svelte or Solid |
| Existing React team | React |
| Progressive enhancement | Vue or Svelte |
| Component library needed | React (most options) |

### Meta-Framework Selection

| Framework | Best For |
|-----------|----------|
| Next.js (React) | Full-stack React, SSR/SSG |
| Nuxt (Vue) | Full-stack Vue, SSR/SSG |
| SvelteKit | Full-stack Svelte |
| Remix | Data-heavy React apps |
| Astro | Content sites, multi-framework |

### When to Use SSR vs SPA vs SSG

| Rendering | Use When |
|-----------|----------|
| SSR | SEO critical, dynamic content, auth-gated |
| SPA | Internal tools, highly interactive, no SEO |
| SSG | Content sites, blogs, documentation |
| ISR | Mix of static and dynamic |

---

## 6. Cloud Provider Selection

### Provider Comparison

| Factor | AWS | GCP | Azure |
|--------|-----|-----|-------|
| Market share | Largest | Growing | Enterprise strong |
| Service breadth | Most comprehensive | Strong ML/data | Best Microsoft integration |
| Pricing | Complex, volume discounts | Simpler, sustained use | EA discounts |
| Kubernetes | EKS | GKE (best managed) | AKS |
| Serverless | Lambda (mature) | Cloud Functions | Azure Functions |
| Database | RDS, DynamoDB | Cloud SQL, Spanner | SQL, Cosmos |

### Decision Factors

| If You Need | Consider |
|-------------|----------|
| Microsoft ecosystem | Azure |
| Best Kubernetes experience | GCP |
| Widest service selection | AWS |
| Machine learning focus | GCP or AWS |
| Government compliance | AWS GovCloud or Azure Gov |
| Startup credits | All offer programs |

### Multi-Cloud Considerations

**Go multi-cloud when:**
- Regulatory requirements mandate it
- Specific service (e.g., GCP BigQuery) is best-in-class
- Negotiating leverage with vendors

**Stay single-cloud when:**
- Team is small
- Want to minimize complexity
- Deep integration needed

### Service Mapping

| Need | AWS | GCP | Azure |
|------|-----|-----|-------|
| Compute | EC2 | Compute Engine | Virtual Machines |
| Containers | ECS, EKS | GKE, Cloud Run | AKS, Container Apps |
| Serverless | Lambda | Cloud Functions | Azure Functions |
| Object Storage | S3 | Cloud Storage | Blob Storage |
| SQL Database | RDS | Cloud SQL | Azure SQL |
| NoSQL | DynamoDB | Firestore | Cosmos DB |
| CDN | CloudFront | Cloud CDN | Azure CDN |
| DNS | Route 53 | Cloud DNS | Azure DNS |

---

## 7. API Style Selection

### REST vs GraphQL vs gRPC

| Factor | REST | GraphQL | gRPC |
|--------|------|---------|------|
| Use case | General purpose | Flexible queries | Microservices |
| Learning curve | Low | Medium | High |
| Over-fetching | Common | Solved | N/A |
| Caching | HTTP native | Complex | Custom |
| Browser support | Native | Native | Limited |
| Tooling | Mature | Growing | Strong |
| Performance | Good | Good | Excellent |

### Decision Matrix

| Requirement | Recommendation |
|-------------|----------------|
| Public API | REST |
| Mobile apps with varied needs | GraphQL |
| Microservices communication | gRPC |
| Real-time updates | GraphQL subscriptions or WebSocket |
| File uploads | REST |
| Internal services only | gRPC |
| Third-party developers | REST + OpenAPI |

### When to Choose Each

**Choose REST when:**
- Building public APIs
- Need HTTP caching
- Simple CRUD operations
- Team experienced with REST

**Choose GraphQL when:**
- Multiple clients with different data needs
- Rapid frontend iteration
- Complex, nested data relationships
- Want to reduce API calls

**Choose gRPC when:**
- Service-to-service communication
- Performance critical
- Streaming required
- Strong typing important

### API Versioning Strategies

| Strategy | Pros | Cons |
|----------|------|------|
| URL path (`/v1/`) | Clear, easy to implement | URL pollution |
| Query param (`?version=1`) | Flexible | Easy to miss |
| Header (`Accept-Version: 1`) | Clean URLs | Less discoverable |
| No versioning (evolve) | Simple | Breaking changes risky |

**Recommendation:** URL path versioning for public APIs, header versioning for internal.

---

## Quick Reference

| Decision | Default Choice | Alternative When |
|----------|----------------|------------------|
| Database | PostgreSQL | Scale/flexibility → MongoDB, DynamoDB |
| Cache | Redis | Simple needs → Memcached |
| Queue | SQS (AWS) / RabbitMQ | Event streaming → Kafka |
| Auth | JWT + Refresh | Traditional web → Sessions |
| Frontend | React + Next.js | Simplicity → Vue, Performance → Svelte |
| Cloud | AWS | Microsoft shop → Azure, ML-first → GCP |
| API | REST | Mobile flexibility → GraphQL, Internal → gRPC |
