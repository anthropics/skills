# SaaS Architecture Patterns

## Overview

This reference covers the key architectural decisions when building SaaS applications. Each pattern includes trade-offs and decision criteria to help teams make informed choices early in the development process.

## Multi-Tenancy Models

### 1. Shared Database (Shared Schema)

All tenants share the same database and tables, distinguished by a `tenant_id` column.

**Pros:**
- Lowest infrastructure cost
- Simplest deployment and maintenance
- Easy cross-tenant analytics
- Fastest time to market

**Cons:**
- Risk of data leakage between tenants
- Noisy neighbor performance issues
- Complex data isolation enforcement
- Harder to meet data residency requirements

**Best for:** Early-stage products, SMB customers, cost-sensitive deployments

### 2. Schema-Per-Tenant

Each tenant gets their own database schema within a shared database instance.

**Pros:**
- Better data isolation than shared schema
- Easier per-tenant backup and restore
- Moderate infrastructure efficiency
- Can customize schema per tenant if needed

**Cons:**
- Schema migration complexity at scale (N migrations per update)
- Connection pooling challenges
- Database instance limits on schema count
- Moderate operational complexity

**Best for:** Mid-market products, moderate tenant count (100-1,000)

### 3. Database-Per-Tenant

Each tenant gets a completely separate database instance.

**Pros:**
- Maximum data isolation and security
- Per-tenant performance tuning
- Easy data residency compliance
- Simple per-tenant backup/restore
- No noisy neighbor issues

**Cons:**
- Highest infrastructure cost
- Complex deployment automation required
- Cross-tenant queries/analytics challenging
- Connection management overhead

**Best for:** Enterprise products, regulated industries (healthcare, finance), high-value customers

### Decision Matrix

| Factor | Shared DB | Schema-Per-Tenant | DB-Per-Tenant |
|--------|-----------|-------------------|---------------|
| Cost | Low | Medium | High |
| Isolation | Low | Medium | High |
| Scale (tenants) | 10,000+ | 100-1,000 | 10-100 |
| Compliance | Basic | Moderate | Full |
| Complexity | Low | Medium | High |
| Performance | Shared | Moderate | Dedicated |

## API-First Design

### Principles
1. **API before UI** - Design the API contract before building any frontend
2. **Versioning from day one** - Use URL versioning (`/v1/`) or header-based
3. **Consistent conventions** - RESTful resources, standard HTTP methods, consistent error format
4. **Documentation as code** - OpenAPI/Swagger specification maintained alongside code

### REST API Standards
- Use nouns for resources (`/users`, `/projects`)
- Use HTTP methods semantically (GET=read, POST=create, PUT=update, DELETE=remove)
- Return appropriate status codes (200, 201, 400, 401, 403, 404, 429, 500)
- Implement pagination (cursor-based for large datasets, offset for small)
- Support filtering, sorting, and field selection
- Rate limiting with clear headers (X-RateLimit-Limit, X-RateLimit-Remaining)

### API Design Checklist
- [ ] OpenAPI 3.0+ specification created
- [ ] Authentication (API keys, OAuth2, JWT) documented
- [ ] Error response format standardized
- [ ] Rate limiting implemented and documented
- [ ] Pagination strategy defined
- [ ] Webhook support for async events
- [ ] SDKs planned for primary languages

## Event-Driven Architecture

### When to Use
- Decoupling services that evolve independently
- Handling asynchronous workflows (notifications, integrations)
- Building audit trails and activity feeds
- Enabling real-time features (live updates, collaboration)

### Event Patterns
- **Event Notification**: Lightweight event triggers consumer to fetch data
- **Event-Carried State Transfer**: Event contains all needed data
- **Event Sourcing**: Store state as sequence of events, derive current state

### Implementation Options
- **Message Queues**: RabbitMQ, Amazon SQS (point-to-point)
- **Event Streams**: Apache Kafka, Amazon Kinesis (pub/sub, replay)
- **Managed PubSub**: Google Pub/Sub, AWS EventBridge
- **In-App**: Redis Streams for lightweight event handling

## CQRS (Command Query Responsibility Segregation)

### Pattern
- Separate read models (optimized for queries) from write models (optimized for commands)
- Write side handles business logic and validation
- Read side provides denormalized views for fast retrieval

### When to Use
- Read/write ratio is heavily skewed (90%+ reads)
- Complex domain logic on write side
- Different scaling needs for reads vs writes
- Multiple read representations of same data needed

### When to Avoid
- Simple CRUD applications
- Small-scale applications where complexity is not justified
- Teams without event-driven architecture experience

## Microservices vs Monolith Decision Matrix

| Factor | Monolith | Microservices |
|--------|----------|--------------|
| Team size | < 10 engineers | > 10 engineers |
| Product maturity | Early stage, exploring | Established, scaling |
| Deployment frequency | Weekly-monthly | Daily per service |
| Domain complexity | Single bounded context | Multiple bounded contexts |
| Scaling needs | Uniform | Service-specific |
| Operational maturity | Low (no DevOps team) | High (platform team) |
| Time to market | Faster initially | Slower initially, faster later |

### Recommended Path
1. **Start monolith** - Get to product-market fit fast
2. **Modular monolith** - Organize code into bounded contexts
3. **Extract services** - Move high-change or high-scale modules to services
4. **Full microservices** - Only when team and infrastructure justify it

## Serverless Considerations

### Good Fit
- Infrequent or bursty workloads
- Event-driven processing (webhooks, file processing, notifications)
- API endpoints with variable traffic
- Scheduled jobs and background tasks

### Poor Fit
- Long-running processes (>15 min)
- WebSocket connections
- Latency-sensitive operations (cold start impact)
- Heavy compute workloads

### Serverless Patterns for SaaS
- **API Gateway + Lambda**: HTTP request handling
- **Event processing**: S3/SQS triggers for async work
- **Scheduled tasks**: CloudWatch Events for cron jobs
- **Edge computing**: CloudFront Functions for personalization

## Infrastructure Recommendations by Stage

| Stage | Users | Architecture | Database | Hosting |
|-------|-------|-------------|----------|---------|
| MVP | 0-100 | Monolith | Shared PostgreSQL | Single server / PaaS |
| Growth | 100-10K | Modular monolith | Managed DB, read replicas | Auto-scaling group |
| Scale | 10K-100K | Service extraction | DB per service, caching | Kubernetes / ECS |
| Enterprise | 100K+ | Microservices | Polyglot persistence | Multi-region, CDN |
