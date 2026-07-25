---
name: "senior-backend"
description: Designs and implements backend systems including REST APIs, microservices, database architectures, authentication flows, and security hardening. Use when the user asks to "design REST APIs", "optimize database queries", "implement authentication", "build microservices", "review backend code", "set up GraphQL", "handle database migrations", or "load test APIs". Covers Node.js/Express/Fastify development, PostgreSQL optimization, API security, and backend architecture patterns.
---

# Senior Backend Engineer

Backend development patterns, API design, database optimization, and security practices.

---

## Quick Start

```bash
# Generate API routes from OpenAPI spec
python scripts/api_scaffolder.py openapi.yaml --framework express --output src/routes/

# Analyze database schema and generate migrations
python scripts/database_migration_tool.py --connection postgres://localhost/mydb --analyze

# Load test an API endpoint
python scripts/api_load_tester.py https://api.example.com/users --concurrency 50 --duration 30
```

---

## Tools Overview

### 1. API Scaffolder

Generates API route handlers, middleware, and OpenAPI specifications from schema definitions.

**Input:** OpenAPI spec (YAML/JSON) or database schema
**Output:** Route handlers, validation middleware, TypeScript types

**Usage:**
```bash
# Generate Express routes from OpenAPI spec
python scripts/api_scaffolder.py openapi.yaml --framework express --output src/routes/
# Output: Generated 12 route handlers, validation middleware, and TypeScript types

# Generate from database schema
python scripts/api_scaffolder.py --from-db postgres://localhost/mydb --output src/routes/

# Generate OpenAPI spec from existing routes
python scripts/api_scaffolder.py src/routes/ --generate-spec --output openapi.yaml
```

**Supported Frameworks:**
- Express.js (`--framework express`)
- Fastify (`--framework fastify`)
- Koa (`--framework koa`)

---

### 2. Database Migration Tool

Analyzes database schemas, detects changes, and generates migration files with rollback support.

**Input:** Database connection string or schema files
**Output:** Migration files, schema diff report, optimization suggestions

**Usage:**
```bash
# Analyze current schema and suggest optimizations
python scripts/database_migration_tool.py --connection postgres://localhost/mydb --analyze
# Output: Missing indexes, N+1 query risks, and suggested migration files

# Generate migration from schema diff
python scripts/database_migration_tool.py --connection postgres://localhost/mydb \
  --compare schema/v2.sql --output migrations/

# Dry-run a migration
python scripts/database_migration_tool.py --connection postgres://localhost/mydb \
  --migrate migrations/20240115_add_user_indexes.sql --dry-run
```

---

### 3. API Load Tester

Performs HTTP load testing with configurable concurrency, measuring latency percentiles and throughput.

**Input:** API endpoint URL and test configuration
**Output:** Performance report with latency distribution, error rates, throughput metrics

**Usage:**
```bash
# Basic load test
python scripts/api_load_tester.py https://api.example.com/users --concurrency 50 --duration 30
# Output: Throughput (req/sec), latency percentiles (P50/P95/P99), error counts, and scaling recommendations

# Test with custom headers and body
python scripts/api_load_tester.py https://api.example.com/orders \
  --method POST \
  --header "Authorization: Bearer token123" \
  --body '{"product_id": 1, "quantity": 2}' \
  --concurrency 100 \
  --duration 60

# Compare two endpoints
python scripts/api_load_tester.py https://api.example.com/v1/users https://api.example.com/v2/users \
  --compare --concurrency 50 --duration 30
```

---

## Backend Development Workflows

### API Design Workflow

Use when designing a new API or refactoring existing endpoints.

**Step 1: Define resources and operations**
```yaml
# openapi.yaml
openapi: 3.0.3
info:
  title: User Service API
  version: 1.0.0
paths:
  /users:
    get:
      summary: List users
      parameters:
        - name: "limit"
          in: query
          schema:
            type: integer
            default: 20
    post:
      summary: Create user
      requestBody:
        required: true
        content:
          application/json:
            schema:
              $ref: '#/components/schemas/CreateUser'
```

**Step 2: Generate route scaffolding**
```bash
python scripts/api_scaffolder.py openapi.yaml --framework express --output src/routes/
```

**Step 3: Implement business logic**
```typescript
// src/routes/users.ts (generated, then customized)
export const createUser = async (req: Request, res: Response) => {
  const { email, name } = req.body;

  // Add business logic
  const user = await userService.create({ email, name });

  res.status(201).json(user);
};
```

**Step 4: Add validation middleware**
```bash
# Validation is auto-generated from OpenAPI schema
# src/middleware/validators.ts includes:
# - Request body validation
# - Query parameter validation
# - Path parameter validation
```

**Step 5: Generate updated OpenAPI spec**
```bash
python scripts/api_scaffolder.py src/routes/ --generate-spec --output openapi.yaml
```

---

### Database Optimization Workflow

Use when queries are slow or database performance needs improvement.

**Step 1: Analyze current performance**
```bash
python scripts/database_migration_tool.py --connection $DATABASE_URL --analyze
```

**Step 2: Identify slow queries**
```sql
-- Check query execution plans
EXPLAIN ANALYZE SELECT * FROM orders
WHERE user_id = 123
ORDER BY created_at DESC
LIMIT 10;

-- Look for: Seq Scan (bad), Index Scan (good)
```

**Step 3: Generate index migrations**
```bash
python scripts/database_migration_tool.py --connection $DATABASE_URL \
  --suggest-indexes --output migrations/
```

**Step 4: Test migration (dry-run)**
```bash
python scripts/database_migration_tool.py --connection $DATABASE_URL \
  --migrate migrations/add_indexes.sql --dry-run
```

**Step 5: Apply and verify**
```bash
# Apply migration
python scripts/database_migration_tool.py --connection $DATABASE_URL \
  --migrate migrations/add_indexes.sql

# Verify improvement
python scripts/database_migration_tool.py --connection $DATABASE_URL --analyze
```

---

### Security Hardening Workflow

Use when preparing an API for production or after a security review.

**Step 1: Review authentication setup**
```typescript
// Verify JWT configuration
const jwtConfig = {
  secret: process.env.JWT_SECRET,  // Must be from env, never hardcoded
  expiresIn: '1h',                 // Short-lived tokens
  algorithm: 'RS256'               // Prefer asymmetric
};
```

**Step 2: Add rate limiting**
```typescript
import rateLimit from 'express-rate-limit';

const apiLimiter = rateLimit({
  windowMs: 15 * 60 * 1000,  // 15 minutes
  max: 100,                   // 100 requests per window
  standardHeaders: true,
  legacyHeaders: false,
});

app.use('/api/', apiLimiter);
```

**Step 3: Validate all inputs**
```typescript
import { z } from 'zod';

const CreateUserSchema = z.object({
  email: z.string().email().max(255),
  name: z.string().min(1).max(100),
  age: z.number().int().positive().optional()
});

// Use in route handler
const data = CreateUserSchema.parse(req.body);
```

**Step 4: Load test with attack patterns**
```bash
# Test rate limiting
python scripts/api_load_tester.py https://api.example.com/login \
  --concurrency 200 --duration 10 --expect-rate-limit

# Test input validation
python scripts/api_load_tester.py https://api.example.com/users \
  --method POST \
  --body '{"email": "not-an-email"}' \
  --expect-status 400
```

**Step 5: Review security headers**
```typescript
import helmet from 'helmet';

app.use(helmet({
  contentSecurityPolicy: true,
  crossOriginEmbedderPolicy: true,
  crossOriginOpenerPolicy: true,
  crossOriginResourcePolicy: true,
  hsts: { maxAge: 31536000, includeSubDomains: true },
}));
```

---

## Reference Documentation

| File | Contains | Use When |
|------|----------|----------|
| `references/api_design_patterns.md` | REST vs GraphQL, versioning, error handling, pagination | Designing new APIs |
| `references/database_optimization_guide.md` | Indexing strategies, query optimization, N+1 solutions | Fixing slow queries |
| `references/backend_security_practices.md` | OWASP Top 10, auth patterns, input validation | Security hardening |

---

## Common Patterns Quick Reference

### REST API Response Format
```json
{
  "data": { "id": 1, "name": "John" },
  "meta": { "requestId": "abc-123" }
}
```

### Error Response Format
```json
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "Invalid email format",
    "details": [{ "field": "email", "message": "must be valid email" }]
  },
  "meta": { "requestId": "abc-123" }
}
```

### HTTP Status Codes
| Code | Use Case |
|------|----------|
| 200 | Success (GET, PUT, PATCH) |
| 201 | Created (POST) |
| 204 | No Content (DELETE) |
| 400 | Validation error |
| 401 | Authentication required |
| 403 | Permission denied |
| 404 | Resource not found |
| 429 | Rate limit exceeded |
| 500 | Internal server error |

### Database Index Strategy
```sql
-- Single column (equality lookups)
CREATE INDEX idx_users_email ON users(email);

-- Composite (multi-column queries)
CREATE INDEX idx_orders_user_status ON orders(user_id, status);

-- Partial (filtered queries)
CREATE INDEX idx_orders_active ON orders(created_at) WHERE status = 'active';

-- Covering (avoid table lookup)
CREATE INDEX idx_users_email_name ON users(email) INCLUDE (name);
```

---

## Common Commands

```bash
# API Development
python scripts/api_scaffolder.py openapi.yaml --framework express
python scripts/api_scaffolder.py src/routes/ --generate-spec

# Database Operations
python scripts/database_migration_tool.py --connection $DATABASE_URL --analyze
python scripts/database_migration_tool.py --connection $DATABASE_URL --migrate file.sql

# Performance Testing
python scripts/api_load_tester.py https://api.example.com/endpoint --concurrency 50
python scripts/api_load_tester.py https://api.example.com/endpoint --compare baseline.json
```

---

## Assumptions and Verifiable Success Criteria (Karpathy discipline)

Before this skill scaffolds, recommends a pattern, or modifies a schema, the following four assumptions MUST be surfaced. If any are unknown, the skill stops and walks the [Forcing-question library](#forcing-question-library-matt-pocock-grill) instead.

1. **Read/write ratio + one-year p99 QPS** — drives DB, cache, queue, and partitioning choices. Kleppmann, *DDIA* (2017).
2. **Tenancy model** — single-tenant, shared multi-tenant, isolated multi-tenant. Drives data-access pattern.
3. **Data sensitivity tier** — public / internal / PII / PHI / PCI. Drives compliance floor.
4. **SLO + named error-budget consumer** — Google SRE Workbook canon. No SLO = no reliability work prioritization.

**Verifiable success criteria** (Karpathy #4) — every recommendation this skill emits must include:

- Latency targets (p50, p95, p99 in ms)
- Uptime / SLO target
- RPO + RTO

If any of those three is not stated, the recommendation is incomplete — return to Q7 of the forcing-question library.

The `scripts/backend_decision_engine.py` tool encodes these checks: it refuses to recommend a profile without read/write ratio + QPS + tenancy + data sensitivity + pattern preference.

---

## Customization profiles

Four built-in profiles in `profiles/` calibrate every recommendation:

| Profile | When to pick | Pattern | Latency floor (p99) |
|---|---|---|---|
| `node-express` | TS team, < 15 eng, customer-facing SaaS | Modular monolith on Postgres | 600ms |
| `fastapi-python` | Python team, < 20 eng, ML-adjacent | Modular monolith on Postgres (async) | 500ms |
| `django-monolith` | Content-heavy CRUD + admin, < 25 eng | Modular monolith on Postgres | 800ms |
| `go-or-rust-microservice` | Extracted service, ≥ 30 eng, platform team, QPS ≥ 1000 | Extracted service | 200ms |

Pick a profile via:

```bash
python scripts/backend_decision_engine.py \
  --team-size 8 --qps-p99 50 --read-write-ratio 20 \
  --tenancy shared-multi-tenant --data-sensitivity pii \
  --pattern modular-monolith --language-preference typescript
```

The tool returns the best-fit profile, runner-up tradeoff (if within 15%), stack picks, anti-patterns, named approvers, and SLO floor. **This tool never auto-approves.**

To add a custom profile: copy `profiles/node-express.json` to `profiles/<your-org>.json` and adjust `constraints` + `success_thresholds` + `named_approver_chain`.

---

## Composition map

This skill does NOT reimplement scope owned by the POWERFUL-tier specialists. It forks into them. See `references/composition_map.md` for the full routing table. Key forks:

| Concern | Fork into |
|---|---|
| API contract / breaking-change risk | `engineering/skills/api-design-reviewer/` |
| Schema design + ERD + indexing | `engineering/skills/database-designer/` |
| Zero-downtime schema migration | `engineering/skills/migration-architect/` |
| SLO + SLI + error-budget | `engineering/slo-architect/` |
| Observability / golden signals | `engineering/skills/observability-designer/` |
| CI/CD pipeline | `engineering/skills/ci-cd-pipeline-builder/` |
| Security / threat model | `engineering-team/skills/senior-security/`, `adversarial-reviewer` |
| Compliance evidence (HIPAA / ISO 27001) | `ra-qm-team/` |
| Pre-commit Karpathy review | `engineering/karpathy-coder/` |
| Pre-flight architecture grill | `engineering/grill-me/` |

The `cs-backend-engineer` agent orchestrates these forks via `context: fork`. Invoke it from another agent with `Agent({subagent_type: "cs-backend-engineer", prompt: "..."})` or via `/cs:backend-review <your problem>`.

---

## Forcing-question library (Matt Pocock grill)

Before locking any backend decision, walk the seven forcing questions in `references/forcing_questions.md`. Discipline:

1. One question per turn. No bundling.
2. Always recommend the answer with cited canon.
3. Track answers in `/tmp/backend-grill-<date>.md`.
4. If a kill criterion trips, stop. Don't scaffold around an unresolved gap.
5. After Q7, run `backend_decision_engine.py` with the seven answers.

Summary:

1. Read/write ratio + p99 QPS forecast?
2. Tenancy model — single / shared / isolated?
3. Sync / async / event-driven — default + exceptions?
4. Data sensitivity tier — PII / PHI / PCI?
5. Monolith / modular monolith / microservices — team-size justification?
6. RPO + RTO?
7. SLO + named error-budget consumer?

---

## Invocation from other agents and skills

Three surfaces:

1. **Slash command:** `/cs:backend-review <prompt>` — full grill + decision engine + composition routing.
2. **Agent subagent:** `Agent({subagent_type: "cs-backend-engineer", prompt: "..."})` — forks context, returns ≤ 200-word digest.
3. **Direct tool call:** `python scripts/backend_decision_engine.py ...` — deterministic profile match when inputs are known.

See `agents/engineering/cs-backend-engineer.md` for the full invocation contract.
