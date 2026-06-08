# Database Layer (2025-2026)

## ORM Decision: Drizzle vs Prisma 7

### The 2025 Situation
Prisma 7 (late 2025) removed the Rust query engine and went pure TypeScript — this closed ~70% of the performance gap with Drizzle. The decision now hinges on developer experience and deployment target, not raw performance.

### Drizzle ORM — When to Use
**Choose Drizzle for**: serverless/edge deployments, developers who think in SQL, minimal bundle size requirements, D1/LibSQL/Turso targets.

```ts
// Schema definition (TypeScript-native):
import { pgTable, serial, text, timestamp, integer } from 'drizzle-orm/pg-core';

export const posts = pgTable('posts', {
  id: serial('id').primaryKey(),
  title: text('title').notNull(),
  content: text('content').notNull(),
  authorId: integer('author_id').references(() => users.id),
  createdAt: timestamp('created_at').defaultNow().notNull(),
});

// Queries (SQL-like API):
const result = await db
  .select({ id: posts.id, title: posts.title, author: users.name })
  .from(posts)
  .leftJoin(users, eq(posts.authorId, users.id))
  .where(and(eq(posts.published, true), gte(posts.createdAt, oneWeekAgo)))
  .orderBy(desc(posts.createdAt))
  .limit(20);

// Migrations:
drizzle-kit generate  // generates SQL migration files
drizzle-kit migrate   // applies migrations
```

Key Drizzle stats:
- ~7.4KB gzipped bundle (vs Prisma 7's ~80KB — still smaller even post-rewrite)
- ~45ms cold start vs ~320ms for older Prisma (Prisma 7 has improved significantly)
- Works on Cloudflare Workers D1, Turso/LibSQL, and all major PostgreSQL hosts

### Prisma 7 — When to Use
**Choose Prisma for**: teams that prefer schema-first workflow, teams needing broad DB support (MySQL, MongoDB, CockroachDB), multi-database scenarios, or teams who value Prisma Studio and migration tooling.

```prisma
// schema.prisma:
model Post {
  id        Int      @id @default(autoincrement())
  title     String
  content   String
  author    User     @relation(fields: [authorId], references: [id])
  authorId  Int
  createdAt DateTime @default(now())
}
```

```ts
// Prisma Client queries:
const posts = await prisma.post.findMany({
  where: { published: true },
  include: { author: { select: { name: true } } },
  orderBy: { createdAt: 'desc' },
  take: 20,
});
```

**Prisma 7 changes**: Pure TypeScript, no Rust binary, significantly faster cold starts, better serverless support. Run `npx prisma@latest` for latest.

### Decision Table
| Factor | Drizzle | Prisma 7 |
|--------|---------|----------|
| Bundle size | ~7.4KB | ~80KB |
| Serverless cold starts | ~45ms | Improved in v7 |
| SQL control | Full (SQL-like API) | Abstracted |
| Migration tooling | Good (kit) | Excellent |
| Ecosystem | Growing | Mature |
| Schema language | TypeScript | Prisma SDL |
| Edge/Workers | Yes (native) | Yes (with Accelerate) |
| Best for | Serverless, SQL experts | Teams wanting abstraction |

---

## PostgreSQL Best Practices

### Connection Pooling — Critical for Serverless
Serverless functions create a new DB connection per invocation. Without pooling, you'll exhaust `max_connections` (default: 100) under load.

**PgBouncer** (self-hosted): transaction-mode pooling, up to 10,000 client connections on a single DB.

**Neon's built-in pooler**: `?pgbouncer=true` connection string option. Handles 10,000 concurrent connections.

**Prisma Accelerate**: cloud-hosted connection pooler from Prisma, adds global edge caching layer.

```ts
// Neon + Drizzle (serverless-safe):
import { neon } from '@neondatabase/serverless';
import { drizzle } from 'drizzle-orm/neon-http';

const sql = neon(process.env.DATABASE_URL!);
const db = drizzle(sql);
// Each call opens an HTTP connection (connection-less), safe for serverless
```

### Row-Level Security (RLS) in PostgreSQL
```sql
-- Enable RLS:
ALTER TABLE posts ENABLE ROW LEVEL SECURITY;

-- Policy: users can only see their own posts:
CREATE POLICY "users see own posts" ON posts
  FOR SELECT USING (auth.uid() = author_id);

-- Policy: users can insert their own posts:
CREATE POLICY "users insert own posts" ON posts
  FOR INSERT WITH CHECK (auth.uid() = author_id);
```
Supabase uses RLS extensively with `auth.uid()` function. For custom backends, use `SET LOCAL app.user_id = ?` before queries.

### Performance Patterns
- Always index foreign keys and frequently-queried columns
- Use `EXPLAIN ANALYZE` before going live on complex queries
- Partial indexes for common filters: `CREATE INDEX ON posts (created_at) WHERE published = true;`
- JSONB for flexible metadata (indexed with `@>` operator and GIN index)
- Use `SELECT only needed columns` — never `SELECT *` in application code

---

## pgvector — Vector Search in PostgreSQL

pgvector enables semantic search and RAG pipelines without a separate vector database. Available by default on Supabase, Neon, AWS RDS.

```sql
-- Enable extension:
CREATE EXTENSION IF NOT EXISTS vector;

-- Add vector column:
ALTER TABLE documents ADD COLUMN embedding vector(1536);

-- IVFFlat index for approximate nearest neighbor:
CREATE INDEX ON documents USING ivfflat (embedding vector_cosine_ops) WITH (lists = 100);
```

```ts
// Drizzle + pgvector:
import { vector } from 'drizzle-orm/pg-core';

export const documents = pgTable('documents', {
  id: serial('id').primaryKey(),
  content: text('content').notNull(),
  embedding: vector('embedding', { dimensions: 1536 }),
});

// Semantic search:
const results = await db
  .select()
  .from(documents)
  .orderBy(sql`embedding <=> ${queryEmbedding}::vector`)
  .limit(10);
```

Use pgvector when: embeddings are ≤ 2048 dimensions, dataset is < 10M vectors, you want to avoid operational complexity. Use Pinecone when: you have tens of millions of vectors, need managed scaling, or require multi-tenant isolation.

---

## Redis — Caching, Queues, Sessions

### Upstash Redis (serverless-native)
REST-based Redis, works on Cloudflare Workers and edge runtimes:
```ts
import { Redis } from '@upstash/redis';

const redis = new Redis({
  url: process.env.UPSTASH_REDIS_REST_URL!,
  token: process.env.UPSTASH_REDIS_REST_TOKEN!,
});

// Cache pattern:
const cacheKey = `posts:${userId}`;
const cached = await redis.get(cacheKey);
if (cached) return cached;
const posts = await db.query.posts.findMany(...);
await redis.setex(cacheKey, 300, posts); // 5-minute TTL
return posts;
```

### BullMQ — Job Queues on Redis
For background jobs, scheduled tasks, heavy PDF/image processing:
```ts
import { Queue, Worker } from 'bullmq';

// Producer:
const emailQueue = new Queue('emails', { connection: redisConnection });
await emailQueue.add('welcome', { to: user.email, name: user.name }, {
  attempts: 3,
  backoff: { type: 'exponential', delay: 2000 },
});

// Worker (separate Node.js process):
const worker = new Worker('emails', async (job) => {
  await sendEmail(job.data);
}, { connection: redisConnection, concurrency: 5 });
```

---

## SQLite at the Edge — Turso / LibSQL

For edge deployments needing a real DB (not just KV):
- **Turso**: distributed SQLite with replication to 35+ regions. <1ms reads in region.
- **Cloudflare D1**: SQLite on Cloudflare Workers. Integrated with Workers bindings.

```ts
// Drizzle + Turso:
import { createClient } from '@libsql/client';
import { drizzle } from 'drizzle-orm/libsql';

const client = createClient({
  url: process.env.TURSO_DATABASE_URL!,
  authToken: process.env.TURSO_AUTH_TOKEN!,
});

export const db = drizzle(client);
```

---

## MongoDB — Document Data

Use MongoDB for: unstructured/variable-schema data, document-centric models (content management, event sourcing), write-heavy workloads with flexible querying. MongoDB Atlas (managed) with Mongoose or Prisma MongoDB adapter. Avoid for: relational data with complex joins, strict ACID requirements, or when the team knows SQL well.

---

## PostgreSQL Hosting Options (2025)

| Platform | Cold Start | Scale-to-zero | Vector | Free Tier |
|----------|-----------|---------------|--------|-----------|
| Neon (Serverless PG) | ~500ms first request | Yes | pgvector | Yes (0.5 GB) |
| Supabase | No (always on) | No (free tier pauses) | pgvector | Yes (500 MB) |
| Railway | N/A | No | pgvector | $5/mo |
| Render | N/A | No | pgvector | 90-day free |
| Prisma Postgres | Yes | Yes | Yes | Yes |

Neon acquired by Databricks in 2025 — strong investment signal. Recommended for serverless apps. Supabase ($200M, $2B valuation in April 2025) recommended when you need Auth + Realtime + Storage alongside the DB.
