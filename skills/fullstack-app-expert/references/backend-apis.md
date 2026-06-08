# Backend Frameworks & APIs (2025-2026)

## Framework Selection by Deployment Target

### Hono — The Edge/Serverless Default
Ultra-lightweight (~14KB), runs on any JS runtime: Cloudflare Workers, Bun, Deno, Node.js, AWS Lambda Edge.

```ts
import { Hono } from 'hono';
import { zValidator } from '@hono/zod-validator';
import { z } from 'zod';

const app = new Hono();

const postSchema = z.object({
  title: z.string().min(1).max(255),
  content: z.string(),
});

app.post('/posts', zValidator('json', postSchema), async (c) => {
  const { title, content } = c.req.valid('json');
  const post = await db.insert(posts).values({ title, content }).returning();
  return c.json(post[0], 201);
});

// Cloudflare Workers deployment:
export default app;
```

Key Hono features:
- `hono/middleware` — built-in auth, CORS, rate limiting, logger
- `@hono/zod-openapi` — generates OpenAPI spec from Zod schemas
- Type-safe RPC client: `hc<AppType>('https://api.example.com')`
- **Caveat**: Hono on Node.js is slower than Fastify (adapter overhead). Use Hono specifically for edge/serverless targets.

### Fastify — Node.js Server Default
Best raw throughput for traditional Node.js servers. 40,000+ req/s on a single process.

```ts
import Fastify from 'fastify';
import { TypeBoxTypeProvider } from '@fastify/type-provider-typebox';
import { Type } from '@sinclair/typebox';

const app = Fastify().withTypeProvider<TypeBoxTypeProvider>();

app.post('/users', {
  schema: {
    body: Type.Object({
      email: Type.String({ format: 'email' }),
      name: Type.String(),
    }),
    response: {
      201: Type.Object({ id: Type.String() }),
    },
  },
}, async (req, reply) => {
  const user = await createUser(req.body);
  return reply.status(201).send({ id: user.id });
});
```

Use Fastify for: long-running Node.js servers, microservices, high-throughput JSON APIs, PostgreSQL-heavy backends.

### Express — Legacy / Mature Ecosystem
Still widely used, massive ecosystem. 2-3x slower than Fastify. Use when inheriting existing codebases or when ecosystem compatibility (middleware libraries) is critical.

### Bun Runtime
Bun is a drop-in Node.js replacement with 2-4x faster startup and HTTP performance. Compatible with most npm packages.
```bash
bun create hono my-api   # Hono on Bun: fastest JS HTTP stack
bun run dev
```
Production-ready as of 2025. Bun.serve() handles HTTP natively. Use with Hono for maximum edge performance.

---

## tRPC v11 — TypeScript Full-Stack Type Safety

tRPC v11 + TanStack React Query integration (released February 2025) is the most significant update. The new client is native to TanStack Query — no more wrapper hooks.

### Setup (Next.js 15 App Router)
```ts
// server/api/root.ts
import { createTRPCRouter, publicProcedure } from './trpc';
import { z } from 'zod';

export const appRouter = createTRPCRouter({
  posts: createTRPCRouter({
    list: publicProcedure
      .input(z.object({ cursor: z.number().optional() }))
      .query(async ({ input, ctx }) => {
        return ctx.db.query.posts.findMany({
          limit: 20,
          offset: input.cursor ?? 0,
        });
      }),
    create: publicProcedure
      .input(z.object({ title: z.string().min(1), content: z.string() }))
      .mutation(async ({ input, ctx }) => {
        return ctx.db.insert(posts).values(input).returning();
      }),
  }),
});

export type AppRouter = typeof appRouter;
```

```ts
// client — TanStack Query native integration (v11):
import { useTRPC } from '@/lib/trpc';
import { useQuery, useMutation } from '@tanstack/react-query';

function Posts() {
  const trpc = useTRPC();
  const { data } = useQuery(trpc.posts.list.queryOptions({ cursor: 0 }));
  const create = useMutation(trpc.posts.create.mutationOptions());
  // Full TanStack Query API — queryKey, staleTime, refetch, etc.
}
```

### tRPC v11 New Features
- **httpBatchStreamLink**: stream responses, helpful for large datasets
- **SSE subscriptions**: real-time updates without WebSockets:
  ```ts
  // Subscription procedure:
  notifications: publicProcedure.subscription(async function* ({ ctx }) {
    const sub = await subscribeToNotifications(ctx.userId);
    for await (const notification of sub) {
      yield notification;
    }
  })
  ```
- Full React Suspense support via `useSuspenseQuery`

---

## GraphQL — When and How

GraphQL makes sense when: multiple clients need different data shapes (mobile vs web), complex nested relationships, established schema-first contract between teams. For simple CRUD or TypeScript-only stacks, tRPC is simpler.

### Type-Safe Stack: Pothos + Apollo Server v4

```ts
// schema.ts — Pothos (code-first, type-safe):
import SchemaBuilder from '@pothos/core';
import PrismaPlugin from '@pothos/plugin-prisma';

const builder = new SchemaBuilder<{ PrismaTypes: PrismaTypes }>({
  plugins: [PrismaPlugin],
  prisma: { client: db },
});

builder.prismaObject('Post', {
  fields: (t) => ({
    id: t.exposeID('id'),
    title: t.exposeString('title'),
    author: t.relation('author'),
  }),
});

builder.queryType({
  fields: (t) => ({
    posts: t.prismaField({
      type: ['Post'],
      resolve: (query) => db.post.findMany({ ...query }),
    }),
  }),
});

export const schema = builder.toSchema();
```

```ts
// server.ts — Apollo Server v4:
import { ApolloServer } from '@apollo/server';
import { startStandaloneServer } from '@apollo/server/standalone';

const server = new ApolloServer({ schema });
const { url } = await startStandaloneServer(server, { listen: { port: 4000 } });
```

### Alternative: GraphQL Yoga + Pothos
Yoga is lighter than Apollo, runs on Cloudflare Workers and edge runtimes, ships with graphiql built-in. Preferred for edge deployments.

---

## REST Best Practices (2025)

- **OpenAPI 3.1** for spec-first or spec-generated APIs
- `@hono/zod-openapi` or `fastify-swagger` for auto-generation
- Resource naming: plural nouns (`/posts`, `/users/{id}/comments`)
- HTTP semantics: GET (idempotent, cacheable), POST (create), PUT (full replace), PATCH (partial), DELETE
- Pagination: cursor-based for real data, offset for admin UIs
- Versioning: URL prefix `/v1/` for major breaking changes; use `Sunset` headers for deprecation
- Return 4xx with machine-readable error bodies: `{ error: { code: "VALIDATION_ERROR", message: "...", fields: [...] } }`

### Webhook Design
```ts
// Validate webhook signature (Stripe/GitHub pattern):
import { createHmac, timingSafeEqual } from 'crypto';

function validateWebhook(payload: Buffer, signature: string, secret: string) {
  const expected = createHmac('sha256', secret)
    .update(payload)
    .digest('hex');
  const sig = Buffer.from(signature);
  const exp = Buffer.from(`sha256=${expected}`);
  return sig.length === exp.length && timingSafeEqual(sig, exp);
}
```
Always: use raw body for signature verification, idempotency keys for retry handling, respond 200 immediately then process async.

---

## Cloudflare Workers — Edge-First Pattern

Full-stack on Cloudflare Workers (2025):
```ts
// Hono app with D1 (SQLite), KV, R2, Durable Objects:
import { Hono } from 'hono';
import { drizzle } from 'drizzle-orm/d1';

type Env = {
  DB: D1Database;
  KV: KVNamespace;
  BUCKET: R2Bucket;
};

const app = new Hono<{ Bindings: Env }>();

app.get('/posts', async (c) => {
  const db = drizzle(c.env.DB);
  const posts = await db.select().from(postsTable).all();
  return c.json(posts);
});

export default app;
```

Workers advantages: zero cold starts (V8 isolates), 200+ locations globally, $0.50/million requests. Worker limitations: no native filesystem, CPU time limits (50ms on free, 30s on paid), no long-running processes.

**Durable Objects** for stateful edge: WebSocket connections, rate limiting, coordination.

---

## Python Backends

### FastAPI (recommended for AI/ML backends)
```python
from fastapi import FastAPI
from pydantic import BaseModel

app = FastAPI()

class Post(BaseModel):
    title: str
    content: str

@app.post("/posts", status_code=201)
async def create_post(post: Post):
    return await db.create_post(post.title, post.content)
```
FastAPI with Uvicorn/Gunicorn: production standard for Python APIs. Automatic OpenAPI docs at `/docs`. Use with SQLAlchemy 2.0 (async) + Alembic for migrations.

### Django (for content-heavy, ORM-dependent apps)
Django REST Framework or Django Ninja (FastAPI-style) for APIs. Strong admin interface out of the box.
