# Fullstack Tech Stack Guide

Technology selection guide with trade-offs, use cases, and integration patterns for modern fullstack development.

---

## Table of Contents

- [Frontend Frameworks](#frontend-frameworks)
- [Backend Frameworks](#backend-frameworks)
- [Databases](#databases)
- [ORMs and Query Builders](#orms-and-query-builders)
- [Authentication Solutions](#authentication-solutions)
- [Deployment Platforms](#deployment-platforms)
- [Stack Recommendations](#stack-recommendations)

---

## Frontend Frameworks

### Next.js

**Best for:** Production React apps, SEO-critical sites, full-stack applications

| Pros | Cons |
|------|------|
| Server components, streaming | Learning curve for advanced features |
| Built-in routing, API routes | Vercel lock-in concerns |
| Excellent DX and performance | Bundle size can grow |
| Strong TypeScript support | Complex mental model (client/server) |

**When to choose:**
- Need SSR/SSG for SEO
- Building a product that may scale
- Want full-stack in one framework
- Team familiar with React

```typescript
// App Router pattern
// app/users/page.tsx
async function UsersPage() {
  const users = await db.user.findMany(); // Server component
  return <UserList users={users} />;
}

// app/users/[id]/page.tsx
export async function generateStaticParams() {
  const users = await db.user.findMany();
  return users.map((user) => ({ id: user.id }));
}
```

### React + Vite

**Best for:** SPAs, dashboards, internal tools

| Pros | Cons |
|------|------|
| Fast development with HMR | No SSR out of the box |
| Simple mental model | Manual routing setup |
| Flexible architecture | No built-in API routes |
| Smaller bundle potential | Need separate backend |

**When to choose:**
- Building internal dashboards
- SEO not important
- Need maximum flexibility
- Prefer decoupled frontend/backend

### Vue 3

**Best for:** Teams transitioning from jQuery, progressive enhancement

| Pros | Cons |
|------|------|
| Gentle learning curve | Smaller ecosystem than React |
| Excellent documentation | Fewer enterprise adoptions |
| Single-file components | Composition API learning curve |
| Good TypeScript support | Two paradigms (Options/Composition) |

**When to choose:**
- Team new to modern frameworks
- Progressive enhancement needed
- Prefer official solutions (Pinia, Vue Router)

### Comparison Matrix

| Feature | Next.js | React+Vite | Vue 3 | Svelte |
|---------|---------|------------|-------|--------|
| SSR | Built-in | Manual | Nuxt | SvelteKit |
| Bundle size | Medium | Small | Small | Smallest |
| Learning curve | Medium | Low | Low | Low |
| Enterprise adoption | High | High | Medium | Low |
| Job market | Large | Large | Medium | Small |

---

## Backend Frameworks

### Node.js Ecosystem

**Express.js**

```typescript
import express from "express";
import { userRouter } from "./routes/users";

const app = express();
app.use(express.json());
app.use("/api/users", userRouter);
app.listen(3000);
```

| Pros | Cons |
|------|------|
| Minimal, flexible | No structure opinions |
| Huge middleware ecosystem | Callback-based (legacy) |
| Well understood | Manual TypeScript setup |

**Fastify**

```typescript
import Fastify from "fastify";

const app = Fastify({ logger: true });

app.get("/users/:id", {
  schema: {
    params: { type: "object", properties: { id: { type: "string" } } },
    response: { 200: UserSchema },
  },
  handler: async (request) => {
    return db.user.findUnique({ where: { id: request.params.id } });
  },
});
```

| Pros | Cons |
|------|------|
| High performance | Smaller ecosystem |
| Built-in validation | Different plugin model |
| TypeScript-first | Less community content |

**NestJS**

```typescript
@Controller("users")
export class UsersController {
  constructor(private usersService: UsersService) {}

  @Get(":id")
  findOne(@Param("id") id: string) {
    return this.usersService.findOne(id);
  }

  @Post()
  @UseGuards(AuthGuard)
  create(@Body() createUserDto: CreateUserDto) {
    return this.usersService.create(createUserDto);
  }
}
```

| Pros | Cons |
|------|------|
| Strong architecture | Steep learning curve |
| Full-featured (GraphQL, WebSockets) | Heavy for small projects |
| Enterprise-ready | Decorator complexity |

### Python Ecosystem

**FastAPI**

```python
from fastapi import FastAPI, Depends
from sqlalchemy.orm import Session

app = FastAPI()

@app.get("/users/{user_id}", response_model=UserResponse)
async def get_user(user_id: int, db: Session = Depends(get_db)):
    user = db.query(User).filter(User.id == user_id).first()
    if not user:
        raise HTTPException(status_code=404)
    return user
```

| Pros | Cons |
|------|------|
| Auto-generated docs | Python GIL limitations |
| Type hints → validation | Async ecosystem maturing |
| High performance | Smaller than Django ecosystem |

**Django**

| Pros | Cons |
|------|------|
| Batteries included | Monolithic |
| Admin panel | ORM limitations |
| Mature ecosystem | Async support newer |

### Framework Selection Guide

| Use Case | Recommendation |
|----------|---------------|
| API-first startup | FastAPI or Fastify |
| Enterprise backend | NestJS or Django |
| Microservices | Fastify or Go |
| Rapid prototype | Express or Django |
| Full-stack TypeScript | Next.js API routes |

---

## Databases

### PostgreSQL

**Best for:** Most applications, relational data, ACID compliance

```sql
-- JSON support
CREATE TABLE users (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  email VARCHAR(255) UNIQUE NOT NULL,
  profile JSONB DEFAULT '{}',
  created_at TIMESTAMPTZ DEFAULT NOW()
);

-- Full-text search
CREATE INDEX users_search_idx ON users
  USING GIN (to_tsvector('english', email || ' ' || profile->>'name'));

SELECT * FROM users
WHERE to_tsvector('english', email || ' ' || profile->>'name')
  @@ to_tsquery('john');
```

| Feature | Rating |
|---------|--------|
| ACID compliance | Excellent |
| JSON support | Excellent |
| Full-text search | Good |
| Horizontal scaling | Requires setup |
| Managed options | Many (RDS, Supabase, Neon) |

### MongoDB

**Best for:** Document-heavy apps, flexible schemas, rapid prototyping

```typescript
// Flexible schema
const userSchema = new Schema({
  email: { type: String, required: true, unique: true },
  profile: {
    name: String,
    preferences: Schema.Types.Mixed, // Any structure
  },
  orders: [{ type: Schema.Types.ObjectId, ref: "Order" }],
});
```

| Feature | Rating |
|---------|--------|
| Schema flexibility | Excellent |
| Horizontal scaling | Excellent |
| Transactions | Good (4.0+) |
| Joins | Limited |
| Managed options | Atlas |

### Redis

**Best for:** Caching, sessions, real-time features, queues

```typescript
// Session storage
await redis.set(`session:${sessionId}`, JSON.stringify(user), "EX", 3600);

// Rate limiting
const requests = await redis.incr(`rate:${ip}`);
if (requests === 1) await redis.expire(`rate:${ip}`, 60);
if (requests > 100) throw new TooManyRequestsError();

// Pub/Sub
redis.publish("notifications", JSON.stringify({ userId, message }));
```

### Database Selection Matrix

| Requirement | PostgreSQL | MongoDB | MySQL |
|-------------|-----------|---------|-------|
| Complex queries | Best | Limited | Good |
| Schema flexibility | Good (JSONB) | Best | Limited |
| Transactions | Best | Good | Good |
| Horizontal scale | Manual | Built-in | Manual |
| Cloud managed | Many | Atlas | Many |

---

## ORMs and Query Builders

### Prisma

**Best for:** TypeScript projects, schema-first development

```typescript
// schema.prisma
model User {
  id        String   @id @default(cuid())
  email     String   @unique
  posts     Post[]
  profile   Profile?
  createdAt DateTime @default(now())
}

// Usage - fully typed
const user = await prisma.user.findUnique({
  where: { email: "user@example.com" },
  include: { posts: true, profile: true },
});
// user.posts is Post[] - TypeScript knows
```

| Pros | Cons |
|------|------|
| Excellent TypeScript | Generated client size |
| Schema migrations | Limited raw SQL support |
| Visual studio | Some edge case limitations |

### Drizzle

**Best for:** SQL-first TypeScript, performance-critical apps

```typescript
// Schema definition
const users = pgTable("users", {
  id: uuid("id").primaryKey().defaultRandom(),
  email: varchar("email", { length: 255 }).notNull().unique(),
  createdAt: timestamp("created_at").defaultNow(),
});

// Query - SQL-like syntax
const result = await db
  .select()
  .from(users)
  .where(eq(users.email, "user@example.com"))
  .leftJoin(posts, eq(posts.userId, users.id));
```

| Pros | Cons |
|------|------|
| Lightweight | Newer, smaller community |
| SQL-like syntax | Fewer integrations |
| Fast runtime | Manual migrations |

### SQLAlchemy (Python)

```python
# Model definition
class User(Base):
    __tablename__ = "users"

    id = Column(UUID, primary_key=True, default=uuid4)
    email = Column(String(255), unique=True, nullable=False)
    posts = relationship("Post", back_populates="author")

# Query
users = session.query(User)\
    .filter(User.email.like("%@example.com"))\
    .options(joinedload(User.posts))\
    .all()
```

---

## Authentication Solutions

### Auth.js (NextAuth)

**Best for:** Next.js apps, social logins

```typescript
// app/api/auth/[...nextauth]/route.ts
import NextAuth from "next-auth";
import GitHub from "next-auth/providers/github";
import Credentials from "next-auth/providers/credentials";

export const { handlers, auth, signIn, signOut } = NextAuth({
  providers: [
    GitHub,
    Credentials({
      credentials: { email: {}, password: {} },
      authorize: async (credentials) => {
        const user = await verifyCredentials(credentials);
        return user;
      },
    }),
  ],
  callbacks: {
    jwt({ token, user }) {
      if (user) token.role = user.role;
      return token;
    },
  },
});
```

| Pros | Cons |
|------|------|
| Many providers | Next.js focused |
| Session management | Complex customization |
| Database adapters | Breaking changes between versions |

### Clerk

**Best for:** Rapid development, hosted solution

```typescript
// Middleware
import { clerkMiddleware } from "@clerk/nextjs/server";

export default clerkMiddleware();

// Usage
import { auth } from "@clerk/nextjs/server";

export async function GET() {
  const { userId } = await auth();
  if (!userId) return new Response("Unauthorized", { status: 401 });
  // ...
}
```

| Pros | Cons |
|------|------|
| Beautiful UI components | Vendor lock-in |
| Managed infrastructure | Cost at scale |
| Multi-factor auth | Data residency concerns |

### Custom JWT

**Best for:** Full control, microservices

```typescript
// Token generation
function generateTokens(user: User) {
  const accessToken = jwt.sign(
    { sub: user.id, role: user.role },
    process.env.JWT_SECRET,
    { expiresIn: "15m" }
  );

  const refreshToken = jwt.sign(
    { sub: user.id, version: user.tokenVersion },
    process.env.REFRESH_SECRET,
    { expiresIn: "7d" }
  );

  return { accessToken, refreshToken };
}

// Middleware
function authenticate(req, res, next) {
  const token = req.headers.authorization?.replace("Bearer ", "");
  if (!token) return res.status(401).json({ error: "No token" });

  try {
    req.user = jwt.verify(token, process.env.JWT_SECRET);
    next();
  } catch {
    res.status(401).json({ error: "Invalid token" });
  }
}
```

---

## Deployment Platforms

### Vercel

**Best for:** Next.js, frontend-focused teams

| Pros | Cons |
|------|------|
| Zero-config Next.js | Expensive at scale |
| Edge functions | Vendor lock-in |
| Preview deployments | Limited backend options |
| Global CDN | Cold starts |

### Railway

**Best for:** Full-stack apps, databases included

| Pros | Cons |
|------|------|
| Simple deployment | Smaller community |
| Built-in databases | Limited regions |
| Good pricing | Fewer integrations |

### AWS (ECS/Lambda)

**Best for:** Enterprise, complex requirements

| Pros | Cons |
|------|------|
| Full control | Complex setup |
| Cost-effective at scale | Steep learning curve |
| Any technology | Requires DevOps knowledge |

### Deployment Selection

| Requirement | Platform |
|-------------|----------|
| Next.js simplicity | Vercel |
| Full-stack + DB | Railway, Render |
| Enterprise scale | AWS, GCP |
| Container control | Fly.io, Railway |
| Budget startup | Railway, Render |

---

## Stack Recommendations

### Startup MVP

```
Frontend: Next.js 14 (App Router)
Backend:  Next.js API Routes
Database: PostgreSQL (Neon/Supabase)
Auth:     Auth.js or Clerk
Deploy:   Vercel
Cache:    Vercel KV or Upstash Redis
```

**Why:** Fastest time to market, single deployment, good scaling path.

### SaaS Product

```
Frontend: Next.js 14
Backend:  Separate API (FastAPI or NestJS)
Database: PostgreSQL (RDS)
Auth:     Custom JWT + Auth.js
Deploy:   Vercel (frontend) + AWS ECS (backend)
Cache:    Redis (ElastiCache)
Queue:    SQS or BullMQ
```

**Why:** Separation allows independent scaling, team specialization.

### Enterprise Application

```
Frontend: Next.js or React + Vite
Backend:  NestJS or Go
Database: PostgreSQL (Aurora)
Auth:     Keycloak or Auth0
Deploy:   Kubernetes (EKS/GKE)
Cache:    Redis Cluster
Queue:    Kafka or RabbitMQ
Observability: Datadog or Grafana Stack
```

**Why:** Maximum control, compliance requirements, team expertise.

### Internal Tool

```
Frontend: React + Vite + Tailwind
Backend:  Express or FastAPI
Database: PostgreSQL or SQLite
Auth:     OIDC with corporate IdP
Deploy:   Docker on internal infrastructure
```

**Why:** Simple, low maintenance, integrates with existing systems.

---

## Quick Decision Guide

| Question | If Yes → | If No → |
|----------|----------|---------|
| Need SEO? | Next.js SSR | React SPA |
| Complex backend? | Separate API | Next.js routes |
| Team knows Python? | FastAPI | Node.js |
| Need real-time? | Add WebSockets | REST is fine |
| Enterprise compliance? | Self-hosted | Managed services |
| Budget constrained? | Railway/Render | Vercel/AWS |
| Schema changes often? | MongoDB | PostgreSQL |
