# Fullstack Architecture Patterns

Proven architectural patterns for scalable fullstack applications covering frontend, backend, and their integration.

---

## Table of Contents

- [Frontend Architecture](#frontend-architecture)
- [Backend Architecture](#backend-architecture)
- [API Design Patterns](#api-design-patterns)
- [Database Patterns](#database-patterns)
- [Caching Strategies](#caching-strategies)
- [Authentication Architecture](#authentication-architecture)

---

## Frontend Architecture

### Component Architecture

**Atomic Design Pattern**

Organize components in hierarchical levels:

```
src/components/
├── atoms/           # Button, Input, Icon
├── molecules/       # SearchInput, FormField
├── organisms/       # Header, Footer, Sidebar
├── templates/       # PageLayout, DashboardLayout
└── pages/           # Home, Profile, Settings
```

**When to use:** Large applications with design systems and multiple teams.

**Container/Presentational Pattern**

```typescript
// Presentational - pure rendering, no state
function UserCard({ name, email, avatar }: UserCardProps) {
  return (
    <div className="card">
      <img src={avatar} alt={name} />
      <h3>{name}</h3>
      <p>{email}</p>
    </div>
  );
}

// Container - handles data fetching and state
function UserCardContainer({ userId }: { userId: string }) {
  const { data, loading } = useUser(userId);
  if (loading) return <Skeleton />;
  return <UserCard {...data} />;
}
```

**When to use:** When you need clear separation between UI and logic.

### State Management Patterns

**Server State vs Client State**

| Type | Examples | Tools |
|------|----------|-------|
| Server State | User data, API responses | React Query, SWR |
| Client State | UI toggles, form inputs | Zustand, Jotai |
| URL State | Filters, pagination | Next.js router |

**React Query for Server State:**

```typescript
function useUsers(filters: Filters) {
  return useQuery({
    queryKey: ["users", filters],
    queryFn: () => api.getUsers(filters),
    staleTime: 5 * 60 * 1000, // 5 minutes
    gcTime: 30 * 60 * 1000,   // 30 minutes
  });
}

// Mutations with optimistic updates
function useUpdateUser() {
  const queryClient = useQueryClient();

  return useMutation({
    mutationFn: api.updateUser,
    onMutate: async (newUser) => {
      await queryClient.cancelQueries({ queryKey: ["users"] });
      const previous = queryClient.getQueryData(["users"]);
      queryClient.setQueryData(["users"], (old) =>
        old.map(u => u.id === newUser.id ? newUser : u)
      );
      return { previous };
    },
    onError: (err, newUser, context) => {
      queryClient.setQueryData(["users"], context.previous);
    },
    onSettled: () => {
      queryClient.invalidateQueries({ queryKey: ["users"] });
    },
  });
}
```

---

## Backend Architecture

### Clean Architecture

```
src/
├── domain/              # Business entities, no dependencies
│   ├── entities/        # User, Order, Product
│   └── interfaces/      # Repository interfaces
├── application/         # Use cases, application logic
│   ├── use-cases/       # CreateOrder, UpdateUser
│   └── services/        # OrderService, AuthService
├── infrastructure/      # External concerns
│   ├── database/        # Repository implementations
│   ├── http/            # Controllers, middleware
│   └── external/        # Third-party integrations
└── shared/              # Cross-cutting concerns
    ├── errors/
    └── utils/
```

**Dependency Flow:** domain ← application ← infrastructure

**Repository Pattern:**

```typescript
// Domain interface
interface UserRepository {
  findById(id: string): Promise<User | null>;
  findByEmail(email: string): Promise<User | null>;
  save(user: User): Promise<User>;
  delete(id: string): Promise<void>;
}

// Infrastructure implementation
class PostgresUserRepository implements UserRepository {
  constructor(private db: Database) {}

  async findById(id: string): Promise<User | null> {
    const row = await this.db.query(
      "SELECT * FROM users WHERE id = $1",
      [id]
    );
    return row ? this.toEntity(row) : null;
  }

  private toEntity(row: UserRow): User {
    return new User({
      id: row.id,
      email: row.email,
      name: row.name,
      createdAt: row.created_at,
    });
  }
}
```

### Middleware Pipeline

```typescript
// Express middleware chain
app.use(cors());
app.use(helmet());
app.use(requestId());
app.use(logger());
app.use(authenticate());
app.use(rateLimit());
app.use("/api", routes);
app.use(errorHandler());

// Custom middleware example
function requestId() {
  return (req: Request, res: Response, next: NextFunction) => {
    req.id = req.headers["x-request-id"] || crypto.randomUUID();
    res.setHeader("x-request-id", req.id);
    next();
  };
}

function errorHandler() {
  return (err: Error, req: Request, res: Response, next: NextFunction) => {
    const status = err instanceof AppError ? err.status : 500;
    const message = status === 500 ? "Internal Server Error" : err.message;

    logger.error({ err, requestId: req.id });
    res.status(status).json({ error: message, requestId: req.id });
  };
}
```

---

## API Design Patterns

### REST Best Practices

**Resource Naming:**
- Use nouns, not verbs: `/users` not `/getUsers`
- Use plural: `/users` not `/user`
- Nest for relationships: `/users/{id}/orders`

**HTTP Methods:**

| Method | Purpose | Idempotent |
|--------|---------|------------|
| GET | Retrieve | Yes |
| POST | Create | No |
| PUT | Replace | Yes |
| PATCH | Partial update | No |
| DELETE | Remove | Yes |

**Response Envelope:**

```typescript
// Success response
{
  "data": { /* resource */ },
  "meta": {
    "requestId": "abc-123",
    "timestamp": "2024-01-15T10:30:00Z"
  }
}

// Paginated response
{
  "data": [/* items */],
  "pagination": {
    "page": 1,
    "pageSize": 20,
    "total": 150,
    "totalPages": 8
  }
}

// Error response
{
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "Invalid input",
    "details": [
      { "field": "email", "message": "Invalid email format" }
    ]
  },
  "meta": { "requestId": "abc-123" }
}
```

### GraphQL Architecture

**Schema-First Design:**

```graphql
type Query {
  user(id: ID!): User
  users(filter: UserFilter, page: PageInput): UserConnection!
}

type Mutation {
  createUser(input: CreateUserInput!): UserPayload!
  updateUser(id: ID!, input: UpdateUserInput!): UserPayload!
}

type User {
  id: ID!
  email: String!
  profile: Profile
  orders(first: Int, after: String): OrderConnection!
}

type UserPayload {
  user: User
  errors: [Error!]
}
```

**Resolver Pattern:**

```typescript
const resolvers = {
  Query: {
    user: async (_, { id }, { dataSources }) => {
      return dataSources.userAPI.findById(id);
    },
  },
  User: {
    // Field resolver for related data
    orders: async (user, { first, after }, { dataSources }) => {
      return dataSources.orderAPI.findByUserId(user.id, { first, after });
    },
  },
};
```

**DataLoader for N+1 Prevention:**

```typescript
const userLoader = new DataLoader(async (userIds: string[]) => {
  const users = await db.query(
    "SELECT * FROM users WHERE id = ANY($1)",
    [userIds]
  );
  // Return in same order as input
  return userIds.map(id => users.find(u => u.id === id));
});
```

---

## Database Patterns

### Connection Pooling

```typescript
// PostgreSQL with connection pool
const pool = new Pool({
  host: process.env.DB_HOST,
  database: process.env.DB_NAME,
  user: process.env.DB_USER,
  password: process.env.DB_PASSWORD,
  max: 20,                    // Maximum connections
  idleTimeoutMillis: 30000,   // Close idle connections
  connectionTimeoutMillis: 2000,
});

// Prisma with connection pool
const prisma = new PrismaClient({
  datasources: {
    db: {
      url: `${process.env.DATABASE_URL}?connection_limit=20&pool_timeout=10`,
    },
  },
});
```

### Transaction Patterns

```typescript
// Unit of Work pattern
async function transferFunds(from: string, to: string, amount: number) {
  return await prisma.$transaction(async (tx) => {
    const sender = await tx.account.update({
      where: { id: from },
      data: { balance: { decrement: amount } },
    });

    if (sender.balance < 0) {
      throw new InsufficientFundsError();
    }

    await tx.account.update({
      where: { id: to },
      data: { balance: { increment: amount } },
    });

    return tx.transaction.create({
      data: { fromId: from, toId: to, amount },
    });
  });
}
```

### Read Replicas

```typescript
// Route reads to replica
const readDB = new PrismaClient({
  datasources: { db: { url: process.env.READ_DATABASE_URL } },
});

const writeDB = new PrismaClient({
  datasources: { db: { url: process.env.WRITE_DATABASE_URL } },
});

class UserRepository {
  async findById(id: string) {
    return readDB.user.findUnique({ where: { id } });
  }

  async create(data: CreateUserData) {
    return writeDB.user.create({ data });
  }
}
```

---

## Caching Strategies

### Cache Layers

```
Request → CDN Cache → Application Cache → Database Cache → Database
```

**Cache-Aside Pattern:**

```typescript
async function getUser(id: string): Promise<User> {
  const cacheKey = `user:${id}`;

  // 1. Try cache
  const cached = await redis.get(cacheKey);
  if (cached) {
    return JSON.parse(cached);
  }

  // 2. Fetch from database
  const user = await db.user.findUnique({ where: { id } });
  if (!user) throw new NotFoundError();

  // 3. Store in cache
  await redis.set(cacheKey, JSON.stringify(user), "EX", 3600);

  return user;
}

// Invalidate on update
async function updateUser(id: string, data: UpdateData): Promise<User> {
  const user = await db.user.update({ where: { id }, data });
  await redis.del(`user:${id}`);
  return user;
}
```

**HTTP Cache Headers:**

```typescript
// Immutable assets (hashed filenames)
res.setHeader("Cache-Control", "public, max-age=31536000, immutable");

// API responses
res.setHeader("Cache-Control", "private, max-age=0, must-revalidate");
res.setHeader("ETag", generateETag(data));

// Static pages
res.setHeader("Cache-Control", "public, max-age=3600, stale-while-revalidate=86400");
```

---

## Authentication Architecture

### JWT + Refresh Token Flow

```
1. User logs in → Server returns access token (15min) + refresh token (7d)
2. Client stores tokens (httpOnly cookie for refresh, memory for access)
3. Access token expires → Client uses refresh token to get new pair
4. Refresh token expires → User must log in again
```

**Implementation:**

```typescript
// Token generation
function generateTokens(user: User) {
  const accessToken = jwt.sign(
    { sub: user.id, email: user.email },
    process.env.JWT_SECRET,
    { expiresIn: "15m" }
  );

  const refreshToken = jwt.sign(
    { sub: user.id, tokenVersion: user.tokenVersion },
    process.env.REFRESH_SECRET,
    { expiresIn: "7d" }
  );

  return { accessToken, refreshToken };
}

// Refresh endpoint
app.post("/auth/refresh", async (req, res) => {
  const refreshToken = req.cookies.refreshToken;

  try {
    const payload = jwt.verify(refreshToken, process.env.REFRESH_SECRET);
    const user = await db.user.findUnique({ where: { id: payload.sub } });

    // Check token version (invalidation mechanism)
    if (user.tokenVersion !== payload.tokenVersion) {
      throw new Error("Token revoked");
    }

    const tokens = generateTokens(user);
    setRefreshCookie(res, tokens.refreshToken);
    res.json({ accessToken: tokens.accessToken });
  } catch {
    res.status(401).json({ error: "Invalid refresh token" });
  }
});
```

### Session-Based Auth

```typescript
// Redis session store
app.use(session({
  store: new RedisStore({ client: redisClient }),
  secret: process.env.SESSION_SECRET,
  resave: false,
  saveUninitialized: false,
  cookie: {
    secure: process.env.NODE_ENV === "production",
    httpOnly: true,
    sameSite: "lax",
    maxAge: 7 * 24 * 60 * 60 * 1000, // 7 days
  },
}));

// Login
app.post("/auth/login", async (req, res) => {
  const user = await authenticate(req.body.email, req.body.password);
  req.session.userId = user.id;
  res.json({ user });
});

// Middleware
function requireAuth(req, res, next) {
  if (!req.session.userId) {
    return res.status(401).json({ error: "Authentication required" });
  }
  next();
}
```

---

## Decision Matrix

| Pattern | Complexity | Scalability | When to Use |
|---------|-----------|-------------|-------------|
| Monolith | Low | Medium | MVPs, small teams |
| Modular Monolith | Medium | High | Growing teams |
| Microservices | High | Very High | Large orgs, diverse tech |
| REST | Low | High | CRUD APIs, public APIs |
| GraphQL | Medium | High | Complex data needs, mobile apps |
| JWT Auth | Low | High | Stateless APIs, microservices |
| Session Auth | Low | Medium | Traditional web apps |
