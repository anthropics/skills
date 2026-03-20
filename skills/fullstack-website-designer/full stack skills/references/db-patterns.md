# Database Patterns

## Schema Templates

### Standard fields for every table
```sql
id         UUID PRIMARY KEY DEFAULT gen_random_uuid()
created_at TIMESTAMPTZ NOT NULL DEFAULT now()
updated_at TIMESTAMPTZ NOT NULL DEFAULT now()
```

For soft-delete tables, add:
```sql
deleted_at TIMESTAMPTZ
```

### Users table
```sql
CREATE TABLE users (
  id            UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  email         TEXT NOT NULL UNIQUE,
  display_name  TEXT,
  avatar_url    TEXT,
  password_hash TEXT NOT NULL,
  email_verified BOOLEAN NOT NULL DEFAULT false,
  role          TEXT NOT NULL DEFAULT 'user' CHECK (role IN ('user', 'admin')),
  created_at    TIMESTAMPTZ NOT NULL DEFAULT now(),
  updated_at    TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE INDEX idx_users_email ON users(email);
```

### Generic content table
```sql
CREATE TABLE posts (
  id          UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id     UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
  title       TEXT NOT NULL,
  slug        TEXT NOT NULL UNIQUE,
  body        TEXT NOT NULL,
  status      TEXT NOT NULL DEFAULT 'draft' CHECK (status IN ('draft', 'published', 'archived')),
  published_at TIMESTAMPTZ,
  created_at  TIMESTAMPTZ NOT NULL DEFAULT now(),
  updated_at  TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE INDEX idx_posts_user_id ON posts(user_id);
CREATE INDEX idx_posts_status ON posts(status) WHERE status = 'published';
CREATE INDEX idx_posts_created_at ON posts(created_at DESC);
```

### Refresh tokens table (for JWT auth)
```sql
CREATE TABLE refresh_tokens (
  id         UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id    UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
  token_hash TEXT NOT NULL UNIQUE,
  expires_at TIMESTAMPTZ NOT NULL,
  created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE INDEX idx_refresh_tokens_user_id ON refresh_tokens(user_id);
-- Clean up expired tokens periodically
CREATE INDEX idx_refresh_tokens_expires_at ON refresh_tokens(expires_at);
```

### Many-to-many (tags example)
```sql
CREATE TABLE tags (
  id   UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  slug TEXT NOT NULL UNIQUE
);

CREATE TABLE post_tags (
  post_id UUID REFERENCES posts(id) ON DELETE CASCADE,
  tag_id  UUID REFERENCES tags(id) ON DELETE CASCADE,
  PRIMARY KEY (post_id, tag_id)
);
```

---

## Prisma Schema Template

```prisma
generator client {
  provider = "prisma-client-js"
}

datasource db {
  provider = "postgresql"
  url      = env("DATABASE_URL")
}

model User {
  id            String    @id @default(cuid())
  email         String    @unique
  displayName   String?
  avatarUrl     String?
  passwordHash  String
  emailVerified Boolean   @default(false)
  role          Role      @default(USER)
  createdAt     DateTime  @default(now())
  updatedAt     DateTime  @updatedAt
  posts         Post[]
  refreshTokens RefreshToken[]
}

enum Role {
  USER
  ADMIN
}

model Post {
  id          String    @id @default(cuid())
  title       String
  slug        String    @unique
  body        String
  status      PostStatus @default(DRAFT)
  publishedAt DateTime?
  createdAt   DateTime  @default(now())
  updatedAt   DateTime  @updatedAt
  user        User      @relation(fields: [userId], references: [id], onDelete: Cascade)
  userId      String
  tags        Tag[]

  @@index([userId])
  @@index([status])
  @@index([createdAt(sort: Desc)])
}

enum PostStatus {
  DRAFT
  PUBLISHED
  ARCHIVED
}

model RefreshToken {
  id        String   @id @default(cuid())
  tokenHash String   @unique
  expiresAt DateTime
  createdAt DateTime @default(now())
  user      User     @relation(fields: [userId], references: [id], onDelete: Cascade)
  userId    String

  @@index([userId])
  @@index([expiresAt])
}

model Tag {
  id    String @id @default(cuid())
  name  String @unique
  slug  String @unique
  posts Post[]
}
```

---

## Migration Patterns (Prisma)

```bash
# Dev: create migration
npx prisma migrate dev --name add_posts_table

# Prod: apply migrations
npx prisma migrate deploy

# Reset dev DB
npx prisma migrate reset

# Generate client after schema change
npx prisma generate
```

---

## Seed Data

```typescript
// prisma/seed.ts
import { PrismaClient } from '@prisma/client'
import bcrypt from 'bcryptjs'

const db = new PrismaClient()

async function main() {
  const password = await bcrypt.hash('password123', 12)

  const admin = await db.user.upsert({
    where: { email: 'admin@example.com' },
    update: {},
    create: {
      email: 'admin@example.com',
      displayName: 'Admin User',
      passwordHash: password,
      role: 'ADMIN',
      emailVerified: true,
    },
  })

  await db.post.createMany({
    data: [
      { title: 'Hello World', slug: 'hello-world', body: 'First post!', status: 'PUBLISHED', userId: admin.id, publishedAt: new Date() },
      { title: 'Draft Post', slug: 'draft-post', body: 'Work in progress.', status: 'DRAFT', userId: admin.id },
    ],
    skipDuplicates: true,
  })

  console.log('Seed complete')
}

main().catch(console.error).finally(() => db.$disconnect())
```

```json
// package.json — add:
"prisma": {
  "seed": "ts-node --compiler-options {\"module\":\"CommonJS\"} prisma/seed.ts"
}
```

```bash
npx prisma db seed
```

---

## Indexing Strategy

- **Always index**: foreign keys, frequently filtered columns, sort columns
- **Partial indexes**: for status/boolean filters (`WHERE status = 'active'`)
- **Composite indexes**: for queries that filter on multiple columns together
- **Text search**: use `pg_trgm` for fuzzy search, or dedicated full-text search

```sql
-- Full-text search index
ALTER TABLE posts ADD COLUMN search_vector tsvector
  GENERATED ALWAYS AS (to_tsvector('english', title || ' ' || body)) STORED;
CREATE INDEX idx_posts_search ON posts USING GIN(search_vector);

-- Query:
SELECT * FROM posts WHERE search_vector @@ plainto_tsquery('english', 'search term');
```

---

## Connection Pooling

For production, use PgBouncer or Prisma Accelerate. Don't open a new DB connection per request.

```typescript
// lib/db.ts — singleton pattern
import { PrismaClient } from '@prisma/client'

const globalForPrisma = globalThis as unknown as { prisma: PrismaClient }

export const db = globalForPrisma.prisma ?? new PrismaClient({
  log: process.env.NODE_ENV === 'development' ? ['query', 'error'] : ['error'],
})

if (process.env.NODE_ENV !== 'production') globalForPrisma.prisma = db
```
