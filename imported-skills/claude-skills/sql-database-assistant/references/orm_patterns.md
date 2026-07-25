# ORM Patterns Reference

Side-by-side comparison of Prisma, Drizzle, TypeORM, and SQLAlchemy patterns for common database operations.

---

## Schema Definition

### Prisma (schema.prisma)
```prisma
model User {
  id        Int      @id @default(autoincrement())
  email     String   @unique
  name      String?
  role      Role     @default(USER)
  posts     Post[]
  profile   Profile?
  createdAt DateTime @default(now())
  updatedAt DateTime @updatedAt

  @@index([email])
  @@map("users")
}

model Post {
  id        Int      @id @default(autoincrement())
  title     String
  body      String?
  published Boolean  @default(false)
  author    User     @relation(fields: [authorId], references: [id], onDelete: Cascade)
  authorId  Int
  tags      Tag[]
  createdAt DateTime @default(now())

  @@index([authorId])
  @@index([published, createdAt])
  @@map("posts")
}

enum Role {
  USER
  ADMIN
  MODERATOR
}
```

### Drizzle (schema.ts)
```typescript
import { pgTable, serial, varchar, text, boolean, timestamp, integer, pgEnum } from 'drizzle-orm/pg-core';

export const roleEnum = pgEnum('role', ['USER', 'ADMIN', 'MODERATOR']);

export const users = pgTable('users', {
  id: serial('id').primaryKey(),
  email: varchar('email', { length: 255 }).notNull().unique(),
  name: varchar('name', { length: 255 }),
  role: roleEnum('role').default('USER').notNull(),
  createdAt: timestamp('created_at').defaultNow().notNull(),
  updatedAt: timestamp('updated_at').defaultNow().notNull(),
});

export const posts = pgTable('posts', {
  id: serial('id').primaryKey(),
  title: varchar('title', { length: 255 }).notNull(),
  body: text('body'),
  published: boolean('published').default(false).notNull(),
  authorId: integer('author_id').notNull().references(() => users.id, { onDelete: 'cascade' }),
  createdAt: timestamp('created_at').defaultNow().notNull(),
}, (table) => ({
  authorIdx: index('idx_posts_author').on(table.authorId),
  publishedIdx: index('idx_posts_published').on(table.published, table.createdAt),
}));
```

### TypeORM (entities)
```typescript
import { Entity, PrimaryGeneratedColumn, Column, ManyToOne, OneToMany, CreateDateColumn, UpdateDateColumn, Index } from 'typeorm';

export enum Role { USER = 'USER', ADMIN = 'ADMIN', MODERATOR = 'MODERATOR' }

@Entity('users')
export class User {
  @PrimaryGeneratedColumn()
  id: number;

  @Column({ unique: true })
  @Index()
  email: string;

  @Column({ nullable: true })
  name: string;

  @Column({ type: 'enum', enum: Role, default: Role.USER })
  role: Role;

  @OneToMany(() => Post, post => post.author)
  posts: Post[];

  @CreateDateColumn()
  createdAt: Date;

  @UpdateDateColumn()
  updatedAt: Date;
}

@Entity('posts')
@Index(['published', 'createdAt'])
export class Post {
  @PrimaryGeneratedColumn()
  id: number;

  @Column()
  title: string;

  @Column({ nullable: true, type: 'text' })
  body: string;

  @Column({ default: false })
  published: boolean;

  @ManyToOne(() => User, user => user.posts, { onDelete: 'CASCADE' })
  author: User;

  @Column()
  authorId: number;

  @CreateDateColumn()
  createdAt: Date;
}
```

### SQLAlchemy (models.py)
```python
import enum
from datetime import datetime
from sqlalchemy import Column, Integer, String, Text, Boolean, DateTime, Enum, ForeignKey, Index
from sqlalchemy.orm import relationship, DeclarativeBase

class Base(DeclarativeBase):
    pass

class Role(enum.Enum):
    USER = "USER"
    ADMIN = "ADMIN"
    MODERATOR = "MODERATOR"

class User(Base):
    __tablename__ = 'users'

    id = Column(Integer, primary_key=True, autoincrement=True)
    email = Column(String(255), unique=True, nullable=False, index=True)
    name = Column(String(255), nullable=True)
    role = Column(Enum(Role), default=Role.USER, nullable=False)
    posts = relationship('Post', back_populates='author', cascade='all, delete-orphan')
    created_at = Column(DateTime, default=datetime.utcnow, nullable=False)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow, nullable=False)

class Post(Base):
    __tablename__ = 'posts'
    __table_args__ = (
        Index('idx_posts_published', 'published', 'created_at'),
    )

    id = Column(Integer, primary_key=True, autoincrement=True)
    title = Column(String(255), nullable=False)
    body = Column(Text, nullable=True)
    published = Column(Boolean, default=False, nullable=False)
    author_id = Column(Integer, ForeignKey('users.id', ondelete='CASCADE'), nullable=False, index=True)
    author = relationship('User', back_populates='posts')
    created_at = Column(DateTime, default=datetime.utcnow, nullable=False)
```

---

## CRUD Operations

### Create

| ORM | Pattern |
|-----|---------|
| **Prisma** | `await prisma.user.create({ data: { email, name } })` |
| **Drizzle** | `await db.insert(users).values({ email, name }).returning()` |
| **TypeORM** | `await userRepo.save(userRepo.create({ email, name }))` |
| **SQLAlchemy** | `session.add(User(email=email, name=name)); session.commit()` |

### Read (with filter)

| ORM | Pattern |
|-----|---------|
| **Prisma** | `await prisma.user.findMany({ where: { role: 'ADMIN' }, orderBy: { createdAt: 'desc' } })` |
| **Drizzle** | `await db.select().from(users).where(eq(users.role, 'ADMIN')).orderBy(desc(users.createdAt))` |
| **TypeORM** | `await userRepo.find({ where: { role: Role.ADMIN }, order: { createdAt: 'DESC' } })` |
| **SQLAlchemy** | `session.query(User).filter(User.role == Role.ADMIN).order_by(User.created_at.desc()).all()` |

### Update

| ORM | Pattern |
|-----|---------|
| **Prisma** | `await prisma.user.update({ where: { id }, data: { name } })` |
| **Drizzle** | `await db.update(users).set({ name }).where(eq(users.id, id))` |
| **TypeORM** | `await userRepo.update(id, { name })` |
| **SQLAlchemy** | `session.query(User).filter(User.id == id).update({User.name: name}); session.commit()` |

### Delete

| ORM | Pattern |
|-----|---------|
| **Prisma** | `await prisma.user.delete({ where: { id } })` |
| **Drizzle** | `await db.delete(users).where(eq(users.id, id))` |
| **TypeORM** | `await userRepo.delete(id)` |
| **SQLAlchemy** | `session.query(User).filter(User.id == id).delete(); session.commit()` |

---

## Relations and Eager Loading

### Prisma — include / select
```typescript
// Eager load posts with user
const user = await prisma.user.findUnique({
  where: { id: 1 },
  include: { posts: { where: { published: true }, orderBy: { createdAt: 'desc' } } },
});

// Nested create
await prisma.user.create({
  data: {
    email: 'new@example.com',
    posts: { create: [{ title: 'First post' }] },
  },
});
```

### Drizzle — relational queries
```typescript
const result = await db.query.users.findFirst({
  where: eq(users.id, 1),
  with: { posts: { where: eq(posts.published, true), orderBy: [desc(posts.createdAt)] } },
});
```

### TypeORM — relations / query builder
```typescript
// FindOptions
const user = await userRepo.findOne({ where: { id: 1 }, relations: ['posts'] });

// QueryBuilder for complex joins
const result = await userRepo.createQueryBuilder('u')
  .leftJoinAndSelect('u.posts', 'p', 'p.published = :pub', { pub: true })
  .where('u.id = :id', { id: 1 })
  .getOne();
```

### SQLAlchemy — joinedload / selectinload
```python
from sqlalchemy.orm import joinedload, selectinload

# Eager load in one JOIN query
user = session.query(User).options(joinedload(User.posts)).filter(User.id == 1).first()

# Eager load in a separate IN query (better for collections)
users = session.query(User).options(selectinload(User.posts)).all()
```

---

## Raw SQL Escape Hatches

Every ORM should provide a way to execute raw SQL for complex queries:

| ORM | Pattern |
|-----|---------|
| **Prisma** | `` prisma.$queryRaw`SELECT * FROM users WHERE id = ${id}` `` |
| **Drizzle** | `db.execute(sql`SELECT * FROM users WHERE id = ${id}`)` |
| **TypeORM** | `dataSource.query('SELECT * FROM users WHERE id = $1', [id])` |
| **SQLAlchemy** | `session.execute(text('SELECT * FROM users WHERE id = :id'), {'id': id})` |

Always use parameterized queries in raw SQL to prevent injection.

---

## Transaction Patterns

### Prisma
```typescript
await prisma.$transaction(async (tx) => {
  const user = await tx.user.create({ data: { email } });
  await tx.post.create({ data: { title: 'Welcome', authorId: user.id } });
});
```

### Drizzle
```typescript
await db.transaction(async (tx) => {
  const [user] = await tx.insert(users).values({ email }).returning();
  await tx.insert(posts).values({ title: 'Welcome', authorId: user.id });
});
```

### TypeORM
```typescript
await dataSource.transaction(async (manager) => {
  const user = await manager.save(User, { email });
  await manager.save(Post, { title: 'Welcome', authorId: user.id });
});
```

### SQLAlchemy
```python
with Session() as session:
    try:
        user = User(email=email)
        session.add(user)
        session.flush()  # Get user.id without committing
        session.add(Post(title='Welcome', author_id=user.id))
        session.commit()
    except Exception:
        session.rollback()
        raise
```

---

## Migration Workflows

### Prisma
```bash
# Generate migration from schema changes
npx prisma migrate dev --name add_posts_table

# Apply in production
npx prisma migrate deploy

# Reset database (dev only)
npx prisma migrate reset

# Generate client after schema change
npx prisma generate
```

**Files:** `prisma/migrations/<timestamp>_<name>/migration.sql`

### Drizzle
```bash
# Generate migration SQL from schema diff
npx drizzle-kit generate:pg

# Push schema directly (dev only, no migration files)
npx drizzle-kit push:pg

# Apply migrations
npx drizzle-kit migrate
```

**Files:** `drizzle/<timestamp>_<name>.sql`

### TypeORM
```bash
# Auto-generate migration from entity changes
npx typeorm migration:generate -d data-source.ts -n AddPostsTable

# Create empty migration
npx typeorm migration:create -n CustomMigration

# Run pending migrations
npx typeorm migration:run -d data-source.ts

# Revert last migration
npx typeorm migration:revert -d data-source.ts
```

**Files:** `src/migrations/<timestamp>-<Name>.ts`

### SQLAlchemy (Alembic)
```bash
# Initialize Alembic
alembic init alembic

# Auto-generate migration from model changes
alembic revision --autogenerate -m "add posts table"

# Apply all pending
alembic upgrade head

# Revert one step
alembic downgrade -1

# Show current state
alembic current
```

**Files:** `alembic/versions/<hash>_<slug>.py`

---

## N+1 Prevention Cheat Sheet

| ORM | Lazy (N+1 risk) | Eager (fixed) |
|-----|-----------------|---------------|
| **Prisma** | Not accessing `include` | `include: { posts: true }` |
| **Drizzle** | Separate queries | `with: { posts: true }` |
| **TypeORM** | `@ManyToOne(() => ..., { lazy: true })` | `relations: ['posts']` or `leftJoinAndSelect` |
| **SQLAlchemy** | Default `lazy='select'` | `joinedload()` or `selectinload()` |

**Rule of thumb:** If you access a relation inside a loop, you have an N+1 problem. Always load relations before the loop.

---

## Connection Pooling

### Prisma
```
# In .env or connection string
DATABASE_URL="postgresql://user:pass@host/db?connection_limit=20&pool_timeout=10"
```

### Drizzle (with node-postgres)
```typescript
import { Pool } from 'pg';
const pool = new Pool({ max: 20, idleTimeoutMillis: 30000, connectionTimeoutMillis: 5000 });
const db = drizzle(pool);
```

### TypeORM
```typescript
const dataSource = new DataSource({
  type: 'postgres',
  extra: { max: 20, idleTimeoutMillis: 30000 },
});
```

### SQLAlchemy
```python
from sqlalchemy import create_engine
engine = create_engine('postgresql://user:pass@host/db', pool_size=20, max_overflow=5, pool_timeout=30)
```

---

## Best Practices Summary

1. **Always use migrations** — never modify production schemas by hand
2. **Eager load relations** — prevent N+1 in every list/collection query
3. **Use transactions** — group related writes to maintain consistency
4. **Parameterize raw SQL** — never concatenate user input into queries
5. **Connection pooling** — configure pool size matching your workload
6. **Index foreign keys** — ORMs often skip this; add manually if needed
7. **Review generated SQL** — enable query logging in development to catch inefficiencies
8. **Type-safe queries** — leverage TypeScript/Python typing for compile-time checks
9. **Separate read/write models** — use views or read replicas for heavy reporting queries
10. **Test migrations both ways** — always verify that down migrations actually reverse up migrations
