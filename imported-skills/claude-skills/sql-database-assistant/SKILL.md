---
name: "sql-database-assistant"
description: "Use when the user asks to write SQL queries, optimize database performance, generate migrations, explore database schemas, or work with ORMs like Prisma, Drizzle, TypeORM, or SQLAlchemy."
---

# SQL Database Assistant - POWERFUL Tier Skill

## Overview

The operational companion to database design. While **database-designer** focuses on schema architecture and **database-schema-designer** handles ERD modeling, this skill covers the day-to-day: writing queries, optimizing performance, generating migrations, and bridging the gap between application code and database engines.

### Core Capabilities

- **Natural Language to SQL** — translate requirements into correct, performant queries
- **Schema Exploration** — introspect live databases across PostgreSQL, MySQL, SQLite, SQL Server
- **Query Optimization** — EXPLAIN analysis, index recommendations, N+1 detection, rewrite patterns
- **Migration Generation** — up/down scripts, zero-downtime strategies, rollback plans
- **ORM Integration** — Prisma, Drizzle, TypeORM, SQLAlchemy patterns and escape hatches
- **Multi-Database Support** — dialect-aware SQL with compatibility guidance

### Tools

| Script | Purpose |
|--------|---------|
| `scripts/query_optimizer.py` | Static analysis of SQL queries for performance issues |
| `scripts/migration_generator.py` | Generate migration file templates from change descriptions |
| `scripts/schema_explorer.py` | Generate schema documentation from introspection queries |

---

## Natural Language to SQL

### Translation Patterns

When converting requirements to SQL, follow this sequence:

1. **Identify entities** — map nouns to tables
2. **Identify relationships** — map verbs to JOINs or subqueries
3. **Identify filters** — map adjectives/conditions to WHERE clauses
4. **Identify aggregations** — map "total", "average", "count" to GROUP BY
5. **Identify ordering** — map "top", "latest", "highest" to ORDER BY + LIMIT

### Common Query Templates

**Top-N per group (window function)**
```sql
SELECT * FROM (
  SELECT *, ROW_NUMBER() OVER (PARTITION BY department_id ORDER BY salary DESC) AS rn
  FROM employees
) ranked WHERE rn <= 3;
```

**Running totals**
```sql
SELECT date, amount,
  SUM(amount) OVER (ORDER BY date ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW) AS running_total
FROM transactions;
```

**Gap detection**
```sql
SELECT curr.id, curr.seq_num, prev.seq_num AS prev_seq
FROM records curr
LEFT JOIN records prev ON prev.seq_num = curr.seq_num - 1
WHERE prev.id IS NULL AND curr.seq_num > 1;
```

**UPSERT (PostgreSQL)**
```sql
INSERT INTO settings (key, value, updated_at)
VALUES ('theme', 'dark', NOW())
ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value, updated_at = EXCLUDED.updated_at;
```

**UPSERT (MySQL)**
```sql
INSERT INTO settings (key_name, value, updated_at)
VALUES ('theme', 'dark', NOW())
ON DUPLICATE KEY UPDATE value = VALUES(value), updated_at = VALUES(updated_at);
```

> See references/query_patterns.md for JOINs, CTEs, window functions, JSON operations, and more.

---

## Schema Exploration

### Introspection Queries

**PostgreSQL — list tables and columns**
```sql
SELECT table_name, column_name, data_type, is_nullable, column_default
FROM information_schema.columns
WHERE table_schema = 'public'
ORDER BY table_name, ordinal_position;
```

**PostgreSQL — foreign keys**
```sql
SELECT tc.table_name, kcu.column_name,
  ccu.table_name AS foreign_table, ccu.column_name AS foreign_column
FROM information_schema.table_constraints tc
JOIN information_schema.key_column_usage kcu ON tc.constraint_name = kcu.constraint_name
JOIN information_schema.constraint_column_usage ccu ON tc.constraint_name = ccu.constraint_name
WHERE tc.constraint_type = 'FOREIGN KEY';
```

**MySQL — table sizes**
```sql
SELECT table_name, table_rows,
  ROUND(data_length / 1024 / 1024, 2) AS data_mb,
  ROUND(index_length / 1024 / 1024, 2) AS index_mb
FROM information_schema.tables
WHERE table_schema = DATABASE()
ORDER BY data_length DESC;
```

**SQLite — schema dump**
```sql
SELECT name, sql FROM sqlite_master WHERE type = 'table' ORDER BY name;
```

**SQL Server — columns with types**
```sql
SELECT t.name AS table_name, c.name AS column_name,
  ty.name AS data_type, c.max_length, c.is_nullable
FROM sys.columns c
JOIN sys.tables t ON c.object_id = t.object_id
JOIN sys.types ty ON c.user_type_id = ty.user_type_id
ORDER BY t.name, c.column_id;
```

### Generating Documentation from Schema

Use `scripts/schema_explorer.py` to produce markdown or JSON documentation:

```bash
python scripts/schema_explorer.py --dialect postgres --tables all --format md
python scripts/schema_explorer.py --dialect mysql --tables users,orders --format json --json
```

---

## Query Optimization

### EXPLAIN Analysis Workflow

1. **Run EXPLAIN ANALYZE** (PostgreSQL) or **EXPLAIN FORMAT=JSON** (MySQL)
2. **Identify the costliest node** — Seq Scan on large tables, Nested Loop with high row estimates
3. **Check for missing indexes** — sequential scans on filtered columns
4. **Look for estimation errors** — planned vs actual rows divergence signals stale statistics
5. **Evaluate JOIN order** — ensure the smallest result set drives the join

### Index Recommendation Checklist

- Columns in WHERE clauses with high selectivity
- Columns in JOIN conditions (foreign keys)
- Columns in ORDER BY when combined with LIMIT
- Composite indexes matching multi-column WHERE predicates (most selective column first)
- Partial indexes for queries with constant filters (e.g., `WHERE status = 'active'`)
- Covering indexes to avoid table lookups for read-heavy queries

### Query Rewriting Patterns

| Anti-Pattern | Rewrite |
|-------------|---------|
| `SELECT * FROM orders` | `SELECT id, status, total FROM orders` (explicit columns) |
| `WHERE YEAR(created_at) = 2025` | `WHERE created_at >= '2025-01-01' AND created_at < '2026-01-01'` (sargable) |
| Correlated subquery in SELECT | LEFT JOIN with aggregation |
| `NOT IN (SELECT ...)` with NULLs | `NOT EXISTS (SELECT 1 ...)` |
| `UNION` (dedup) when not needed | `UNION ALL` |
| `LIKE '%search%'` | Full-text search index (GIN/FULLTEXT) |
| `ORDER BY RAND()` | Application-side random sampling or `TABLESAMPLE` |

### N+1 Detection

**Symptoms:**
- Application loop that executes one query per parent row
- ORM lazy-loading related entities inside a loop
- Query log shows hundreds of identical SELECT patterns with different IDs

**Fixes:**
- Use eager loading (`include` in Prisma, `joinedload` in SQLAlchemy)
- Batch queries with `WHERE id IN (...)`
- Use DataLoader pattern for GraphQL resolvers

### Static Analysis Tool

```bash
python scripts/query_optimizer.py --query "SELECT * FROM orders WHERE status = 'pending'" --dialect postgres
python scripts/query_optimizer.py --query queries.sql --dialect mysql --json
```

> See references/optimization_guide.md for EXPLAIN plan reading, index types, and connection pooling.

---

## Migration Generation

### Zero-Downtime Migration Patterns

**Adding a column (safe)**
```sql
-- Up
ALTER TABLE users ADD COLUMN phone VARCHAR(20);

-- Down
ALTER TABLE users DROP COLUMN phone;
```

**Renaming a column (expand-contract)**
```sql
-- Step 1: Add new column
ALTER TABLE users ADD COLUMN full_name VARCHAR(255);
-- Step 2: Backfill
UPDATE users SET full_name = name;
-- Step 3: Deploy app reading both columns
-- Step 4: Deploy app writing only new column
-- Step 5: Drop old column
ALTER TABLE users DROP COLUMN name;
```

**Adding a NOT NULL column (safe sequence)**
```sql
-- Step 1: Add nullable
ALTER TABLE orders ADD COLUMN region VARCHAR(50);
-- Step 2: Backfill with default
UPDATE orders SET region = 'unknown' WHERE region IS NULL;
-- Step 3: Add constraint
ALTER TABLE orders ALTER COLUMN region SET NOT NULL;
ALTER TABLE orders ALTER COLUMN region SET DEFAULT 'unknown';
```

**Index creation (non-blocking, PostgreSQL)**
```sql
CREATE INDEX CONCURRENTLY idx_orders_status ON orders (status);
```

### Data Backfill Strategies

- **Batch updates** — process in chunks of 1000-10000 rows to avoid lock contention
- **Background jobs** — run backfills asynchronously with progress tracking
- **Dual-write** — write to old and new columns during transition period
- **Validation queries** — verify row counts and data integrity after each batch

### Rollback Strategies

Every migration must have a reversible down script. For irreversible changes:

1. **Backup before execution** — `pg_dump` the affected tables
2. **Feature flags** — application can switch between old/new schema reads
3. **Shadow tables** — keep a copy of the original table during migration window

### Migration Generator Tool

```bash
python scripts/migration_generator.py --change "add email_verified boolean to users" --dialect postgres --format sql
python scripts/migration_generator.py --change "rename column name to full_name in customers" --dialect mysql --format alembic --json
```

---

## Multi-Database Support

### Dialect Differences

| Feature | PostgreSQL | MySQL | SQLite | SQL Server |
|---------|-----------|-------|--------|------------|
| UPSERT | `ON CONFLICT DO UPDATE` | `ON DUPLICATE KEY UPDATE` | `ON CONFLICT DO UPDATE` | `MERGE` |
| Boolean | Native `BOOLEAN` | `TINYINT(1)` | `INTEGER` | `BIT` |
| Auto-increment | `SERIAL` / `GENERATED` | `AUTO_INCREMENT` | `INTEGER PRIMARY KEY` | `IDENTITY` |
| JSON | `JSONB` (indexed) | `JSON` | Text (ext) | `NVARCHAR(MAX)` |
| Array | Native `ARRAY` | Not supported | Not supported | Not supported |
| CTE (recursive) | Full support | 8.0+ | 3.8.3+ | Full support |
| Window functions | Full support | 8.0+ | 3.25.0+ | Full support |
| Full-text search | `tsvector` + GIN | `FULLTEXT` index | FTS5 extension | Full-text catalog |
| LIMIT/OFFSET | `LIMIT n OFFSET m` | `LIMIT n OFFSET m` | `LIMIT n OFFSET m` | `OFFSET m ROWS FETCH NEXT n ROWS ONLY` |

### Compatibility Tips

- **Always use parameterized queries** — prevents SQL injection across all dialects
- **Avoid dialect-specific functions in shared code** — wrap in adapter layer
- **Test migrations on target engine** — `information_schema` varies between engines
- **Use ISO date format** — `'YYYY-MM-DD'` works everywhere
- **Quote identifiers** — use double quotes (SQL standard) or backticks (MySQL)

---

## ORM Patterns

### Prisma

**Schema definition**
```prisma
model User {
  id        Int      @id @default(autoincrement())
  email     String   @unique
  name      String?
  posts     Post[]
  createdAt DateTime @default(now())
}

model Post {
  id       Int    @id @default(autoincrement())
  title    String
  author   User   @relation(fields: [authorId], references: [id])
  authorId Int
}
```

**Migrations**: `npx prisma migrate dev --name add_user_email`
**Query API**: `prisma.user.findMany({ where: { email: { contains: '@' } }, include: { posts: true } })`
**Raw SQL escape hatch**: `prisma.$queryRaw\`SELECT * FROM users WHERE id = ${userId}\``

### Drizzle

**Schema-first definition**
```typescript
export const users = pgTable('users', {
  id: serial('id').primaryKey(),
  email: varchar('email', { length: 255 }).notNull().unique(),
  name: text('name'),
  createdAt: timestamp('created_at').defaultNow(),
});
```

**Query builder**: `db.select().from(users).where(eq(users.email, email))`
**Migrations**: `npx drizzle-kit generate:pg` then `npx drizzle-kit push:pg`

### TypeORM

**Entity decorators**
```typescript
@Entity()
export class User {
  @PrimaryGeneratedColumn()
  id: number;

  @Column({ unique: true })
  email: string;

  @OneToMany(() => Post, post => post.author)
  posts: Post[];
}
```

**Repository pattern**: `userRepo.find({ where: { email }, relations: ['posts'] })`
**Migrations**: `npx typeorm migration:generate -n AddUserEmail`

### SQLAlchemy

**Declarative models**
```python
class User(Base):
    __tablename__ = 'users'
    id = Column(Integer, primary_key=True)
    email = Column(String(255), unique=True, nullable=False)
    name = Column(String(255))
    posts = relationship('Post', back_populates='author')
```

**Session management**: Always use `with Session() as session:` context manager
**Alembic migrations**: `alembic revision --autogenerate -m "add user email"`

> See references/orm_patterns.md for side-by-side comparisons and migration workflows per ORM.

---

## Data Integrity

### Constraint Strategy

- **Primary keys** — every table must have one; prefer surrogate keys (serial/UUID)
- **Foreign keys** — enforce referential integrity; define ON DELETE behavior explicitly
- **UNIQUE constraints** — for business-level uniqueness (email, slug, API key)
- **CHECK constraints** — validate ranges, enums, and business rules at the DB level
- **NOT NULL** — default to NOT NULL; make nullable only when genuinely optional

### Transaction Isolation Levels

| Level | Dirty Read | Non-Repeatable Read | Phantom Read | Use Case |
|-------|-----------|-------------------|-------------|----------|
| READ UNCOMMITTED | Yes | Yes | Yes | Never recommended |
| READ COMMITTED | No | Yes | Yes | Default for PostgreSQL, general OLTP |
| REPEATABLE READ | No | No | Yes (InnoDB: No) | Financial calculations |
| SERIALIZABLE | No | No | No | Critical consistency (billing, inventory) |

### Deadlock Prevention

1. **Consistent lock ordering** — always acquire locks in the same table/row order
2. **Short transactions** — minimize time between first lock and commit
3. **Advisory locks** — use `pg_advisory_lock()` for application-level coordination
4. **Retry logic** — catch deadlock errors and retry with exponential backoff

---

## Backup & Restore

### PostgreSQL
```bash
# Full backup
pg_dump -Fc --no-owner dbname > backup.dump
# Restore
pg_restore -d dbname --clean --no-owner backup.dump
# Point-in-time recovery: configure WAL archiving + restore_command
```

### MySQL
```bash
# Full backup
mysqldump --single-transaction --routines --triggers dbname > backup.sql
# Restore
mysql dbname < backup.sql
# Binary log for PITR: mysqlbinlog --start-datetime="2025-01-01 00:00:00" binlog.000001
```

### SQLite
```bash
# Backup (safe with concurrent reads)
sqlite3 dbname ".backup backup.db"
```

### Backup Best Practices
- **Automate** — cron or systemd timer, never manual-only
- **Test restores** — untested backups are not backups
- **Offsite copies** — S3, GCS, or separate region
- **Retention policy** — daily for 7 days, weekly for 4 weeks, monthly for 12 months
- **Monitor backup size and duration** — sudden changes signal issues

---

## Anti-Patterns

| Anti-Pattern | Problem | Fix |
|-------------|---------|-----|
| `SELECT *` | Transfers unnecessary data, breaks on schema changes | Explicit column list |
| Missing indexes on FK columns | Slow JOINs and cascading deletes | Add indexes on all foreign keys |
| N+1 queries | 1 + N round trips to database | Eager loading or batch queries |
| Implicit type coercion | `WHERE id = '123'` prevents index use | Match types in predicates |
| No connection pooling | Exhausts connections under load | PgBouncer, ProxySQL, or ORM pool |
| Unbounded queries | No LIMIT risks returning millions of rows | Always paginate |
| Storing money as FLOAT | Rounding errors | Use `DECIMAL(19,4)` or integer cents |
| God tables | One table with 50+ columns | Normalize or use vertical partitioning |
| Soft deletes everywhere | Complicates every query with `WHERE deleted_at IS NULL` | Archive tables or event sourcing |
| Raw string concatenation | SQL injection | Parameterized queries always |

---

## Cross-References

| Skill | Relationship |
|-------|-------------|
| **database-designer** | Schema architecture, normalization analysis, ERD generation |
| **database-schema-designer** | Visual ERD modeling, relationship mapping |
| **migration-architect** | Complex multi-step migration orchestration |
| **api-design-reviewer** | Ensuring API endpoints align with query patterns |
| **observability-platform** | Query performance monitoring, slow query alerts |
