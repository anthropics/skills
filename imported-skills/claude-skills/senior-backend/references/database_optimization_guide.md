# Database Optimization Guide

Practical strategies for PostgreSQL query optimization, indexing, and performance tuning.

## Guide Index

1. [Query Analysis with EXPLAIN](#1-query-analysis-with-explain)
2. [Indexing Strategies](#2-indexing-strategies)
3. [N+1 Query Problem](#3-n1-query-problem)
4. [Connection Pooling](#4-connection-pooling)
5. [Query Optimization Patterns](#5-query-optimization-patterns)
6. [Database Migrations](#6-database-migrations)
7. [Monitoring and Alerting](#7-monitoring-and-alerting)

---

## 1. Query Analysis with EXPLAIN

### Basic EXPLAIN Usage

```sql
-- Show query plan
EXPLAIN SELECT * FROM orders WHERE user_id = 123;

-- Show plan with actual execution times
EXPLAIN ANALYZE SELECT * FROM orders WHERE user_id = 123;

-- Show buffers and I/O statistics
EXPLAIN (ANALYZE, BUFFERS, FORMAT TEXT)
SELECT * FROM orders WHERE user_id = 123;
```

### Reading EXPLAIN Output

```
                                    QUERY PLAN
---------------------------------------------------------------------------
 Index Scan using idx_orders_user_id on orders  (cost=0.43..8.45 rows=10 width=120)
   Index Cond: (user_id = 123)
   Buffers: shared hit=3
 Planning Time: 0.152 ms
 Execution Time: 0.089 ms
```

**Key metrics:**
- `cost`: Estimated cost (startup..total)
- `rows`: Estimated row count
- `width`: Average row size in bytes
- `actual time`: Real execution time (with ANALYZE)
- `Buffers: shared hit`: Pages read from cache

### Scan Types (Best to Worst)

| Scan Type | Description | Performance |
|-----------|-------------|-------------|
| Index Only Scan | Data from index alone | Best |
| Index Scan | Index lookup + heap fetch | Good |
| Bitmap Index Scan | Multiple index conditions | Good |
| Index Scan + Filter | Index + row filtering | Okay |
| Seq Scan (small table) | Full table scan | Okay |
| Seq Scan (large table) | Full table scan | Bad |
| Nested Loop (large) | O(n*m) join | Very Bad |

### Warning Signs

```sql
-- BAD: Sequential scan on large table
Seq Scan on orders  (cost=0.00..1854231.00 rows=50000000 width=120)
  Filter: (status = 'pending')
  Rows Removed by Filter: 49500000

-- BAD: Nested loop with high iterations
Nested Loop  (cost=0.43..2847593.20 rows=12500000 width=240)
  ->  Seq Scan on users  (cost=0.00..1250.00 rows=50000 width=120)
  ->  Index Scan on orders  (cost=0.43..45.73 rows=250 width=120)
       Index Cond: (orders.user_id = users.id)
```

---

## 2. Indexing Strategies

### Index Types

```sql
-- B-tree (default, most common)
CREATE INDEX idx_users_email ON users(email);

-- Hash (equality only, rarely better than B-tree)
CREATE INDEX idx_users_id_hash ON users USING hash(id);

-- GIN (arrays, JSONB, full-text search)
CREATE INDEX idx_products_tags ON products USING gin(tags);
CREATE INDEX idx_users_data ON users USING gin(metadata jsonb_path_ops);

-- GiST (geometric, range types, full-text)
CREATE INDEX idx_locations_point ON locations USING gist(coordinates);
```

### Composite Indexes

```sql
-- Order matters! Column with = first, then range/sort
CREATE INDEX idx_orders_user_status_date
ON orders(user_id, status, created_at DESC);

-- This index supports:
-- WHERE user_id = ?
-- WHERE user_id = ? AND status = ?
-- WHERE user_id = ? AND status = ? ORDER BY created_at DESC
-- WHERE user_id = ? ORDER BY created_at DESC

-- This index does NOT efficiently support:
-- WHERE status = ? (user_id not in query)
-- WHERE created_at > ? (leftmost column not in query)
```

### Partial Indexes

```sql
-- Index only active users (smaller, faster)
CREATE INDEX idx_users_active_email
ON users(email)
WHERE status = 'active';

-- Index only recent orders
CREATE INDEX idx_orders_recent
ON orders(created_at DESC)
WHERE created_at > CURRENT_DATE - INTERVAL '90 days';

-- Index only unprocessed items
CREATE INDEX idx_queue_pending
ON job_queue(priority DESC, created_at)
WHERE processed_at IS NULL;
```

### Covering Indexes (Index-Only Scans)

```sql
-- Include non-indexed columns to avoid heap lookup
CREATE INDEX idx_users_email_covering
ON users(email)
INCLUDE (name, created_at);

-- Query can be satisfied from index alone
SELECT name, created_at FROM users WHERE email = 'test@example.com';
-- Result: Index Only Scan
```

### Index Maintenance

```sql
-- Check index usage
SELECT
    schemaname,
    tablename,
    indexname,
    idx_scan,
    idx_tup_read,
    idx_tup_fetch,
    pg_size_pretty(pg_relation_size(indexrelid)) as size
FROM pg_stat_user_indexes
ORDER BY idx_scan ASC;

-- Find unused indexes (candidates for removal)
SELECT indexrelid::regclass as index,
       relid::regclass as table,
       pg_size_pretty(pg_relation_size(indexrelid)) as size
FROM pg_stat_user_indexes
WHERE idx_scan = 0
  AND indexrelid NOT IN (SELECT conindid FROM pg_constraint);

-- Rebuild bloated indexes
REINDEX INDEX CONCURRENTLY idx_orders_user_id;
```

---

## 3. N+1 Query Problem

### The Problem

```typescript
// BAD: N+1 queries
const users = await db.query('SELECT * FROM users LIMIT 100');

for (const user of users) {
  // This runs 100 times!
  const orders = await db.query(
    'SELECT * FROM orders WHERE user_id = $1',
    [user.id]
  );
  user.orders = orders;
}
// Total queries: 1 + 100 = 101
```

### Solution 1: JOIN

```typescript
// GOOD: Single query with JOIN
const usersWithOrders = await db.query(`
  SELECT u.*, o.id as order_id, o.total, o.status
  FROM users u
  LEFT JOIN orders o ON o.user_id = u.id
  LIMIT 100
`);
// Total queries: 1
```

### Solution 2: Batch Loading (DataLoader pattern)

```typescript
// GOOD: Two queries with batch loading
const users = await db.query('SELECT * FROM users LIMIT 100');
const userIds = users.map(u => u.id);

const orders = await db.query(
  'SELECT * FROM orders WHERE user_id = ANY($1)',
  [userIds]
);

// Group orders by user_id
const ordersByUser = groupBy(orders, 'user_id');
users.forEach(user => {
  user.orders = ordersByUser[user.id] || [];
});
// Total queries: 2
```

### Solution 3: ORM Eager Loading

```typescript
// Prisma
const users = await prisma.user.findMany({
  take: 100,
  include: { orders: true }
});

// TypeORM
const users = await userRepository.find({
  take: 100,
  relations: ['orders']
});

// Sequelize
const users = await User.findAll({
  limit: 100,
  include: [{ model: Order }]
});
```

### Detecting N+1 in Production

```typescript
// Query logging middleware
let queryCount = 0;
const originalQuery = db.query;

db.query = async (...args) => {
  queryCount++;
  if (queryCount > 10) {
    console.warn(`High query count: ${queryCount} in single request`);
    console.trace();
  }
  return originalQuery.apply(db, args);
};
```

---

## 4. Connection Pooling

### Why Pooling Matters

```
Without pooling:
Request → Create connection → Query → Close connection
         (50-100ms overhead)

With pooling:
Request → Get connection from pool → Query → Return to pool
         (0-1ms overhead)
```

### pg-pool Configuration

```typescript
import { Pool } from 'pg';

const pool = new Pool({
  host: process.env.DB_HOST,
  port: 5432,
  database: process.env.DB_NAME,
  user: process.env.DB_USER,
  password: process.env.DB_PASSWORD,

  // Pool settings
  min: 5,                    // Minimum connections
  max: 20,                   // Maximum connections
  idleTimeoutMillis: 30000,  // Close idle connections after 30s
  connectionTimeoutMillis: 5000, // Fail if can't connect in 5s

  // Statement timeout (cancel long queries)
  statement_timeout: 30000,
});

// Health check
pool.on('error', (err, client) => {
  console.error('Unexpected pool error', err);
});
```

### Pool Sizing Formula

```
Optimal connections = (CPU cores * 2) + effective_spindle_count

For SSD with 4 cores:
connections = (4 * 2) + 1 = 9

For multiple app servers:
connections_per_server = total_connections / num_servers
```

### PgBouncer for High Scale

```ini
# pgbouncer.ini
[databases]
mydb = host=localhost port=5432 dbname=mydb

[pgbouncer]
listen_port = 6432
listen_addr = 0.0.0.0
auth_type = md5
auth_file = /etc/pgbouncer/userlist.txt
pool_mode = transaction
max_client_conn = 1000
default_pool_size = 20
reserve_pool_size = 5
```

---

## 5. Query Optimization Patterns

### Pagination Optimization

```sql
-- BAD: OFFSET is slow for large values
SELECT * FROM orders ORDER BY created_at DESC LIMIT 20 OFFSET 10000;
-- Must scan 10,020 rows, discard 10,000

-- GOOD: Cursor-based pagination
SELECT * FROM orders
WHERE created_at < '2024-01-15T10:00:00Z'
ORDER BY created_at DESC
LIMIT 20;
-- Only scans 20 rows
```

### Batch Updates

```sql
-- BAD: Individual updates
UPDATE orders SET status = 'shipped' WHERE id = 1;
UPDATE orders SET status = 'shipped' WHERE id = 2;
-- ...repeat 1000 times

-- GOOD: Batch update
UPDATE orders
SET status = 'shipped'
WHERE id = ANY(ARRAY[1, 2, 3, ...1000]);

-- GOOD: Update from values
UPDATE orders o
SET status = v.new_status
FROM (VALUES
  (1, 'shipped'),
  (2, 'delivered'),
  (3, 'cancelled')
) AS v(id, new_status)
WHERE o.id = v.id;
```

### Avoiding SELECT *

```sql
-- BAD: Fetches all columns including large text/blob
SELECT * FROM articles WHERE published = true;

-- GOOD: Only fetch needed columns
SELECT id, title, summary, author_id, published_at
FROM articles
WHERE published = true;
```

### Using EXISTS vs IN

```sql
-- For checking existence, EXISTS is often faster
-- BAD
SELECT * FROM users
WHERE id IN (SELECT user_id FROM orders WHERE total > 1000);

-- GOOD (for large subquery results)
SELECT * FROM users u
WHERE EXISTS (
  SELECT 1 FROM orders o
  WHERE o.user_id = u.id AND o.total > 1000
);
```

### Materialized Views for Complex Aggregations

```sql
-- Create materialized view for expensive aggregations
CREATE MATERIALIZED VIEW daily_sales_summary AS
SELECT
  date_trunc('day', created_at) as date,
  product_id,
  COUNT(*) as order_count,
  SUM(quantity) as total_quantity,
  SUM(total) as total_revenue
FROM orders
GROUP BY date_trunc('day', created_at), product_id;

-- Create index on materialized view
CREATE INDEX idx_daily_sales_date ON daily_sales_summary(date);

-- Refresh periodically
REFRESH MATERIALIZED VIEW CONCURRENTLY daily_sales_summary;
```

---

## 6. Database Migrations

### Migration Best Practices

```sql
-- Always include rollback
-- migrations/20240115_001_add_user_status.sql
-- UP
ALTER TABLE users ADD COLUMN status VARCHAR(20) DEFAULT 'active';
CREATE INDEX CONCURRENTLY idx_users_status ON users(status);

-- DOWN (in separate file or comment)
DROP INDEX CONCURRENTLY IF EXISTS idx_users_status;
ALTER TABLE users DROP COLUMN IF EXISTS status;
```

### Safe Column Addition

```sql
-- SAFE: Add nullable column (no table rewrite)
ALTER TABLE users ADD COLUMN phone VARCHAR(20);

-- SAFE: Add column with volatile default (PG 11+)
ALTER TABLE users ADD COLUMN created_at TIMESTAMP DEFAULT NOW();

-- UNSAFE: Add column with constant default (table rewrite before PG 11)
-- ALTER TABLE users ADD COLUMN score INTEGER DEFAULT 0;

-- SAFE alternative for constant default:
ALTER TABLE users ADD COLUMN score INTEGER;
UPDATE users SET score = 0 WHERE score IS NULL;
ALTER TABLE users ALTER COLUMN score SET DEFAULT 0;
ALTER TABLE users ALTER COLUMN score SET NOT NULL;
```

### Safe Index Creation

```sql
-- UNSAFE: Locks table
CREATE INDEX idx_orders_user ON orders(user_id);

-- SAFE: Non-blocking
CREATE INDEX CONCURRENTLY idx_orders_user ON orders(user_id);

-- Note: CONCURRENTLY cannot run in a transaction
```

### Safe Column Removal

```sql
-- Step 1: Stop writing to column (application change)
-- Step 2: Wait for all deployments
-- Step 3: Drop column
ALTER TABLE users DROP COLUMN IF EXISTS legacy_field;
```

---

## 7. Monitoring and Alerting

### Key Metrics to Monitor

```sql
-- Active connections
SELECT count(*) FROM pg_stat_activity WHERE state = 'active';

-- Connection by state
SELECT state, count(*)
FROM pg_stat_activity
GROUP BY state;

-- Long-running queries
SELECT
  pid,
  now() - pg_stat_activity.query_start AS duration,
  query,
  state
FROM pg_stat_activity
WHERE (now() - pg_stat_activity.query_start) > interval '5 minutes'
  AND state != 'idle';

-- Table bloat
SELECT
  schemaname,
  tablename,
  pg_size_pretty(pg_total_relation_size(schemaname||'.'||tablename)) as total_size,
  pg_size_pretty(pg_relation_size(schemaname||'.'||tablename)) as table_size,
  pg_size_pretty(pg_indexes_size(schemaname||'.'||tablename)) as index_size
FROM pg_tables
WHERE schemaname = 'public'
ORDER BY pg_total_relation_size(schemaname||'.'||tablename) DESC
LIMIT 10;
```

### pg_stat_statements for Query Analysis

```sql
-- Enable extension
CREATE EXTENSION IF NOT EXISTS pg_stat_statements;

-- Find slowest queries
SELECT
  round(total_exec_time::numeric, 2) as total_time_ms,
  calls,
  round(mean_exec_time::numeric, 2) as avg_time_ms,
  round((100 * total_exec_time / sum(total_exec_time) over())::numeric, 2) as percentage,
  query
FROM pg_stat_statements
ORDER BY total_exec_time DESC
LIMIT 10;

-- Find most frequent queries
SELECT
  calls,
  round(total_exec_time::numeric, 2) as total_time_ms,
  round(mean_exec_time::numeric, 2) as avg_time_ms,
  query
FROM pg_stat_statements
ORDER BY calls DESC
LIMIT 10;
```

### Alert Thresholds

| Metric | Warning | Critical |
|--------|---------|----------|
| Connection usage | > 70% | > 90% |
| Query time P95 | > 500ms | > 2s |
| Replication lag | > 30s | > 5m |
| Disk usage | > 70% | > 85% |
| Cache hit ratio | < 95% | < 90% |

---

## Quick Reference: PostgreSQL Commands

```sql
-- Check table sizes
SELECT pg_size_pretty(pg_total_relation_size('orders'));

-- Check index sizes
SELECT pg_size_pretty(pg_indexes_size('orders'));

-- Kill a query
SELECT pg_cancel_backend(pid);  -- Graceful
SELECT pg_terminate_backend(pid);  -- Force

-- Check locks
SELECT * FROM pg_locks WHERE granted = false;

-- Vacuum analyze (update statistics)
VACUUM ANALYZE orders;

-- Check autovacuum status
SELECT * FROM pg_stat_user_tables WHERE relname = 'orders';
```
