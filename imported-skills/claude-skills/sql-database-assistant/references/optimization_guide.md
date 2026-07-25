# Query Optimization Guide

How to read EXPLAIN plans, choose the right index types, understand query plan operators, and configure connection pooling.

---

## Reading EXPLAIN Plans

### PostgreSQL — EXPLAIN ANALYZE

```sql
EXPLAIN (ANALYZE, BUFFERS, FORMAT TEXT) SELECT * FROM orders WHERE status = 'paid' ORDER BY created_at DESC LIMIT 20;
```

**Sample output:**
```
Limit  (cost=0.43..12.87 rows=20 width=128) (actual time=0.052..0.089 rows=20 loops=1)
  ->  Index Scan Backward using idx_orders_status_created on orders  (cost=0.43..4521.33 rows=7284 width=128) (actual time=0.051..0.085 rows=20 loops=1)
        Index Cond: (status = 'paid')
        Buffers: shared hit=4
Planning Time: 0.156 ms
Execution Time: 0.112 ms
```

**Key fields to check:**

| Field | What it tells you |
|-------|-------------------|
| `cost` | Estimated startup..total cost (arbitrary units) |
| `rows` | Estimated row count at that node |
| `actual time` | Real wall-clock time in milliseconds |
| `actual rows` | Real row count — compare against estimate |
| `Buffers: shared hit` | Pages read from cache (good) |
| `Buffers: shared read` | Pages read from disk (slow) |
| `loops` | How many times the node executed |

**Red flags:**
- `Seq Scan` on a large table with a WHERE clause — missing index
- `actual rows` >> `rows` (estimated) — stale statistics, run `ANALYZE`
- `Nested Loop` with high loop count — consider hash join or add index
- `Sort` with `external merge` — not enough `work_mem`, spilling to disk
- `Buffers: shared read` much higher than `shared hit` — cold cache or table too large for memory

### MySQL — EXPLAIN FORMAT=JSON

```sql
EXPLAIN FORMAT=JSON SELECT * FROM orders WHERE status = 'paid' ORDER BY created_at DESC LIMIT 20;
```

**Key fields:**
- `query_block.select_id` — identifies subqueries
- `table.access_type` — `ALL` (full scan), `ref` (index lookup), `range`, `index`, `const`
- `table.rows_examined_per_scan` — how many rows the engine reads
- `table.using_index` — covering index (no table lookup needed)
- `table.attached_condition` — the WHERE filter applied

**Access types ranked (best to worst):**
`system` > `const` > `eq_ref` > `ref` > `range` > `index` > `ALL`

---

## Index Types

### B-tree (default)

The workhorse index. Supports equality, range, prefix, and ORDER BY operations.

**Best for:** `=`, `<`, `>`, `<=`, `>=`, `BETWEEN`, `LIKE 'prefix%'`, `ORDER BY`, `MIN()`, `MAX()`

```sql
CREATE INDEX idx_orders_created ON orders (created_at);
```

**Composite B-tree:** Column order matters. The index is useful for queries that filter on a leftmost prefix of the indexed columns.

```sql
-- This index serves: WHERE status = ... AND created_at > ...
-- Also serves: WHERE status = ...
-- Does NOT serve: WHERE created_at > ... (without status)
CREATE INDEX idx_orders_status_created ON orders (status, created_at);
```

### Hash

Equality-only lookups. Faster than B-tree for exact matches but no range support.

**Best for:** `=` lookups on high-cardinality columns

```sql
-- PostgreSQL
CREATE INDEX idx_sessions_token ON sessions USING hash (token);
```

**Limitations:** No range queries, no ORDER BY, not WAL-logged before PostgreSQL 10.

### GIN (Generalized Inverted Index)

For multi-valued data: arrays, JSONB, full-text search vectors.

```sql
-- JSONB containment
CREATE INDEX idx_products_tags ON products USING gin (tags);
-- Query: SELECT * FROM products WHERE tags @> '["sale"]';

-- Full-text search
CREATE INDEX idx_articles_search ON articles USING gin (to_tsvector('english', title || ' ' || body));
```

### GiST (Generalized Search Tree)

For geometric, range, and proximity data.

```sql
-- Range type (e.g., date ranges)
CREATE INDEX idx_bookings_period ON bookings USING gist (during);
-- Query: SELECT * FROM bookings WHERE during && '[2025-01-01, 2025-01-31]';

-- PostGIS geometry
CREATE INDEX idx_locations_geom ON locations USING gist (geom);
```

### BRIN (Block Range INdex)

Tiny index for naturally ordered data (e.g., time-series append-only tables).

```sql
CREATE INDEX idx_events_created ON events USING brin (created_at);
```

**Best for:** Large tables where the indexed column correlates with physical row order. Much smaller than B-tree but less precise.

### Partial Index

Index only rows matching a condition. Smaller and faster for targeted queries.

```sql
-- Only index active users (skip millions of inactive)
CREATE INDEX idx_users_active_email ON users (email) WHERE status = 'active';
```

### Covering Index (INCLUDE)

Store extra columns in the index to avoid table lookups (index-only scans).

```sql
-- PostgreSQL 11+
CREATE INDEX idx_orders_status ON orders (status) INCLUDE (total, created_at);
-- Query can be answered entirely from the index:
-- SELECT total, created_at FROM orders WHERE status = 'paid';
```

### Expression Index

Index the result of a function or expression.

```sql
CREATE INDEX idx_users_lower_email ON users (LOWER(email));
-- Query: SELECT * FROM users WHERE LOWER(email) = 'user@example.com';
```

---

## Query Plan Operators

### Scan operators

| Operator | Description | Performance |
|----------|-------------|-------------|
| **Seq Scan** | Full table scan, reads every row | Slow on large tables |
| **Index Scan** | B-tree lookup + table fetch | Fast for selective queries |
| **Index Only Scan** | Reads only the index (covering) | Fastest for covered queries |
| **Bitmap Index Scan** | Builds a bitmap of matching pages | Good for medium selectivity |
| **Bitmap Heap Scan** | Fetches pages identified by bitmap | Pairs with bitmap index scan |

### Join operators

| Operator | Description | Best when |
|----------|-------------|-----------|
| **Nested Loop** | For each outer row, scan inner | Small outer set, indexed inner |
| **Hash Join** | Build hash table on inner, probe with outer | Medium-large sets, no index |
| **Merge Join** | Merge two sorted inputs | Both inputs already sorted |

### Other operators

| Operator | Description |
|----------|-------------|
| **Sort** | Sorts rows (may spill to disk if work_mem exceeded) |
| **Hash Aggregate** | GROUP BY using hash table |
| **Group Aggregate** | GROUP BY on pre-sorted input |
| **Limit** | Stops after N rows |
| **Materialize** | Caches subquery results in memory |
| **Gather / Gather Merge** | Collects results from parallel workers |

---

## Connection Pooling

### Why pool connections?

Each database connection consumes memory (5-10 MB in PostgreSQL). Without pooling:
- Application creates a new connection per request (slow: TCP + TLS + auth)
- Under load, connection count spikes past `max_connections`
- Database OOM or connection refused errors

### PgBouncer (PostgreSQL)

The standard external connection pooler for PostgreSQL.

**Modes:**
- **Session** — connection assigned for entire client session (safest, least efficient)
- **Transaction** — connection returned to pool after each transaction (recommended)
- **Statement** — connection returned after each statement (cannot use transactions)

```ini
# pgbouncer.ini
[databases]
mydb = host=127.0.0.1 port=5432 dbname=mydb

[pgbouncer]
pool_mode = transaction
max_client_conn = 200
default_pool_size = 20
min_pool_size = 5
reserve_pool_size = 5
reserve_pool_timeout = 3
server_idle_timeout = 300
```

**Sizing formula:**
```
default_pool_size = num_cpu_cores * 2 + effective_spindle_count
```
For SSDs, start with `num_cpu_cores * 2` (typically 4-16 connections is optimal).

### ProxySQL (MySQL)

```ini
mysql_servers = ({ address="127.0.0.1", port=3306, hostgroup=0, max_connections=100 })
mysql_query_rules = ({ rule_id=1, match_pattern="^SELECT.*FOR UPDATE", destination_hostgroup=0 })
```

### Application-Level Pooling

Most ORMs and drivers include built-in pooling:

| Platform | Pool Configuration |
|----------|--------------------|
| **node-postgres** | `new Pool({ max: 20, idleTimeoutMillis: 30000 })` |
| **SQLAlchemy** | `create_engine(url, pool_size=20, max_overflow=5)` |
| **HikariCP (Java)** | `maximumPoolSize=20, minimumIdle=5, idleTimeout=300000` |
| **Prisma** | `connection_limit=20` in connection string |

### Pool Sizing Guidelines

| Metric | Guideline |
|--------|-----------|
| **Minimum** | Number of always-active background workers |
| **Maximum** | 2-4x CPU cores for OLTP; lower for OLAP |
| **Idle timeout** | 30-300 seconds (reclaim unused connections) |
| **Connection timeout** | 3-10 seconds (fail fast under pressure) |
| **Queue size** | 2-5x pool max (buffer bursts before rejecting) |

**Warning:** More connections does not mean better performance. Beyond the optimal point (usually 20-50), contention on locks, CPU, and I/O causes throughput to decrease.

---

## Statistics and Maintenance

### PostgreSQL
```sql
-- Update statistics for the query planner
ANALYZE orders;
ANALYZE;  -- All tables

-- Check table bloat and dead tuples
SELECT relname, n_dead_tup, last_autovacuum, last_autoanalyze
FROM pg_stat_user_tables ORDER BY n_dead_tup DESC;

-- Identify unused indexes
SELECT indexrelname, idx_scan, pg_size_pretty(pg_relation_size(indexrelid)) AS size
FROM pg_stat_user_indexes
WHERE idx_scan = 0 AND indexrelname NOT LIKE '%pkey%'
ORDER BY pg_relation_size(indexrelid) DESC;
```

### MySQL
```sql
-- Update statistics
ANALYZE TABLE orders;

-- Check index usage
SELECT * FROM sys.schema_unused_indexes;
SELECT * FROM sys.schema_redundant_indexes;

-- Identify long-running queries
SELECT * FROM information_schema.processlist WHERE time > 10;
```

---

## Performance Checklist

Before deploying any query to production:

1. Run `EXPLAIN ANALYZE` and verify no unexpected sequential scans
2. Check that estimated rows are within 10x of actual rows
3. Verify index usage on all WHERE, JOIN, and ORDER BY columns
4. Ensure LIMIT is present for user-facing list queries
5. Confirm parameterized queries (no string concatenation)
6. Test with production-like data volume (not just 10 rows)
7. Monitor query time in application metrics after deployment
8. Set up slow query log alerting (> 100ms for OLTP, > 5s for reports)

---

## Quick Reference: When to Use Which Index

| Query Pattern | Index Type |
|--------------|-----------|
| `WHERE col = value` | B-tree or Hash |
| `WHERE col > value` | B-tree |
| `WHERE col LIKE 'prefix%'` | B-tree |
| `WHERE col LIKE '%substring%'` | GIN (full-text) or trigram |
| `WHERE jsonb_col @> '{...}'` | GIN |
| `WHERE array_col && ARRAY[...]` | GIN |
| `WHERE range_col && '[a,b]'` | GiST |
| `WHERE ST_DWithin(geom, ...)` | GiST |
| `WHERE col = value` (append-only) | BRIN |
| `WHERE col = value AND status = 'active'` | Partial B-tree |
| `SELECT a, b WHERE c = value` | Covering (INCLUDE) |
