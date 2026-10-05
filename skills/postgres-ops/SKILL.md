---
name: postgres-ops
description: Operational PostgreSQL workflows for production environments — diagnosing slow queries, lock contention, bloat, replication lag, and connection-pool exhaustion; designing and reviewing backups (pg_dump, pg_basebackup, PITR via WAL archiving); planning upgrades and major-version migrations; configuring pgBouncer/RDS Proxy/PgCat; tuning postgresql.conf for OLTP and analytics workloads; writing and reviewing schema migrations across EF Core, Alembic, Flyway, and raw SQL; setting up observability with postgres_exporter to Prometheus, log shipping to Loki, and slow-query alerting; hardening for DoD/federal use (STIG, role separation, RLS, pgaudit, TLS). Use this skill whenever the user mentions Postgres, PostgreSQL, pg_, EXPLAIN ANALYZE, autovacuum, pgBouncer, replication lag, schema migrations, or anything involving a Postgres incident, performance problem, upgrade, backup, or compliance audit — even if they don't say "Postgres" explicitly but the context is clearly a relational database on PostgreSQL. Do NOT use for greenfield CRUD scaffolding — use nextjs-react-postgres-builder for that.
---

# postgres-ops

Production-grade PostgreSQL operations: diagnosis, performance, HA/DR, security, and observability. Assume the user is a senior engineer — skip introductory explanations of what Postgres is and go straight to evidence-driven SRE workflow.

## When to use

Trigger on operational Postgres tasks:

- **Incident diagnosis**: slow queries, deadlocks, lock waits, runaway autovacuum, connection exhaustion, replication lag, disk pressure, OOMs.
- **Performance review**: `EXPLAIN (ANALYZE, BUFFERS, VERBOSE)` interpretation, index strategy, partitioning, vacuum/autovacuum tuning, `work_mem` / `shared_buffers` sizing.
- **HA/DR**: streaming replication, logical replication, Patroni, pgBackRest, WAL-G, PITR planning, RTO/RPO target validation.
- **Migrations & upgrades**: minor and major version upgrades (pg_upgrade vs logical replication cutover), schema migration tooling (EF Core migrations, Alembic, Flyway, sqitch, raw SQL), zero-downtime patterns.
- **Connection management**: pgBouncer (transaction vs session pooling tradeoffs), RDS Proxy, PgCat, pool sizing math.
- **Security & compliance**: role design, RLS, pgaudit, TLS enforcement, secret rotation, STIG/SRG line items, CIS benchmark gaps.
- **Observability**: postgres_exporter, pg_stat_statements, auto_explain, slow query log shipping (Loki), Grafana dashboards, SLO definition.

Do NOT trigger for:
- New-feature CRUD scaffolding in Next.js (use `nextjs-react-postgres-builder`).
- Pure SQL-language questions ("what does LATERAL do") with no operational context.
- Other database engines (MySQL, SQL Server, Cosmos DB).

## Instructions

### 1. Diagnose like an SRE

For any incident or performance complaint, follow hypothesis → evidence → fix → verification. Never propose a fix without naming the query you'd run to confirm the diagnosis first.

Default first-look queries:

```sql
-- Active sessions and what they're waiting on
SELECT pid, usename, application_name, state, wait_event_type, wait_event,
       now() - query_start AS runtime, left(query, 200) AS query
FROM pg_stat_activity
WHERE state <> 'idle'
ORDER BY runtime DESC NULLS LAST;

-- Blocking chains
SELECT blocked.pid AS blocked_pid, blocked.query AS blocked_query,
       blocking.pid AS blocking_pid, blocking.query AS blocking_query
FROM pg_stat_activity blocked
JOIN pg_stat_activity blocking ON blocking.pid = ANY(pg_blocking_pids(blocked.pid));

-- Top queries by total time (requires pg_stat_statements)
SELECT round(total_exec_time::numeric, 0) AS total_ms,
       calls, round(mean_exec_time::numeric, 2) AS mean_ms,
       round((100 * total_exec_time / sum(total_exec_time) OVER ())::numeric, 1) AS pct,
       left(query, 200) AS query
FROM pg_stat_statements
ORDER BY total_exec_time DESC LIMIT 20;

-- Bloat / vacuum status
SELECT schemaname, relname, n_live_tup, n_dead_tup,
       round(100.0 * n_dead_tup / NULLIF(n_live_tup + n_dead_tup, 0), 1) AS dead_pct,
       last_vacuum, last_autovacuum, last_analyze, last_autoanalyze
FROM pg_stat_user_tables
WHERE n_dead_tup > 1000
ORDER BY dead_pct DESC NULLS LAST;

-- Replication lag (on primary)
SELECT client_addr, state, sync_state,
       pg_wal_lsn_diff(pg_current_wal_lsn(), sent_lsn) AS sent_lag_bytes,
       pg_wal_lsn_diff(pg_current_wal_lsn(), replay_lsn) AS replay_lag_bytes,
       write_lag, flush_lag, replay_lag
FROM pg_stat_replication;
```

### 2. Read query plans rigorously

When given an `EXPLAIN ANALYZE` output:
1. Identify row-estimate vs actual mismatch (>10x = stale stats or bad correlation).
2. Find the dominant cost node (Seq Scan on large table, nested loop with high outer rows, sort spilling to disk).
3. Check buffer numbers — heavy `read=` vs `hit=` indicates cold cache or undersized `shared_buffers`.
4. Recommend: index, query rewrite, statistics target bump, or partitioning — in that order of preference.
5. Always provide the verification command (re-run with same params and compare).

### 3. Migration & upgrade discipline

For schema migrations:
- Always show forward and rollback DDL.
- Flag any `ALTER TABLE` that rewrites the table (changing column type, adding NOT NULL without DEFAULT on PG <11, etc.).
- For zero-downtime: use the expand-contract pattern (add nullable → backfill → enforce → drop).
- For EF Core: use `Add-Migration` + `Script-Migration` to review SQL before apply; never `Update-Database` in prod.

For version upgrades:
- pg_upgrade with `--link` for in-place when downtime is acceptable.
- Logical replication cutover (pglogical or built-in) for near-zero downtime.
- Always confirm extension compatibility on the target version first.

### 4. Connection pooling math

For pgBouncer in transaction-pooling mode:
- `default_pool_size` per (user, database) ≈ `max_connections / number_of_pools` with headroom.
- App-side pool: keep small (5–20 per replica). The pooler is the real concurrency limit.
- Watch out for: prepared statements (need `pgbouncer >= 1.21` with `server_lifetime` tuning), session-level features (`SET LOCAL` only, no `LISTEN/NOTIFY`, no temp tables across txns).

### 5. Federal/DoD posture (when relevant)

- Enforce TLS with `ssl=on`, `ssl_min_protocol_version=TLSv1.2`, restrict `hostssl` only in `pg_hba.conf`.
- `pgaudit` extension for STIG-required audit logging; ship logs to a tamper-resistant store.
- Separate roles: no shared accounts, no `SUPERUSER` for app roles, RLS for tenant isolation.
- FIPS-validated OpenSSL on the host; verify with `SHOW ssl_library;` and OS-level FIPS mode.
- Check the current PostgreSQL STIG (DISA) for line-item compliance — versions ship updates regularly.

### 6. Observability defaults

- Enable `pg_stat_statements`, `auto_explain` (with `log_min_duration_statement` reasonable for prod, e.g., 1000ms).
- Run `postgres_exporter` as a sidecar; scrape into Prometheus.
- Ship CSV logs to Loki via Promtail or Vector; Grafana dashboards keyed on `pg_stat_statements` and `pg_stat_activity`.
- SLO suggestion: P95 query latency for the top-N statements, plus replication lag <N seconds.

### 7. Output discipline

- Give complete, runnable SQL or shell — no placeholders.
- Call out destructive operations explicitly (`DROP`, `TRUNCATE`, `pg_upgrade --link`, `vacuum full`).
- For any tuning parameter recommendation, state the workload assumption (OLTP / analytics / mixed) and the math behind it.
- When uncertain about a version-specific behavior, say so and name the version where the behavior changed.

## Example prompts

- *"We have a query taking 30 seconds in prod. Here's the EXPLAIN ANALYZE — what's wrong?"*
- *"Our app hit max_connections. Walk me through diagnosing the cause and fixing it without downtime."*
- *"I need to add a NOT NULL column to a 200M-row table. What's the zero-downtime approach?"*
- *"We're upgrading from Postgres 14 to 16. What's the fastest path and what should I check first?"*
- *"Help me size pgBouncer pool for 50 app instances hitting a single primary."*
- *"Our DISA STIG audit is next week. What Postgres controls do I need in place?"*
- *"Autovacuum is running constantly on one table. How do I tune it?"*

## Related skills

- [`k8s-nextjs-deploy`](./k8s-nextjs-deploy/SKILL.md) — Kubernetes deployment patterns if Postgres runs in-cluster
- [`ubuntu24-stig`](./ubuntu24-stig/SKILL.md) — OS-level STIG hardening for the host running Postgres
