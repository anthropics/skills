# Snowflake SQL and Pipelines Reference

Detailed patterns and anti-patterns for Snowflake SQL development and data pipeline design.

## Table of Contents

1. [SQL Patterns](#sql-patterns)
2. [Dynamic Table Deep Dive](#dynamic-table-deep-dive)
3. [Streams and Tasks Patterns](#streams-and-tasks-patterns)
4. [Snowpipe](#snowpipe)
5. [Anti-Patterns](#anti-patterns)

---

## SQL Patterns

### CTE-Based Transformations

```sql
WITH raw AS (
    SELECT * FROM raw_events WHERE event_date = CURRENT_DATE()
),
cleaned AS (
    SELECT
        event_id,
        TRIM(LOWER(event_type)) AS event_type,
        user_id,
        event_timestamp,
        src:metadata::VARIANT AS metadata
    FROM raw
    WHERE event_type IS NOT NULL
),
enriched AS (
    SELECT
        c.*,
        u.name AS user_name,
        u.segment
    FROM cleaned c
    JOIN dim_users u ON c.user_id = u.user_id
)
SELECT * FROM enriched;
```

### MERGE with Multiple Match Conditions

```sql
MERGE INTO dim_customers t
USING (
    SELECT customer_id, name, email, updated_at,
           ROW_NUMBER() OVER (PARTITION BY customer_id ORDER BY updated_at DESC) AS rn
    FROM staging_customers
) s
ON t.customer_id = s.customer_id AND s.rn = 1
WHEN MATCHED AND s.updated_at > t.updated_at THEN
    UPDATE SET t.name = s.name, t.email = s.email, t.updated_at = s.updated_at
WHEN NOT MATCHED THEN
    INSERT (customer_id, name, email, updated_at)
    VALUES (s.customer_id, s.name, s.email, s.updated_at);
```

### Semi-Structured Data Patterns

**Flatten nested arrays:**
```sql
SELECT
    o.order_id,
    f.value:product_id::STRING AS product_id,
    f.value:quantity::NUMBER AS quantity,
    f.value:price::NUMBER(10,2) AS price
FROM orders o,
LATERAL FLATTEN(input => o.line_items) f;
```

**Nested flatten (array of arrays):**
```sql
SELECT
    f1.value:category::STRING AS category,
    f2.value:tag::STRING AS tag
FROM catalog,
LATERAL FLATTEN(input => data:categories) f1,
LATERAL FLATTEN(input => f1.value:tags) f2;
```

**OBJECT_CONSTRUCT for building JSON:**
```sql
SELECT OBJECT_CONSTRUCT(
    'id', customer_id,
    'name', name,
    'orders', ARRAY_AGG(OBJECT_CONSTRUCT('order_id', order_id, 'total', total))
) AS customer_json
FROM customers c JOIN orders o ON c.customer_id = o.customer_id
GROUP BY c.customer_id, c.name;
```

### Window Functions

```sql
-- Running total with partitions
SELECT
    department,
    employee,
    salary,
    SUM(salary) OVER (PARTITION BY department ORDER BY hire_date) AS dept_running_total
FROM employees;

-- Detect gaps in sequences
SELECT id, seq_num,
    seq_num - LAG(seq_num) OVER (ORDER BY seq_num) AS gap
FROM records
HAVING gap > 1;
```

### Time Travel

```sql
-- Query data as of a specific timestamp
SELECT * FROM my_table AT(TIMESTAMP => '2026-03-20 10:00:00'::TIMESTAMP);

-- Query data before a specific statement
SELECT * FROM my_table BEFORE(STATEMENT => '<query_id>');

-- Restore a dropped table
UNDROP TABLE accidentally_dropped_table;
```

Default retention: 1 day (standard edition), up to 90 days (enterprise+). Set per table: `DATA_RETENTION_TIME_IN_DAYS = 7`.

---

## Dynamic Table Deep Dive

### TARGET_LAG Strategy

Design your DT DAG with progressive lag -- tighter upstream, looser downstream:

```
raw_events (base table)
    |
    v
cleaned_events (DT, TARGET_LAG = '1 minute')
    |
    v
enriched_events (DT, TARGET_LAG = '5 minutes')
    |
    v
daily_aggregates (DT, TARGET_LAG = '1 hour')
```

### Refresh Mode Rules

| Refresh Mode | Condition |
|-------------|-----------|
| Incremental | DTs with simple SELECT, JOIN, WHERE, GROUP BY, UNION ALL on change-tracked sources |
| Full | DTs using non-deterministic functions, LIMIT, or depending on full-refresh DTs |

**Check refresh mode:**
```sql
SELECT name, refresh_mode, refresh_mode_reason
FROM TABLE(INFORMATION_SCHEMA.DYNAMIC_TABLES())
WHERE name = 'MY_DT';
```

### DT Debugging Queries

```sql
-- Check DT health and lag
SELECT name, scheduling_state, last_completed_refresh_state,
       data_timestamp, DATEDIFF('minute', data_timestamp, CURRENT_TIMESTAMP()) AS lag_minutes
FROM TABLE(INFORMATION_SCHEMA.DYNAMIC_TABLES());

-- Check refresh history for failures
SELECT name, state, state_message, refresh_trigger
FROM TABLE(INFORMATION_SCHEMA.DYNAMIC_TABLE_REFRESH_HISTORY())
WHERE state = 'FAILED'
ORDER BY refresh_end_time DESC
LIMIT 10;

-- Examine graph dependencies
SELECT name, qualified_name, refresh_mode
FROM TABLE(INFORMATION_SCHEMA.DYNAMIC_TABLE_GRAPH_HISTORY());
```

### DT Constraints

- No views between two DTs in the DAG.
- `SELECT *` breaks on upstream schema changes.
- Cannot use non-deterministic functions (e.g., `CURRENT_TIMESTAMP()`) -- use a column from the source instead.
- Change tracking must be enabled on source tables: `ALTER TABLE src SET CHANGE_TRACKING = TRUE;`

---

## Streams and Tasks Patterns

### Task Trees (Parent-Child)

```sql
CREATE OR REPLACE TASK parent_task
    WAREHOUSE = transform_wh
    SCHEDULE = 'USING CRON 0 */1 * * * America/Los_Angeles'
    AS CALL process_stage_1();

CREATE OR REPLACE TASK child_task
    WAREHOUSE = transform_wh
    AFTER parent_task
    AS CALL process_stage_2();

-- Resume in reverse order: children first, then parent
ALTER TASK child_task RESUME;
ALTER TASK parent_task RESUME;
```

### Stream Types

| Stream Type | Use Case |
|------------|----------|
| Standard (default) | Track all DML changes (INSERT, UPDATE, DELETE) |
| Append-only | Only track INSERTs. More efficient for insert-heavy tables. |
| Insert-only (external tables) | Track new files loaded via external tables. |

```sql
-- Append-only stream for event log tables
CREATE STREAM event_stream ON TABLE events APPEND_ONLY = TRUE;
```

### Serverless Tasks

```sql
-- No warehouse needed. Snowflake manages compute automatically.
CREATE OR REPLACE TASK lightweight_task
    USER_TASK_MANAGED_INITIAL_WAREHOUSE_SIZE = 'XSMALL'
    SCHEDULE = '5 MINUTE'
    AS INSERT INTO audit_log SELECT CURRENT_TIMESTAMP(), 'heartbeat';
```

---

## Snowpipe

### Auto-Ingest Setup (S3)

```sql
CREATE OR REPLACE PIPE my_pipe
    AUTO_INGEST = TRUE
    AS COPY INTO raw_table
    FROM @my_s3_stage
    FILE_FORMAT = (TYPE = 'JSON', STRIP_NULL_VALUES = TRUE);
```

Configure the S3 event notification to point to the pipe's SQS queue:
```sql
SHOW PIPES LIKE 'my_pipe';
-- Use the notification_channel value for S3 event config
```

### Snowpipe Monitoring

```sql
-- Check pipe status
SELECT SYSTEM$PIPE_STATUS('my_pipe');

-- Recent load history
SELECT * FROM TABLE(INFORMATION_SCHEMA.COPY_HISTORY(
    TABLE_NAME => 'raw_table',
    START_TIME => DATEADD(HOUR, -24, CURRENT_TIMESTAMP())
));
```

---

## Anti-Patterns

| Anti-Pattern | Why It's Bad | Fix |
|-------------|-------------|-----|
| `SELECT *` in production | Scans all columns, breaks on schema changes | Explicit column list |
| Double-quoted identifiers | Creates case-sensitive names requiring constant quoting | Use `snake_case` without quotes |
| `ORDER BY` without `LIMIT` | Sorts entire result set for no reason | Add `LIMIT` or remove `ORDER BY` |
| Single warehouse for everything | Workloads compete for resources | Separate warehouses per workload |
| `FLOAT` for money | Rounding errors | `NUMBER(19,4)` or integer cents |
| Missing `RESUME` after task creation | Task never runs | Always `ALTER TASK ... RESUME` |
| `CURRENT_TIMESTAMP()` in DT query | Forces full refresh mode | Use a timestamp column from the source |
| Scanning VARIANT without casting | "Numeric value not recognized" errors | Always cast: `col:field::TYPE` |
