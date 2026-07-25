# Snowflake Troubleshooting Reference

Common errors, debugging queries, and resolution patterns for Snowflake development.

## Table of Contents

1. [Error Reference](#error-reference)
2. [Debugging Queries](#debugging-queries)
3. [Performance Diagnostics](#performance-diagnostics)

---

## Error Reference

### SQL Errors

| Error | Cause | Fix |
|-------|-------|-----|
| "Object 'X' does not exist or not authorized" | Wrong database/schema context, missing grants, or typo | Fully qualify: `db.schema.table`. Check `SHOW GRANTS ON TABLE`. |
| "Invalid identifier 'VAR'" in procedure | Missing colon prefix on variable in SQL procedure | Use `:var_name` inside SELECT/INSERT/UPDATE/DELETE/MERGE |
| "Numeric value 'X' is not recognized" | VARIANT field accessed without type cast | Always cast: `src:field::NUMBER(10,2)` |
| "SQL compilation error: ambiguous column name" | Same column name in multiple joined tables | Use table aliases: `t.id`, `s.id` |
| "Number of columns in insert does not match" | INSERT column count mismatch with VALUES | Verify column list matches value list exactly |
| "Division by zero" | Dividing by a column that contains 0 | Use `NULLIF(divisor, 0)` or `IFF(divisor = 0, NULL, ...)` |

### Pipeline Errors

| Error | Cause | Fix |
|-------|-------|-----|
| Task not running | Created but not resumed | `ALTER TASK task_name RESUME;` |
| DT stuck in FAILED state | Query error or upstream dependency issue | Check `DYNAMIC_TABLE_REFRESH_HISTORY()` for error messages |
| DT shows full refresh instead of incremental | Non-deterministic function or unsupported pattern | Check `refresh_mode_reason` in `INFORMATION_SCHEMA.DYNAMIC_TABLES()` |
| Stream shows no data | Stream was consumed or table was recreated | Verify stream is on the correct table, check `STALE_AFTER` |
| Snowpipe not loading files | SQS notification misconfigured or file format mismatch | Check `SYSTEM$PIPE_STATUS()`, verify notification channel |
| "UPSTREAM_FAILED" on DT | A DT dependency upstream has a refresh failure | Fix the upstream DT first, then downstream will recover |

### Cortex AI Errors

| Error | Cause | Fix |
|-------|-------|-----|
| "Function X does not exist" | Using deprecated function name | Use new `AI_*` names (e.g., `AI_CLASSIFY` not `CLASSIFY_TEXT`) |
| TO_FILE error | Single argument instead of two | `TO_FILE('@stage', 'file.pdf')` -- two separate arguments |
| Agent returns empty or wrong results | Poor tool descriptions or wrong semantic model | Improve tool descriptions, verify semantic model covers the question |
| "Invalid specification" on agent | JSON structure error in spec | Check: `models` is object not array, `tool_resources` is top-level, no trailing commas |

---

## Debugging Queries

### Query History

```sql
-- Find slow queries in the last 24 hours
SELECT query_id, query_text, execution_status,
       total_elapsed_time / 1000 AS elapsed_sec,
       bytes_scanned / (1024*1024*1024) AS gb_scanned,
       rows_produced, warehouse_name
FROM TABLE(INFORMATION_SCHEMA.QUERY_HISTORY(
    END_TIME_RANGE_START => DATEADD(HOUR, -24, CURRENT_TIMESTAMP()),
    RESULT_LIMIT => 50
))
WHERE total_elapsed_time > 30000  -- > 30 seconds
ORDER BY total_elapsed_time DESC;
```

### Dynamic Table Health

```sql
-- Overall DT status
SELECT name, scheduling_state, last_completed_refresh_state,
       data_timestamp,
       DATEDIFF('minute', data_timestamp, CURRENT_TIMESTAMP()) AS lag_minutes
FROM TABLE(INFORMATION_SCHEMA.DYNAMIC_TABLES())
ORDER BY lag_minutes DESC;

-- Recent failures
SELECT name, state, state_message, refresh_trigger,
       DATEDIFF('second', refresh_start_time, refresh_end_time) AS duration_sec
FROM TABLE(INFORMATION_SCHEMA.DYNAMIC_TABLE_REFRESH_HISTORY())
WHERE state = 'FAILED'
ORDER BY refresh_end_time DESC
LIMIT 20;
```

### Stream Status

```sql
-- Check stream freshness
SHOW STREAMS;

-- Check if stream has data
SELECT SYSTEM$STREAM_HAS_DATA('my_stream');
```

### Task Monitoring

```sql
-- Check task run history
SELECT name, state, error_message,
       scheduled_time, completed_time,
       DATEDIFF('second', scheduled_time, completed_time) AS duration_sec
FROM TABLE(INFORMATION_SCHEMA.TASK_HISTORY())
WHERE name = 'MY_TASK'
ORDER BY scheduled_time DESC
LIMIT 20;
```

### Grants Debugging

```sql
-- What grants does a role have?
SHOW GRANTS TO ROLE my_role;

-- What grants exist on an object?
SHOW GRANTS ON TABLE my_db.my_schema.my_table;

-- Who has ACCOUNTADMIN?
SHOW GRANTS OF ROLE ACCOUNTADMIN;
```

---

## Performance Diagnostics

### Warehouse Utilization

```sql
-- Warehouse load over time
SELECT start_time, warehouse_name,
       avg_running, avg_queued_load, avg_blocked
FROM TABLE(INFORMATION_SCHEMA.WAREHOUSE_LOAD_HISTORY(
    DATE_RANGE_START => DATEADD(HOUR, -24, CURRENT_TIMESTAMP())
))
WHERE warehouse_name = 'MY_WH'
ORDER BY start_time DESC;
```

### Clustering Health

```sql
-- Check clustering depth (lower is better)
SELECT SYSTEM$CLUSTERING_INFORMATION('my_table', '(date_col, region)');
```

### Storage Costs

```sql
-- Table storage usage
SELECT table_name, active_bytes / (1024*1024*1024) AS active_gb,
       time_travel_bytes / (1024*1024*1024) AS time_travel_gb,
       failsafe_bytes / (1024*1024*1024) AS failsafe_gb
FROM INFORMATION_SCHEMA.TABLE_STORAGE_METRICS
WHERE table_schema = 'MY_SCHEMA'
ORDER BY active_bytes DESC;
```
