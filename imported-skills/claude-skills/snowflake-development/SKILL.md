---
name: "snowflake-development"
description: "Use when writing Snowflake SQL, building data pipelines with Dynamic Tables or Streams/Tasks, using Cortex AI functions, creating Cortex Agents, writing Snowpark Python, configuring dbt for Snowflake, or troubleshooting Snowflake errors."
---

# Snowflake Development

Snowflake SQL, data pipelines, Cortex AI, and Snowpark Python development. Covers the colon-prefix rule, semi-structured data, MERGE upserts, Dynamic Tables, Streams+Tasks, Cortex AI functions, agent specs, performance tuning, and security hardening.

> Originally contributed by [James Cha-Earley](https://github.com/jamescha-earley) — enhanced and integrated by the claude-skills team.

## Quick Start

```bash
# Generate a MERGE upsert template
python scripts/snowflake_query_helper.py merge --target customers --source staging_customers --key customer_id --columns name,email,updated_at

# Generate a Dynamic Table template
python scripts/snowflake_query_helper.py dynamic-table --name cleaned_events --warehouse transform_wh --lag "5 minutes"

# Generate RBAC grant statements
python scripts/snowflake_query_helper.py grant --role analyst_role --database analytics --schemas public,staging --privileges SELECT,USAGE
```

---

## SQL Best Practices

### Naming and Style

- Use `snake_case` for all identifiers. Avoid double-quoted identifiers -- they force case-sensitive names that require constant quoting.
- Use CTEs (`WITH` clauses) over nested subqueries.
- Use `CREATE OR REPLACE` for idempotent DDL.
- Use explicit column lists -- never `SELECT *` in production. Snowflake's columnar storage scans only referenced columns, so explicit lists reduce I/O.

### Stored Procedures -- Colon Prefix Rule

In SQL stored procedures (BEGIN...END blocks), variables and parameters **must** use the colon `:` prefix inside SQL statements. Without it, Snowflake treats them as column identifiers and raises "invalid identifier" errors.

```sql
-- WRONG: missing colon prefix
SELECT name INTO result FROM users WHERE id = p_id;

-- CORRECT: colon prefix on both variable and parameter
SELECT name INTO :result FROM users WHERE id = :p_id;
```

This applies to DECLARE variables, LET variables, and procedure parameters when used inside SELECT, INSERT, UPDATE, DELETE, or MERGE.

### Semi-Structured Data

- VARIANT, OBJECT, ARRAY for JSON/Avro/Parquet/ORC.
- Access nested fields: `src:customer.name::STRING`. Always cast with `::TYPE`.
- VARIANT null vs SQL NULL: JSON `null` is stored as the string `"null"`. Use `STRIP_NULL_VALUE = TRUE` on load.
- Flatten arrays: `SELECT f.value:name::STRING FROM my_table, LATERAL FLATTEN(input => src:items) f;`

### MERGE for Upserts

```sql
MERGE INTO target t USING source s ON t.id = s.id
WHEN MATCHED THEN UPDATE SET t.name = s.name, t.updated_at = CURRENT_TIMESTAMP()
WHEN NOT MATCHED THEN INSERT (id, name, updated_at) VALUES (s.id, s.name, CURRENT_TIMESTAMP());
```

> See `references/snowflake_sql_and_pipelines.md` for deeper SQL patterns and anti-patterns.

---

## Data Pipelines

### Choosing Your Approach

| Approach | When to Use |
|----------|-------------|
| Dynamic Tables | Declarative transformations. **Default choice.** Define the query, Snowflake handles refresh. |
| Streams + Tasks | Imperative CDC. Use for procedural logic, stored procedure calls, complex branching. |
| Snowpipe | Continuous file loading from cloud storage (S3, GCS, Azure). |

### Dynamic Tables

```sql
CREATE OR REPLACE DYNAMIC TABLE cleaned_events
    TARGET_LAG = '5 minutes'
    WAREHOUSE = transform_wh
    AS
    SELECT event_id, event_type, user_id, event_timestamp
    FROM raw_events
    WHERE event_type IS NOT NULL;
```

Key rules:
- Set `TARGET_LAG` progressively: tighter at the top of the DAG, looser downstream.
- Incremental DTs cannot depend on Full-refresh DTs.
- `SELECT *` breaks on upstream schema changes -- use explicit column lists.
- Views cannot sit between two Dynamic Tables in the DAG.

### Streams and Tasks

```sql
CREATE OR REPLACE STREAM raw_stream ON TABLE raw_events;

CREATE OR REPLACE TASK process_events
    WAREHOUSE = transform_wh
    SCHEDULE = 'USING CRON 0 */1 * * * America/Los_Angeles'
    WHEN SYSTEM$STREAM_HAS_DATA('raw_stream')
    AS INSERT INTO cleaned_events SELECT ... FROM raw_stream;

-- Tasks start SUSPENDED. You MUST resume them.
ALTER TASK process_events RESUME;
```

> See `references/snowflake_sql_and_pipelines.md` for DT debugging queries and Snowpipe patterns.

---

## Cortex AI

### Function Reference

| Function | Purpose |
|----------|---------|
| `AI_COMPLETE` | LLM completion (text, images, documents) |
| `AI_CLASSIFY` | Classify text into categories (up to 500 labels) |
| `AI_FILTER` | Boolean filter on text or images |
| `AI_EXTRACT` | Structured extraction from text/images/documents |
| `AI_SENTIMENT` | Sentiment score (-1 to 1) |
| `AI_PARSE_DOCUMENT` | OCR or layout extraction from documents |
| `AI_REDACT` | PII removal from text |

**Deprecated names (do NOT use):** `COMPLETE`, `CLASSIFY_TEXT`, `EXTRACT_ANSWER`, `PARSE_DOCUMENT`, `SUMMARIZE`, `TRANSLATE`, `SENTIMENT`, `EMBED_TEXT_768`.

### TO_FILE -- Common Pitfall

Stage path and filename are **separate** arguments:

```sql
-- WRONG: single combined argument
TO_FILE('@stage/file.pdf')

-- CORRECT: two arguments
TO_FILE('@db.schema.mystage', 'invoice.pdf')
```

### Cortex Agents

Agent specs use a JSON structure with top-level keys: `models`, `instructions`, `tools`, `tool_resources`.

- Use `$spec$` delimiter (not `$$`).
- `models` must be an object, not an array.
- `tool_resources` is a separate top-level key, not nested inside `tools`.
- Tool descriptions are the single biggest factor in agent quality.

> See `references/cortex_ai_and_agents.md` for full agent spec examples and Cortex Search patterns.

---

## Snowpark Python

```python
from snowflake.snowpark import Session
import os

session = Session.builder.configs({
    "account": os.environ["SNOWFLAKE_ACCOUNT"],
    "user": os.environ["SNOWFLAKE_USER"],
    "password": os.environ["SNOWFLAKE_PASSWORD"],
    "role": "my_role", "warehouse": "my_wh",
    "database": "my_db", "schema": "my_schema"
}).create()
```

- Never hardcode credentials. Use environment variables or key pair auth.
- DataFrames are lazy -- executed on `collect()` / `show()`.
- Do NOT call `collect()` on large DataFrames. Process server-side with DataFrame operations.
- Use **vectorized UDFs** (10-100x faster) for batch and ML workloads.

## dbt on Snowflake

```sql
-- Dynamic table materialization (streaming/near-real-time marts):
{{ config(materialized='dynamic_table', snowflake_warehouse='transforming', target_lag='1 hour') }}

-- Incremental materialization (large fact tables):
{{ config(materialized='incremental', unique_key='event_id') }}

-- Snowflake-specific configs (combine with any materialization):
{{ config(transient=true, copy_grants=true, query_tag='team_daily') }}
```

- Do NOT use `{{ this }}` without `{% if is_incremental() %}` guard.
- Use `dynamic_table` materialization for streaming or near-real-time marts.

## Performance

- **Cluster keys**: Only for multi-TB tables. Apply on WHERE / JOIN / GROUP BY columns.
- **Search Optimization**: `ALTER TABLE t ADD SEARCH OPTIMIZATION ON EQUALITY(col);`
- **Warehouse sizing**: Start X-Small, scale up. Set `AUTO_SUSPEND = 60`, `AUTO_RESUME = TRUE`.
- **Separate warehouses** per workload (load, transform, query).

## Security

- Follow least-privilege RBAC. Use database roles for object-level grants.
- Audit ACCOUNTADMIN regularly: `SHOW GRANTS OF ROLE ACCOUNTADMIN;`
- Use network policies for IP allowlisting.
- Use masking policies for PII columns and row access policies for multi-tenant isolation.

---

## Proactive Triggers

Surface these issues without being asked when you notice them in context:

- **Missing colon prefix** in SQL stored procedures -- flag immediately, this causes "invalid identifier" at runtime.
- **`SELECT *` in Dynamic Tables** -- flag as a schema-change time bomb.
- **Deprecated Cortex function names** (`CLASSIFY_TEXT`, `SUMMARIZE`, etc.) -- suggest the current `AI_*` equivalents.
- **Task not resumed** after creation -- remind that tasks start SUSPENDED.
- **Hardcoded credentials** in Snowpark code -- flag as a security risk.

---

## Common Errors

| Error | Cause | Fix |
|-------|-------|-----|
| "Object does not exist" | Wrong database/schema context or missing grants | Fully qualify names (`db.schema.table`), check grants |
| "Invalid identifier" in procedure | Missing colon prefix on variable | Use `:variable_name` inside SQL statements |
| "Numeric value not recognized" | VARIANT field not cast | Cast explicitly: `src:field::NUMBER(10,2)` |
| Task not running | Forgot to resume after creation | `ALTER TASK task_name RESUME;` |
| DT refresh failing | Schema change upstream or tracking disabled | Use explicit columns, verify change tracking |
| TO_FILE error | Combined path as single argument | Split into two args: `TO_FILE('@stage', 'file.pdf')` |

---

## Practical Workflows

### Workflow 1: Build a Reporting Pipeline (30 min)

1. **Stage raw data**: Create external stage pointing to S3/GCS/Azure, set up Snowpipe for auto-ingest
2. **Clean with Dynamic Table**: Create DT with `TARGET_LAG = '5 minutes'` that filters nulls, casts types, deduplicates
3. **Aggregate with downstream DT**: Second DT that joins cleaned data with dimension tables, computes metrics
4. **Expose via Secure View**: Create `SECURE VIEW` for the BI tool / API layer
5. **Grant access**: Use `snowflake_query_helper.py grant` to generate RBAC statements

### Workflow 2: Add AI Classification to Existing Data

1. **Identify the column**: Find the text column to classify (e.g., support tickets, reviews)
2. **Test with AI_CLASSIFY**: `SELECT AI_CLASSIFY(text_col, ['bug', 'feature', 'question']) FROM table LIMIT 10;`
3. **Create enrichment DT**: Dynamic Table that runs `AI_CLASSIFY` on new rows automatically
4. **Monitor costs**: Cortex AI is billed per token — sample before running on full tables

### Workflow 3: Debug a Failing Pipeline

1. **Check task history**: `SELECT * FROM TABLE(INFORMATION_SCHEMA.TASK_HISTORY()) WHERE STATE = 'FAILED' ORDER BY SCHEDULED_TIME DESC;`
2. **Check DT refresh**: `SELECT * FROM TABLE(INFORMATION_SCHEMA.DYNAMIC_TABLE_REFRESH_HISTORY('my_dt')) ORDER BY REFRESH_END_TIME DESC;`
3. **Check stream staleness**: `SHOW STREAMS; -- check stale_after column`
4. **Consult troubleshooting reference**: See `references/troubleshooting.md` for error-specific fixes

---

## Anti-Patterns

| Anti-Pattern | Why It Fails | Better Approach |
|---|---|---|
| `SELECT *` in Dynamic Tables | Schema changes upstream break the DT silently | Use explicit column lists |
| Missing colon prefix in procedures | "Invalid identifier" runtime error | Always use `:variable_name` in SQL blocks |
| Single warehouse for all workloads | Contention between load, transform, and query | Separate warehouses per workload type |
| Hardcoded credentials in Snowpark | Security risk, breaks in CI/CD | Use `os.environ[]` or key pair auth |
| `collect()` on large DataFrames | Pulls entire result set to client memory | Process server-side with DataFrame operations |
| Nested subqueries instead of CTEs | Unreadable, hard to debug, Snowflake optimizes CTEs better | Use `WITH` clauses |
| Using deprecated Cortex functions | `CLASSIFY_TEXT`, `SUMMARIZE` etc. will be removed | Use `AI_CLASSIFY`, `AI_COMPLETE` etc. |
| Tasks without `WHEN SYSTEM$STREAM_HAS_DATA` | Task runs on schedule even with no new data, wasting credits | Add the WHEN clause for stream-driven tasks |
| Double-quoted identifiers | Forces case-sensitive names across all queries | Use `snake_case` unquoted identifiers |

---

## Cross-References

| Skill | Relationship |
|-------|-------------|
| `engineering/sql-database-assistant` | General SQL patterns — use for non-Snowflake databases |
| `engineering/database-designer` | Schema design — use for data modeling before Snowflake implementation |
| `engineering-team/senior-data-engineer` | Broader data engineering — pipelines, Spark, Airflow, data quality |
| `engineering-team/senior-data-scientist` | Analytics and ML — use alongside Snowpark for feature engineering |
| `engineering-team/senior-devops` | CI/CD for Snowflake deployments (Terraform, GitHub Actions) |

---

## Reference Documentation

| Document | Contents |
|----------|----------|
| `references/snowflake_sql_and_pipelines.md` | SQL patterns, MERGE templates, Dynamic Table debugging, Snowpipe, anti-patterns |
| `references/cortex_ai_and_agents.md` | Cortex AI functions, agent spec structure, Cortex Search, Snowpark |
| `references/troubleshooting.md` | Error reference, debugging queries, common fixes |
