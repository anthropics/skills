# Cortex AI and Agents Reference

Complete reference for Snowflake Cortex AI functions, Cortex Agents, Cortex Search, and Snowpark Python patterns.

## Table of Contents

1. [Cortex AI Functions](#cortex-ai-functions)
2. [Cortex Agents](#cortex-agents)
3. [Cortex Search](#cortex-search)
4. [Snowpark Python](#snowpark-python)

---

## Cortex AI Functions

### Complete Function Reference

| Function | Signature | Returns |
|----------|-----------|---------|
| `AI_COMPLETE` | `AI_COMPLETE(model, prompt)` or `AI_COMPLETE(model, conversation, options)` | STRING or OBJECT |
| `AI_CLASSIFY` | `AI_CLASSIFY(input, categories)` | OBJECT with `labels` array |
| `AI_EXTRACT` | `AI_EXTRACT(input, fields)` | OBJECT with extracted fields |
| `AI_FILTER` | `AI_FILTER(input, condition)` | BOOLEAN |
| `AI_SENTIMENT` | `AI_SENTIMENT(text)` | FLOAT (-1 to 1) |
| `AI_SUMMARIZE` | `AI_SUMMARIZE(text)` | STRING |
| `AI_TRANSLATE` | `AI_TRANSLATE(text, source_lang, target_lang)` | STRING |
| `AI_PARSE_DOCUMENT` | `AI_PARSE_DOCUMENT(file, options)` | OBJECT |
| `AI_REDACT` | `AI_REDACT(text)` | STRING |
| `AI_EMBED` | `AI_EMBED(model, text)` | ARRAY (vector) |
| `AI_AGG` | `AI_AGG(column, instruction)` | STRING |

### Deprecated Function Mapping

| Old Name (Do NOT Use) | New Name |
|-----------------------|----------|
| `COMPLETE` | `AI_COMPLETE` |
| `CLASSIFY_TEXT` | `AI_CLASSIFY` |
| `EXTRACT_ANSWER` | `AI_EXTRACT` |
| `SUMMARIZE` | `AI_SUMMARIZE` |
| `TRANSLATE` | `AI_TRANSLATE` |
| `SENTIMENT` | `AI_SENTIMENT` |
| `EMBED_TEXT_768` | `AI_EMBED` |

### AI_COMPLETE Patterns

**Simple completion:**
```sql
SELECT AI_COMPLETE('claude-4-sonnet', 'Summarize this text: ' || article_text) AS summary
FROM articles;
```

**With system prompt (conversation format):**
```sql
SELECT AI_COMPLETE(
    'claude-4-sonnet',
    [
        {'role': 'system', 'content': 'You are a data quality analyst. Be concise.'},
        {'role': 'user', 'content': 'Analyze this record: ' || record::STRING}
    ]
) AS analysis
FROM flagged_records;
```

**With document input (TO_FILE):**
```sql
SELECT AI_COMPLETE(
    'claude-4-sonnet',
    'Extract the invoice total from this document',
    TO_FILE('@docs_stage', 'invoice.pdf')
) AS invoice_total;
```

### AI_CLASSIFY Patterns

Use AI_CLASSIFY instead of AI_COMPLETE for classification tasks -- it is purpose-built, cheaper, and returns structured output.

```sql
SELECT
    ticket_text,
    AI_CLASSIFY(ticket_text, ['billing', 'technical', 'account', 'feature_request']):labels[0]::VARCHAR AS category
FROM support_tickets;
```

### AI_EXTRACT Patterns

```sql
SELECT
    AI_EXTRACT(email_body, ['sender_name', 'action_requested', 'deadline'])::OBJECT AS extracted
FROM emails;
```

### Cost Awareness

Estimate token costs before running AI functions on large tables:

```sql
-- Count tokens first
SELECT
    COUNT(*) AS row_count,
    SUM(AI_COUNT_TOKENS('claude-4-sonnet', text_column)) AS total_tokens
FROM my_table;

-- Process a sample first
SELECT AI_COMPLETE('claude-4-sonnet', text_column) FROM my_table SAMPLE (100 ROWS);
```

---

## Cortex Agents

### Agent Spec Structure

```sql
CREATE OR REPLACE AGENT my_db.my_schema.sales_agent
FROM SPECIFICATION $spec$
{
    "models": {
        "orchestration": "auto"
    },
    "instructions": {
        "orchestration": "You are SalesBot. Help users query sales data.",
        "response": "Be concise. Use tables for numeric data."
    },
    "tools": [
        {
            "tool_spec": {
                "type": "cortex_analyst_text_to_sql",
                "name": "SalesQuery",
                "description": "Query sales metrics including revenue, orders, and customer data. Use for questions about sales performance, trends, and comparisons."
            }
        },
        {
            "tool_spec": {
                "type": "cortex_search",
                "name": "PolicySearch",
                "description": "Search company sales policies and procedures."
            }
        }
    ],
    "tool_resources": {
        "SalesQuery": {
            "semantic_model_file": "@my_db.my_schema.models/sales_model.yaml"
        },
        "PolicySearch": {
            "cortex_search_service": "my_db.my_schema.policy_search_service"
        }
    }
}
$spec$;
```

### Agent Rules

- **Delimiter**: Use `$spec$` not `$$` to avoid conflicts with SQL dollar-quoting.
- **models**: Must be an object (`{"orchestration": "auto"}`), not an array.
- **tool_resources**: A separate top-level key, not nested inside individual tool entries.
- **Empty values in edit specs**: Do NOT include `null` or empty string values when editing -- they clear existing values.
- **Tool descriptions**: The single biggest quality factor. Be specific about what data each tool accesses and what questions it answers.
- **Testing**: Never modify production agents directly. Clone first, test, then swap.

### Calling an Agent

```sql
SELECT SNOWFLAKE.CORTEX.AGENT(
    'my_db.my_schema.sales_agent',
    'What was total revenue last quarter?'
);
```

---

## Cortex Search

### Creating a Search Service

```sql
CREATE OR REPLACE CORTEX SEARCH SERVICE my_db.my_schema.docs_search
ON text_column
ATTRIBUTES category, department
WAREHOUSE = search_wh
TARGET_LAG = '1 hour'
AS (
    SELECT text_column, category, department, doc_id
    FROM documents
);
```

### Querying a Search Service

```sql
SELECT PARSE_JSON(
    SNOWFLAKE.CORTEX.SEARCH_PREVIEW(
        'my_db.my_schema.docs_search',
        '{
            "query": "return policy for electronics",
            "columns": ["text_column", "category"],
            "filter": {"@eq": {"department": "retail"}},
            "limit": 5
        }'
    )
) AS results;
```

---

## Snowpark Python

### Session Setup

```python
from snowflake.snowpark import Session
import os

session = Session.builder.configs({
    "account": os.environ["SNOWFLAKE_ACCOUNT"],
    "user": os.environ["SNOWFLAKE_USER"],
    "password": os.environ["SNOWFLAKE_PASSWORD"],
    "role": "my_role",
    "warehouse": "my_wh",
    "database": "my_db",
    "schema": "my_schema"
}).create()
```

### DataFrame Operations

```python
# Lazy operations -- nothing executes until collect()/show()
df = session.table("events")
result = (
    df.filter(df["event_type"] == "purchase")
      .group_by("user_id")
      .agg(F.sum("amount").alias("total_spent"))
      .sort(F.col("total_spent").desc())
)
result.show()  # Execution happens here
```

### Vectorized UDFs (10-100x Faster)

```python
from snowflake.snowpark.functions import pandas_udf
from snowflake.snowpark.types import StringType, PandasSeriesType
import pandas as pd

@pandas_udf(
    name="normalize_email",
    is_permanent=True,
    stage_location="@udf_stage",
    replace=True
)
def normalize_email(emails: pd.Series) -> pd.Series:
    return emails.str.lower().str.strip()
```

### Stored Procedures in Python

```python
from snowflake.snowpark import Session

def process_batch(session: Session, batch_date: str) -> str:
    df = session.table("raw_events").filter(F.col("event_date") == batch_date)
    df.write.mode("overwrite").save_as_table("processed_events")
    return f"Processed {df.count()} rows for {batch_date}"

session.sproc.register(
    func=process_batch,
    name="process_batch",
    is_permanent=True,
    stage_location="@sproc_stage",
    replace=True
)
```

### Key Rules

- Never hardcode credentials. Use environment variables, key pair auth, or Snowflake's built-in connection config.
- DataFrames are lazy. Calling `.collect()` pulls all data to the client -- avoid on large datasets.
- Use vectorized UDFs over scalar UDFs for batch processing (10-100x performance improvement).
- Close sessions when done: `session.close()`.
