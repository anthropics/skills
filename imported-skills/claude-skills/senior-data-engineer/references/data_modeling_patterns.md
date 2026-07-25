# Data Modeling Patterns

Comprehensive guide to data modeling for analytics and data warehousing.

## Table of Contents

1. [Dimensional Modeling](#dimensional-modeling)
2. [Slowly Changing Dimensions](#slowly-changing-dimensions)
3. [Data Vault Modeling](#data-vault-modeling)
4. [dbt Best Practices](#dbt-best-practices)
5. [Partitioning and Clustering](#partitioning-and-clustering)
6. [Schema Evolution](#schema-evolution)

---

## Dimensional Modeling

### Star Schema

The most common pattern for analytical data models. One fact table surrounded by dimension tables.

```
                    ┌─────────────┐
                    │ dim_product │
                    └──────┬──────┘
                           │
┌─────────────┐    ┌───────▼───────┐    ┌─────────────┐
│ dim_customer│◄───│   fct_sales   │───►│  dim_date   │
└─────────────┘    └───────┬───────┘    └─────────────┘
                           │
                    ┌──────▼──────┐
                    │  dim_store  │
                    └─────────────┘
```

**Fact Table (fct_sales):**

```sql
CREATE TABLE fct_sales (
    sale_id BIGINT PRIMARY KEY,

    -- Foreign keys to dimensions
    customer_key INT REFERENCES dim_customer(customer_key),
    product_key INT REFERENCES dim_product(product_key),
    store_key INT REFERENCES dim_store(store_key),
    date_key INT REFERENCES dim_date(date_key),

    -- Degenerate dimension (no separate table)
    order_number VARCHAR(50),

    -- Measures (facts)
    quantity INT,
    unit_price DECIMAL(10,2),
    discount_amount DECIMAL(10,2),
    net_amount DECIMAL(10,2),
    tax_amount DECIMAL(10,2),
    total_amount DECIMAL(10,2),

    -- Audit columns
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Partition by date for query performance
ALTER TABLE fct_sales
PARTITION BY RANGE (date_key);
```

**Dimension Table (dim_customer):**

```sql
CREATE TABLE dim_customer (
    customer_key INT PRIMARY KEY,  -- Surrogate key
    customer_id VARCHAR(50),       -- Natural/business key

    -- Attributes
    first_name VARCHAR(100),
    last_name VARCHAR(100),
    email VARCHAR(255),
    phone VARCHAR(50),

    -- Hierarchies
    city VARCHAR(100),
    state VARCHAR(100),
    country VARCHAR(100),
    region VARCHAR(50),

    -- SCD tracking
    effective_date DATE,
    expiration_date DATE,
    is_current BOOLEAN,

    -- Audit
    created_at TIMESTAMP,
    updated_at TIMESTAMP
);
```

**Date Dimension:**

```sql
CREATE TABLE dim_date (
    date_key INT PRIMARY KEY,      -- YYYYMMDD format
    full_date DATE,

    -- Day attributes
    day_of_week INT,
    day_of_month INT,
    day_of_year INT,
    day_name VARCHAR(10),
    is_weekend BOOLEAN,
    is_holiday BOOLEAN,

    -- Week attributes
    week_of_year INT,
    week_start_date DATE,
    week_end_date DATE,

    -- Month attributes
    month_number INT,
    month_name VARCHAR(10),
    month_start_date DATE,
    month_end_date DATE,

    -- Quarter attributes
    quarter_number INT,
    quarter_name VARCHAR(10),

    -- Year attributes
    year_number INT,
    fiscal_year INT,
    fiscal_quarter INT,

    -- Relative flags
    is_current_day BOOLEAN,
    is_current_week BOOLEAN,
    is_current_month BOOLEAN,
    is_current_quarter BOOLEAN,
    is_current_year BOOLEAN
);

-- Generate date dimension
INSERT INTO dim_date
SELECT
    TO_CHAR(d, 'YYYYMMDD')::INT as date_key,
    d as full_date,
    EXTRACT(DOW FROM d) as day_of_week,
    EXTRACT(DAY FROM d) as day_of_month,
    EXTRACT(DOY FROM d) as day_of_year,
    TO_CHAR(d, 'Day') as day_name,
    EXTRACT(DOW FROM d) IN (0, 6) as is_weekend,
    FALSE as is_holiday,  -- Update from holiday calendar
    EXTRACT(WEEK FROM d) as week_of_year,
    DATE_TRUNC('week', d) as week_start_date,
    DATE_TRUNC('week', d) + INTERVAL '6 days' as week_end_date,
    EXTRACT(MONTH FROM d) as month_number,
    TO_CHAR(d, 'Month') as month_name,
    DATE_TRUNC('month', d) as month_start_date,
    (DATE_TRUNC('month', d) + INTERVAL '1 month' - INTERVAL '1 day')::DATE as month_end_date,
    EXTRACT(QUARTER FROM d) as quarter_number,
    'Q' || EXTRACT(QUARTER FROM d) as quarter_name,
    EXTRACT(YEAR FROM d) as year_number,
    -- Fiscal year (assuming July start)
    CASE WHEN EXTRACT(MONTH FROM d) >= 7 THEN EXTRACT(YEAR FROM d) + 1
         ELSE EXTRACT(YEAR FROM d) END as fiscal_year,
    CASE WHEN EXTRACT(MONTH FROM d) >= 7 THEN CEIL((EXTRACT(MONTH FROM d) - 6) / 3.0)
         ELSE CEIL((EXTRACT(MONTH FROM d) + 6) / 3.0) END as fiscal_quarter,
    d = CURRENT_DATE as is_current_day,
    d >= DATE_TRUNC('week', CURRENT_DATE) AND d < DATE_TRUNC('week', CURRENT_DATE) + INTERVAL '7 days' as is_current_week,
    DATE_TRUNC('month', d) = DATE_TRUNC('month', CURRENT_DATE) as is_current_month,
    DATE_TRUNC('quarter', d) = DATE_TRUNC('quarter', CURRENT_DATE) as is_current_quarter,
    EXTRACT(YEAR FROM d) = EXTRACT(YEAR FROM CURRENT_DATE) as is_current_year
FROM generate_series('2020-01-01'::DATE, '2030-12-31'::DATE, '1 day'::INTERVAL) d;
```

### Snowflake Schema

Normalized dimensions for reduced storage and update anomalies.

```
                         ┌─────────────┐
                         │ dim_category│
                         └──────┬──────┘
                                │
┌─────────────┐    ┌───────────▼────┐    ┌─────────────┐
│ dim_customer│◄───│   fct_sales    │───►│ dim_product │
└──────┬──────┘    └───────┬────────┘    └──────┬──────┘
       │                   │                    │
┌──────▼──────┐    ┌───────▼───────┐    ┌──────▼──────┐
│ dim_geography│   │   dim_date    │    │  dim_brand  │
└─────────────┘    └───────────────┘    └─────────────┘
```

**When to use Snowflake vs Star:**

| Criteria | Star Schema | Snowflake Schema |
|----------|-------------|------------------|
| Query complexity | Simple JOINs | More JOINs required |
| Query performance | Faster (fewer JOINs) | Slower |
| Storage | Higher (denormalized) | Lower (normalized) |
| ETL complexity | Higher | Lower |
| Dimension updates | Multiple places | Single place |
| Best for | BI/reporting | Storage-constrained |

### One Big Table (OBT)

Fully denormalized single table - gaining popularity with modern columnar warehouses.

```sql
CREATE TABLE obt_sales AS
SELECT
    -- Fact measures
    s.sale_id,
    s.quantity,
    s.unit_price,
    s.total_amount,

    -- Customer attributes (denormalized)
    c.customer_id,
    c.first_name,
    c.last_name,
    c.email,
    c.city,
    c.state,
    c.country,

    -- Product attributes (denormalized)
    p.product_id,
    p.product_name,
    p.category,
    p.subcategory,
    p.brand,

    -- Date attributes (denormalized)
    d.full_date as sale_date,
    d.year_number,
    d.quarter_number,
    d.month_name,
    d.week_of_year,
    d.is_weekend

FROM fct_sales s
JOIN dim_customer c ON s.customer_key = c.customer_key AND c.is_current
JOIN dim_product p ON s.product_key = p.product_key AND p.is_current
JOIN dim_date d ON s.date_key = d.date_key;
```

**OBT Tradeoffs:**

| Pros | Cons |
|------|------|
| Simple queries (no JOINs) | Storage bloat |
| Fast for analytics | Harder to maintain |
| Great with columnar storage | Stale data risk |
| Self-documenting | Update anomalies |

---

## Slowly Changing Dimensions

### Type 0: Fixed Dimension

No changes allowed - original value preserved forever.

```sql
-- Type 0: Never update these fields
CREATE TABLE dim_customer_type0 (
    customer_key INT PRIMARY KEY,
    customer_id VARCHAR(50),
    original_signup_date DATE,  -- Never changes
    original_source VARCHAR(50) -- Never changes
);
```

### Type 1: Overwrite

Simply overwrite old value with new. No history preserved.

```sql
-- Type 1: Update in place
UPDATE dim_customer
SET
    email = 'new.email@example.com',
    updated_at = CURRENT_TIMESTAMP
WHERE customer_id = 'CUST001';

-- dbt implementation (Type 1)
-- models/dim_customer_type1.sql
{{
    config(
        materialized='table',
        unique_key='customer_id'
    )
}}

SELECT
    customer_id,
    first_name,
    last_name,
    email,  -- Current value only
    phone,
    address,
    CURRENT_TIMESTAMP as updated_at
FROM {{ source('raw', 'customers') }}
```

### Type 2: Add New Row

Create new record with new values. Full history preserved.

```sql
-- Type 2 dimension structure
CREATE TABLE dim_customer_scd2 (
    customer_key SERIAL PRIMARY KEY,    -- Surrogate key
    customer_id VARCHAR(50),            -- Natural key
    first_name VARCHAR(100),
    last_name VARCHAR(100),
    email VARCHAR(255),
    city VARCHAR(100),
    state VARCHAR(100),

    -- SCD2 tracking columns
    effective_start_date TIMESTAMP,
    effective_end_date TIMESTAMP,
    is_current BOOLEAN,

    -- Hash for change detection
    row_hash VARCHAR(64)
);

-- SCD2 merge logic
MERGE INTO dim_customer_scd2 AS target
USING (
    SELECT
        customer_id,
        first_name,
        last_name,
        email,
        city,
        state,
        MD5(CONCAT(first_name, last_name, email, city, state)) as row_hash
    FROM staging_customers
) AS source
ON target.customer_id = source.customer_id AND target.is_current = TRUE

-- Close existing record if changed
WHEN MATCHED AND target.row_hash != source.row_hash THEN
    UPDATE SET
        effective_end_date = CURRENT_TIMESTAMP,
        is_current = FALSE

-- Insert new record for changes
WHEN NOT MATCHED OR (MATCHED AND target.row_hash != source.row_hash) THEN
    INSERT (customer_id, first_name, last_name, email, city, state,
            effective_start_date, effective_end_date, is_current, row_hash)
    VALUES (source.customer_id, source.first_name, source.last_name, source.email,
            source.city, source.state, CURRENT_TIMESTAMP, '9999-12-31', TRUE, source.row_hash);
```

**dbt SCD2 Implementation:**

```sql
-- models/dim_customer_scd2.sql
{{
    config(
        materialized='incremental',
        unique_key='customer_key',
        strategy='check',
        check_cols=['first_name', 'last_name', 'email', 'city', 'state']
    )
}}

WITH source_data AS (
    SELECT
        customer_id,
        first_name,
        last_name,
        email,
        city,
        state,
        MD5(CONCAT_WS('|', first_name, last_name, email, city, state)) as row_hash,
        CURRENT_TIMESTAMP as extracted_at
    FROM {{ source('raw', 'customers') }}
),

{% if is_incremental() %}
-- Get current records that have changed
changed_records AS (
    SELECT
        s.*,
        t.customer_key as existing_key
    FROM source_data s
    LEFT JOIN {{ this }} t
        ON s.customer_id = t.customer_id
        AND t.is_current = TRUE
    WHERE t.customer_key IS NULL  -- New record
       OR t.row_hash != s.row_hash  -- Changed record
)
{% endif %}

SELECT
    {{ dbt_utils.generate_surrogate_key(['customer_id', 'extracted_at']) }} as customer_key,
    customer_id,
    first_name,
    last_name,
    email,
    city,
    state,
    extracted_at as effective_start_date,
    CAST('9999-12-31' AS TIMESTAMP) as effective_end_date,
    TRUE as is_current,
    row_hash
{% if is_incremental() %}
FROM changed_records
{% else %}
FROM source_data
{% endif %}
```

### Type 3: Add New Column

Add column for previous value. Limited history (usually just prior value).

```sql
-- Type 3: Previous value column
CREATE TABLE dim_customer_scd3 (
    customer_key INT PRIMARY KEY,
    customer_id VARCHAR(50),
    city VARCHAR(100),
    previous_city VARCHAR(100),  -- Previous value
    city_change_date DATE,
    state VARCHAR(100),
    previous_state VARCHAR(100),
    state_change_date DATE
);

-- Update Type 3
UPDATE dim_customer_scd3
SET
    previous_city = city,
    city = 'New York',
    city_change_date = CURRENT_DATE
WHERE customer_id = 'CUST001';
```

### Type 4: Mini-Dimension

Separate rapidly changing attributes into a mini-dimension.

```sql
-- Main customer dimension (slowly changing)
CREATE TABLE dim_customer (
    customer_key INT PRIMARY KEY,
    customer_id VARCHAR(50),
    first_name VARCHAR(100),
    last_name VARCHAR(100),
    email VARCHAR(255)
);

-- Mini-dimension for rapidly changing attributes
CREATE TABLE dim_customer_profile (
    profile_key INT PRIMARY KEY,
    age_band VARCHAR(20),      -- '18-24', '25-34', etc.
    income_band VARCHAR(20),   -- 'Low', 'Medium', 'High'
    loyalty_tier VARCHAR(20)   -- 'Bronze', 'Silver', 'Gold'
);

-- Fact table references both
CREATE TABLE fct_sales (
    sale_id BIGINT PRIMARY KEY,
    customer_key INT REFERENCES dim_customer,
    profile_key INT REFERENCES dim_customer_profile,  -- Current profile at time of sale
    ...
);
```

### Type 6: Hybrid (1 + 2 + 3)

Combines Types 1, 2, and 3 for maximum flexibility.

```sql
-- Type 6: Combined approach
CREATE TABLE dim_customer_scd6 (
    customer_key INT PRIMARY KEY,
    customer_id VARCHAR(50),

    -- Current values (Type 1 - always updated)
    current_city VARCHAR(100),
    current_state VARCHAR(100),

    -- Historical values (Type 2 - row versioned)
    historical_city VARCHAR(100),
    historical_state VARCHAR(100),

    -- Previous values (Type 3)
    previous_city VARCHAR(100),

    -- SCD2 tracking
    effective_start_date TIMESTAMP,
    effective_end_date TIMESTAMP,
    is_current BOOLEAN
);
```

---

## Data Vault Modeling

### Core Concepts

Data Vault provides:
- Full historization
- Parallel loading
- Flexibility for changing business rules
- Auditability

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  Hub_Customer│◄───│Link_Customer│───►│  Hub_Order  │
│              │    │   _Order    │    │             │
└──────┬───────┘    └─────────────┘    └──────┬──────┘
       │                                      │
       ▼                                      ▼
┌─────────────┐                        ┌─────────────┐
│Sat_Customer │                        │  Sat_Order  │
│  _Details   │                        │  _Details   │
└─────────────┘                        └─────────────┘
```

### Hub Tables

Business keys and surrogate keys only.

```sql
-- Hub: Business entity identifier
CREATE TABLE hub_customer (
    hub_customer_key VARCHAR(64) PRIMARY KEY,  -- Hash of business key
    customer_id VARCHAR(50),                    -- Business key
    load_date TIMESTAMP,
    record_source VARCHAR(100)
);

-- Hub loading (idempotent insert)
INSERT INTO hub_customer (hub_customer_key, customer_id, load_date, record_source)
SELECT
    MD5(customer_id) as hub_customer_key,
    customer_id,
    CURRENT_TIMESTAMP as load_date,
    'SOURCE_CRM' as record_source
FROM staging_customers s
WHERE NOT EXISTS (
    SELECT 1 FROM hub_customer h
    WHERE h.customer_id = s.customer_id
);
```

### Satellite Tables

Descriptive attributes with full history.

```sql
-- Satellite: Attributes with history
CREATE TABLE sat_customer_details (
    hub_customer_key VARCHAR(64),
    load_date TIMESTAMP,
    load_end_date TIMESTAMP,

    -- Descriptive attributes
    first_name VARCHAR(100),
    last_name VARCHAR(100),
    email VARCHAR(255),
    phone VARCHAR(50),

    -- Change detection
    hash_diff VARCHAR(64),
    record_source VARCHAR(100),

    PRIMARY KEY (hub_customer_key, load_date),
    FOREIGN KEY (hub_customer_key) REFERENCES hub_customer
);

-- Satellite loading (delta detection)
INSERT INTO sat_customer_details
SELECT
    MD5(s.customer_id) as hub_customer_key,
    CURRENT_TIMESTAMP as load_date,
    NULL as load_end_date,
    s.first_name,
    s.last_name,
    s.email,
    s.phone,
    MD5(CONCAT_WS('|', s.first_name, s.last_name, s.email, s.phone)) as hash_diff,
    'SOURCE_CRM' as record_source
FROM staging_customers s
LEFT JOIN sat_customer_details sat
    ON MD5(s.customer_id) = sat.hub_customer_key
    AND sat.load_end_date IS NULL
WHERE sat.hub_customer_key IS NULL  -- New customer
   OR sat.hash_diff != MD5(CONCAT_WS('|', s.first_name, s.last_name, s.email, s.phone));  -- Changed

-- Close previous satellite records
UPDATE sat_customer_details
SET load_end_date = CURRENT_TIMESTAMP
WHERE hub_customer_key IN (
    SELECT MD5(customer_id) FROM staging_customers
)
AND load_end_date IS NULL
AND load_date < CURRENT_TIMESTAMP;
```

### Link Tables

Relationships between hubs.

```sql
-- Link: Relationship between entities
CREATE TABLE link_customer_order (
    link_customer_order_key VARCHAR(64) PRIMARY KEY,
    hub_customer_key VARCHAR(64),
    hub_order_key VARCHAR(64),
    load_date TIMESTAMP,
    record_source VARCHAR(100),

    FOREIGN KEY (hub_customer_key) REFERENCES hub_customer,
    FOREIGN KEY (hub_order_key) REFERENCES hub_order
);

-- Link loading
INSERT INTO link_customer_order
SELECT
    MD5(CONCAT(s.customer_id, '|', s.order_id)) as link_customer_order_key,
    MD5(s.customer_id) as hub_customer_key,
    MD5(s.order_id) as hub_order_key,
    CURRENT_TIMESTAMP as load_date,
    'SOURCE_ORDERS' as record_source
FROM staging_orders s
WHERE NOT EXISTS (
    SELECT 1 FROM link_customer_order l
    WHERE l.hub_customer_key = MD5(s.customer_id)
      AND l.hub_order_key = MD5(s.order_id)
);
```

---

## dbt Best Practices

### Model Organization

```
models/
├── staging/           # 1:1 with source tables
│   ├── stg_orders.sql
│   ├── stg_customers.sql
│   └── _staging.yml
├── intermediate/      # Business logic transformations
│   ├── int_orders_enriched.sql
│   └── _intermediate.yml
└── marts/             # Business-facing models
    ├── core/
    │   ├── dim_customers.sql
    │   ├── fct_orders.sql
    │   └── _core.yml
    └── marketing/
        ├── mrt_customer_segments.sql
        └── _marketing.yml
```

### Staging Models

```sql
-- models/staging/stg_orders.sql
{{
    config(
        materialized='view'
    )
}}

WITH source AS (
    SELECT * FROM {{ source('ecommerce', 'orders') }}
),

renamed AS (
    SELECT
        -- Primary key
        id as order_id,

        -- Foreign keys
        customer_id,
        product_id,

        -- Timestamps
        created_at as order_created_at,
        updated_at as order_updated_at,

        -- Measures
        quantity,
        CAST(unit_price AS DECIMAL(10,2)) as unit_price,
        CAST(discount AS DECIMAL(5,2)) as discount_percent,

        -- Status
        UPPER(status) as order_status

    FROM source
)

SELECT * FROM renamed
```

### Intermediate Models

```sql
-- models/intermediate/int_orders_enriched.sql
{{
    config(
        materialized='ephemeral'  -- Not persisted, just CTE
    )
}}

WITH orders AS (
    SELECT * FROM {{ ref('stg_orders') }}
),

customers AS (
    SELECT * FROM {{ ref('stg_customers') }}
),

products AS (
    SELECT * FROM {{ ref('stg_products') }}
),

enriched AS (
    SELECT
        o.order_id,
        o.order_created_at,
        o.order_status,

        -- Customer info
        c.customer_id,
        c.customer_name,
        c.customer_segment,

        -- Product info
        p.product_id,
        p.product_name,
        p.category,

        -- Calculated fields
        o.quantity,
        o.unit_price,
        o.quantity * o.unit_price as gross_amount,
        o.quantity * o.unit_price * (1 - COALESCE(o.discount_percent, 0) / 100) as net_amount

    FROM orders o
    LEFT JOIN customers c ON o.customer_id = c.customer_id
    LEFT JOIN products p ON o.product_id = p.product_id
)

SELECT * FROM enriched
```

### Incremental Models

```sql
-- models/marts/fct_orders.sql
{{
    config(
        materialized='incremental',
        unique_key='order_id',
        incremental_strategy='merge',
        on_schema_change='sync_all_columns',
        cluster_by=['order_date']
    )
}}

WITH orders AS (
    SELECT * FROM {{ ref('int_orders_enriched') }}

    {% if is_incremental() %}
    -- Only process new/changed records
    WHERE order_updated_at > (
        SELECT COALESCE(MAX(order_updated_at), '1900-01-01')
        FROM {{ this }}
    )
    {% endif %}
),

final AS (
    SELECT
        order_id,
        customer_id,
        product_id,
        DATE(order_created_at) as order_date,
        order_created_at,
        order_updated_at,
        order_status,
        quantity,
        unit_price,
        gross_amount,
        net_amount,
        CURRENT_TIMESTAMP as _loaded_at
    FROM orders
)

SELECT * FROM final
```

### Testing

```yaml
# models/marts/_core.yml
version: 2

models:
  - name: fct_orders
    description: "Order fact table"
    columns:
      - name: order_id
        tests:
          - unique
          - not_null

      - name: customer_id
        tests:
          - not_null
          - relationships:
              to: ref('dim_customers')
              field: customer_id

      - name: net_amount
        tests:
          - not_null
          - dbt_utils.accepted_range:
              min_value: 0
              inclusive: true

      - name: order_date
        tests:
          - not_null
          - dbt_utils.recency:
              datepart: day
              field: order_date
              interval: 1
```

### Macros

```sql
-- macros/generate_surrogate_key.sql
{% macro generate_surrogate_key(columns) %}
    {{ dbt_utils.generate_surrogate_key(columns) }}
{% endmacro %}

-- macros/cents_to_dollars.sql
{% macro cents_to_dollars(column_name) %}
    ROUND({{ column_name }} / 100.0, 2)
{% endmacro %}

-- macros/safe_divide.sql
{% macro safe_divide(numerator, denominator, default=0) %}
    CASE
        WHEN {{ denominator }} = 0 OR {{ denominator }} IS NULL THEN {{ default }}
        ELSE {{ numerator }} / {{ denominator }}
    END
{% endmacro %}

-- Usage in models:
-- {{ safe_divide('revenue', 'orders') }} as avg_order_value
```

---

## Partitioning and Clustering

### Partitioning Strategies

**Time-based Partitioning (Most Common):**

```sql
-- BigQuery
CREATE TABLE fct_events
PARTITION BY DATE(event_timestamp)
CLUSTER BY user_id, event_type
AS SELECT * FROM raw_events;

-- Snowflake (automatic micro-partitioning)
-- Explicit clustering for optimization
ALTER TABLE fct_events CLUSTER BY (event_date, user_id);

-- Spark/Delta Lake
df.write \
    .format("delta") \
    .partitionBy("event_date") \
    .save("/path/to/table")
```

**Partition Pruning:**

```sql
-- Query with partition filter (fast)
SELECT * FROM fct_events
WHERE event_date = '2024-01-15';  -- Scans only 1 partition

-- Query without partition filter (slow - full scan)
SELECT * FROM fct_events
WHERE user_id = '12345';  -- Scans all partitions
```

**Partition Size Guidelines:**

| Partition | Size Target | Notes |
|-----------|-------------|-------|
| Daily | 1-10 GB | Ideal for most cases |
| Hourly | 100 MB - 1 GB | High-volume streaming |
| Monthly | 10-100 GB | Infrequent access |

### Clustering

```sql
-- BigQuery clustering (up to 4 columns)
CREATE TABLE fct_sales
PARTITION BY DATE(sale_date)
CLUSTER BY customer_id, product_id
AS SELECT * FROM raw_sales;

-- Snowflake clustering
CREATE TABLE fct_sales (
    sale_id INT,
    customer_id VARCHAR(50),
    product_id VARCHAR(50),
    sale_date DATE,
    amount DECIMAL(10,2)
)
CLUSTER BY (customer_id, sale_date);

-- Delta Lake Z-ordering
OPTIMIZE events ZORDER BY (user_id, event_type);
```

**When to Cluster:**

| Column Type | Cluster? | Notes |
|-------------|----------|-------|
| High cardinality filter columns | Yes | customer_id, product_id |
| Join keys | Yes | Improves join performance |
| Low cardinality | Maybe | status, type (limited benefit) |
| Frequently updated | No | Clustering breaks on updates |

---

## Schema Evolution

### Adding Columns

```sql
-- Safe: Add nullable column
ALTER TABLE fct_orders ADD COLUMN discount_amount DECIMAL(10,2);

-- With default
ALTER TABLE fct_orders ADD COLUMN currency VARCHAR(3) DEFAULT 'USD';

-- dbt handling
{{
    config(
        materialized='incremental',
        on_schema_change='append_new_columns'
    )
}}
```

### Handling in Spark/Delta

```python
# Delta Lake schema evolution
df.write \
    .format("delta") \
    .mode("append") \
    .option("mergeSchema", "true") \
    .save("/path/to/table")

# Explicit schema enforcement
spark.sql("""
    ALTER TABLE delta.`/path/to/table`
    ADD COLUMNS (new_column STRING)
""")

# Schema merge on read
df = spark.read \
    .option("mergeSchema", "true") \
    .format("delta") \
    .load("/path/to/table")
```

### Backward Compatibility

```sql
-- Create view for backward compatibility
CREATE VIEW orders_v1 AS
SELECT
    order_id,
    customer_id,
    amount,
    -- Map new columns to old schema
    COALESCE(discount_amount, 0) as discount,
    COALESCE(currency, 'USD') as currency
FROM orders_v2;

-- Deprecation pattern
CREATE VIEW orders_deprecated AS
SELECT * FROM orders_v1;
-- Add comment: "DEPRECATED: Use orders_v2. Will be removed 2024-06-01"
```

### Data Contracts for Schema Changes

```yaml
# contracts/orders_contract.yaml
name: orders
version: "2.0.0"
owner: data-team@company.com

schema:
  order_id:
    type: string
    required: true
    breaking_change: never

  customer_id:
    type: string
    required: true
    breaking_change: never

  amount:
    type: decimal
    precision: 10
    scale: 2
    required: true

  # New in v2.0.0
  discount_amount:
    type: decimal
    precision: 10
    scale: 2
    required: false
    added_in: "2.0.0"
    default: 0

  # Deprecated in v2.0.0
  legacy_status:
    type: string
    deprecated: true
    removed_in: "3.0.0"
    migration: "Use order_status instead"

compatibility:
  backward: true   # v2 readers can read v1 data
  forward: true    # v1 readers can read v2 data
```
