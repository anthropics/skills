---
name: "senior-data-engineer"
description: Data engineering skill for building scalable data pipelines, ETL/ELT systems, and data infrastructure. Expertise in Python, SQL, Spark, Airflow, dbt, Kafka, and modern data stack. Includes data modeling, pipeline orchestration, data quality, and DataOps. Use when designing data architectures, building data pipelines, optimizing data workflows, implementing data governance, or troubleshooting data issues.
---

# Senior Data Engineer

Production-grade data engineering skill for building scalable, reliable data systems.

## Table of Contents

1. [Trigger Phrases](#trigger-phrases)
2. [Quick Start](#quick-start)
3. [Workflows](#workflows)
4. [Architecture Decision Framework](#architecture-decision-framework)
5. [Tech Stack](#tech-stack)
6. [Reference Documentation](#reference-documentation)
7. [Troubleshooting](#troubleshooting)

---

## Trigger Phrases

Activate this skill when you see:

**Pipeline Design:**
- "Design a data pipeline for..."
- "Build an ETL/ELT process..."
- "How should I ingest data from..."
- "Set up data extraction from..."

**Architecture:**
- "Should I use batch or streaming?"
- "Lambda vs Kappa architecture"
- "How to handle late-arriving data"
- "Design a data lakehouse"

**Data Modeling:**
- "Create a dimensional model..."
- "Star schema vs snowflake"
- "Implement slowly changing dimensions"
- "Design a data vault"

**Data Quality:**
- "Add data validation to..."
- "Set up data quality checks"
- "Monitor data freshness"
- "Implement data contracts"

**Performance:**
- "Optimize this Spark job"
- "Query is running slow"
- "Reduce pipeline execution time"
- "Tune Airflow DAG"

---

## Quick Start

### Core Tools

```bash
# Generate pipeline orchestration config
python scripts/pipeline_orchestrator.py generate \
  --type airflow \
  --source postgres \
  --destination snowflake \
  --schedule "0 5 * * *"

# Validate data quality
python scripts/data_quality_validator.py validate \
  --input data/sales.parquet \
  --schema schemas/sales.json \
  --checks freshness,completeness,uniqueness

# Optimize ETL performance
python scripts/etl_performance_optimizer.py analyze \
  --query queries/daily_aggregation.sql \
  --engine spark \
  --recommend
```

---

## Workflows
→ See references/workflows.md for details

## Architecture Decision Framework

Use this framework to choose the right approach for your data pipeline.

### Batch vs Streaming

| Criteria | Batch | Streaming |
|----------|-------|-----------|
| **Latency requirement** | Hours to days | Seconds to minutes |
| **Data volume** | Large historical datasets | Continuous event streams |
| **Processing complexity** | Complex transformations, ML | Simple aggregations, filtering |
| **Cost sensitivity** | More cost-effective | Higher infrastructure cost |
| **Error handling** | Easier to reprocess | Requires careful design |

**Decision Tree:**
```
Is real-time insight required?
├── Yes → Use streaming
│   └── Is exactly-once semantics needed?
│       ├── Yes → Kafka + Flink/Spark Structured Streaming
│       └── No → Kafka + consumer groups
└── No → Use batch
    └── Is data volume > 1TB daily?
        ├── Yes → Spark/Databricks
        └── No → dbt + warehouse compute
```

### Lambda vs Kappa Architecture

| Aspect | Lambda | Kappa |
|--------|--------|-------|
| **Complexity** | Two codebases (batch + stream) | Single codebase |
| **Maintenance** | Higher (sync batch/stream logic) | Lower |
| **Reprocessing** | Native batch layer | Replay from source |
| **Use case** | ML training + real-time serving | Pure event-driven |

**When to choose Lambda:**
- Need to train ML models on historical data
- Complex batch transformations not feasible in streaming
- Existing batch infrastructure

**When to choose Kappa:**
- Event-sourced architecture
- All processing can be expressed as stream operations
- Starting fresh without legacy systems

### Data Warehouse vs Data Lakehouse

| Feature | Warehouse (Snowflake/BigQuery) | Lakehouse (Delta/Iceberg) |
|---------|-------------------------------|---------------------------|
| **Best for** | BI, SQL analytics | ML, unstructured data |
| **Storage cost** | Higher (proprietary format) | Lower (open formats) |
| **Flexibility** | Schema-on-write | Schema-on-read |
| **Performance** | Excellent for SQL | Good, improving |
| **Ecosystem** | Mature BI tools | Growing ML tooling |

---

## Tech Stack

| Category | Technologies |
|----------|--------------|
| **Languages** | Python, SQL, Scala |
| **Orchestration** | Airflow, Prefect, Dagster |
| **Transformation** | dbt, Spark, Flink |
| **Streaming** | Kafka, Kinesis, Pub/Sub |
| **Storage** | S3, GCS, Delta Lake, Iceberg |
| **Warehouses** | Snowflake, BigQuery, Redshift, Databricks |
| **Quality** | Great Expectations, dbt tests, Monte Carlo |
| **Monitoring** | Prometheus, Grafana, Datadog |

---

## Reference Documentation

### 1. Data Pipeline Architecture
See `references/data_pipeline_architecture.md` for:
- Lambda vs Kappa architecture patterns
- Batch processing with Spark and Airflow
- Stream processing with Kafka and Flink
- Exactly-once semantics implementation
- Error handling and dead letter queues

### 2. Data Modeling Patterns
See `references/data_modeling_patterns.md` for:
- Dimensional modeling (Star/Snowflake)
- Slowly Changing Dimensions (SCD Types 1-6)
- Data Vault modeling
- dbt best practices
- Partitioning and clustering

### 3. DataOps Best Practices
See `references/dataops_best_practices.md` for:
- Data testing frameworks
- Data contracts and schema validation
- CI/CD for data pipelines
- Observability and lineage
- Incident response

---

## Troubleshooting
→ See references/troubleshooting.md for details

