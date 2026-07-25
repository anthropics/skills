# DataOps Best Practices

Comprehensive guide to DataOps practices for production data systems.

## Table of Contents

1. [Data Testing Frameworks](#data-testing-frameworks)
2. [Data Contracts](#data-contracts)
3. [CI/CD for Data Pipelines](#cicd-for-data-pipelines)
4. [Observability and Lineage](#observability-and-lineage)
5. [Incident Response](#incident-response)
6. [Cost Optimization](#cost-optimization)

---

## Data Testing Frameworks

### Great Expectations

```python
# great_expectations_suite.py
import great_expectations as gx
from great_expectations.core.batch import BatchRequest

# Initialize context
context = gx.get_context()

# Create expectation suite
suite = context.add_expectation_suite("orders_suite")

# Get validator
validator = context.get_validator(
    batch_request=BatchRequest(
        datasource_name="warehouse",
        data_asset_name="orders",
    ),
    expectation_suite_name="orders_suite"
)

# Schema expectations
validator.expect_table_columns_to_match_set(
    column_set=["order_id", "customer_id", "amount", "created_at", "status"],
    exact_match=True
)

# Completeness expectations
validator.expect_column_values_to_not_be_null(
    column="order_id",
    mostly=1.0  # 100% must be non-null
)

validator.expect_column_values_to_not_be_null(
    column="customer_id",
    mostly=0.99  # 99% must be non-null
)

# Uniqueness expectations
validator.expect_column_values_to_be_unique("order_id")

# Type expectations
validator.expect_column_values_to_be_of_type("amount", "FLOAT")
validator.expect_column_values_to_be_of_type("created_at", "TIMESTAMP")

# Range expectations
validator.expect_column_values_to_be_between(
    column="amount",
    min_value=0,
    max_value=1000000,
    mostly=0.999
)

# Categorical expectations
validator.expect_column_values_to_be_in_set(
    column="status",
    value_set=["pending", "confirmed", "shipped", "delivered", "cancelled"]
)

# Distribution expectations
validator.expect_column_mean_to_be_between(
    column="amount",
    min_value=50,
    max_value=500
)

# Freshness expectations
validator.expect_column_max_to_be_between(
    column="created_at",
    min_value={"$PARAMETER": "now() - interval '24 hours'"},
    max_value={"$PARAMETER": "now()"}
)

# Cross-table expectations (referential integrity)
validator.expect_column_pair_values_to_be_in_set(
    column_A="customer_id",
    column_B="customer_status",
    value_pairs_set=[
        ("cust_001", "active"),
        ("cust_002", "active"),
        # ...
    ]
)

# Save suite
validator.save_expectation_suite(discard_failed_expectations=False)

# Run validation
checkpoint = context.add_or_update_checkpoint(
    name="orders_checkpoint",
    validations=[
        {
            "batch_request": {
                "datasource_name": "warehouse",
                "data_asset_name": "orders",
            },
            "expectation_suite_name": "orders_suite",
        }
    ],
)

results = checkpoint.run()
print(f"Validation success: {results.success}")
```

### dbt Tests

```yaml
# models/marts/schema.yml
version: 2

models:
  - name: fct_orders
    description: "Order fact table with comprehensive testing"

    # Model-level tests
    tests:
      # Row count consistency
      - dbt_utils.equal_rowcount:
          compare_model: ref('stg_orders')

      # Expression test
      - dbt_utils.expression_is_true:
          expression: "net_amount >= 0"

      # Recency test
      - dbt_utils.recency:
          datepart: hour
          field: _loaded_at
          interval: 24

    columns:
      - name: order_id
        description: "Primary key - unique order identifier"
        tests:
          - unique
          - not_null
          - dbt_expectations.expect_column_values_to_match_regex:
              regex: "^ORD-[0-9]{10}$"

      - name: customer_id
        tests:
          - not_null
          - relationships:
              to: ref('dim_customers')
              field: customer_id
              severity: warn  # Don't fail, just warn

      - name: order_date
        tests:
          - not_null
          - dbt_expectations.expect_column_values_to_be_between:
              min_value: "'2020-01-01'"
              max_value: "current_date"

      - name: net_amount
        tests:
          - not_null
          - dbt_utils.accepted_range:
              min_value: 0
              max_value: 1000000
              inclusive: true

      - name: quantity
        tests:
          - dbt_expectations.expect_column_values_to_be_between:
              min_value: 1
              max_value: 1000
              row_condition: "status != 'cancelled'"

      - name: status
        tests:
          - accepted_values:
              values: ['pending', 'confirmed', 'shipped', 'delivered', 'cancelled']

  - name: dim_customers
    columns:
      - name: customer_id
        tests:
          - unique
          - not_null

      - name: email
        tests:
          - unique:
              where: "is_current = true"
          - dbt_expectations.expect_column_values_to_match_regex:
              regex: "^[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\\.[a-zA-Z0-9-.]+$"

# Custom generic test
# tests/generic/test_no_orphan_records.sql
{% test no_orphan_records(model, column_name, parent_model, parent_column) %}
SELECT {{ column_name }}
FROM {{ model }}
WHERE {{ column_name }} NOT IN (
    SELECT {{ parent_column }}
    FROM {{ parent_model }}
)
{% endtest %}
```

### Custom Data Quality Checks

```python
# data_quality/quality_checks.py
from dataclasses import dataclass
from typing import List, Dict, Any, Callable
from datetime import datetime, timedelta
import logging

logger = logging.getLogger(__name__)

@dataclass
class QualityCheck:
    name: str
    description: str
    severity: str  # "critical", "warning", "info"
    check_func: Callable
    threshold: float = 1.0

@dataclass
class QualityResult:
    check_name: str
    passed: bool
    actual_value: float
    threshold: float
    message: str
    timestamp: datetime

class DataQualityValidator:
    """Comprehensive data quality validation framework."""

    def __init__(self, connection):
        self.conn = connection
        self.checks: List[QualityCheck] = []
        self.results: List[QualityResult] = []

    def add_check(self, check: QualityCheck):
        self.checks.append(check)

    # Built-in check generators
    def add_null_check(self, table: str, column: str, max_null_rate: float = 0.0):
        def check_nulls():
            query = f"""
                SELECT
                    COUNT(*) as total,
                    SUM(CASE WHEN {column} IS NULL THEN 1 ELSE 0 END) as nulls
                FROM {table}
            """
            result = self.conn.execute(query).fetchone()
            null_rate = result[1] / result[0] if result[0] > 0 else 0
            return null_rate <= max_null_rate, null_rate

        self.add_check(QualityCheck(
            name=f"null_check_{table}_{column}",
            description=f"Check null rate for {table}.{column}",
            severity="critical" if max_null_rate == 0 else "warning",
            check_func=check_nulls,
            threshold=max_null_rate
        ))

    def add_uniqueness_check(self, table: str, column: str):
        def check_unique():
            query = f"""
                SELECT
                    COUNT(*) as total,
                    COUNT(DISTINCT {column}) as distinct_count
                FROM {table}
            """
            result = self.conn.execute(query).fetchone()
            is_unique = result[0] == result[1]
            duplicate_rate = 1 - (result[1] / result[0]) if result[0] > 0 else 0
            return is_unique, duplicate_rate

        self.add_check(QualityCheck(
            name=f"uniqueness_check_{table}_{column}",
            description=f"Check uniqueness for {table}.{column}",
            severity="critical",
            check_func=check_unique,
            threshold=0.0
        ))

    def add_freshness_check(self, table: str, timestamp_column: str, max_hours: int):
        def check_freshness():
            query = f"""
                SELECT MAX({timestamp_column}) as latest
                FROM {table}
            """
            result = self.conn.execute(query).fetchone()
            if result[0] is None:
                return False, float('inf')

            hours_old = (datetime.now() - result[0]).total_seconds() / 3600
            return hours_old <= max_hours, hours_old

        self.add_check(QualityCheck(
            name=f"freshness_check_{table}",
            description=f"Check data freshness for {table}",
            severity="critical",
            check_func=check_freshness,
            threshold=max_hours
        ))

    def add_range_check(self, table: str, column: str, min_val: float, max_val: float):
        def check_range():
            query = f"""
                SELECT
                    COUNT(*) as total,
                    SUM(CASE WHEN {column} < {min_val} OR {column} > {max_val} THEN 1 ELSE 0 END) as out_of_range
                FROM {table}
            """
            result = self.conn.execute(query).fetchone()
            violation_rate = result[1] / result[0] if result[0] > 0 else 0
            return violation_rate == 0, violation_rate

        self.add_check(QualityCheck(
            name=f"range_check_{table}_{column}",
            description=f"Check range [{min_val}, {max_val}] for {table}.{column}",
            severity="warning",
            check_func=check_range,
            threshold=0.0
        ))

    def add_referential_integrity_check(self, child_table: str, child_column: str,
                                        parent_table: str, parent_column: str):
        def check_referential():
            query = f"""
                SELECT COUNT(*)
                FROM {child_table} c
                LEFT JOIN {parent_table} p ON c.{child_column} = p.{parent_column}
                WHERE p.{parent_column} IS NULL AND c.{child_column} IS NOT NULL
            """
            result = self.conn.execute(query).fetchone()
            orphan_count = result[0]
            return orphan_count == 0, orphan_count

        self.add_check(QualityCheck(
            name=f"referential_integrity_{child_table}_{child_column}",
            description=f"Check FK {child_table}.{child_column} -> {parent_table}.{parent_column}",
            severity="warning",
            check_func=check_referential,
            threshold=0
        ))

    def run_all_checks(self) -> Dict[str, Any]:
        """Execute all quality checks and return results."""
        self.results = []

        for check in self.checks:
            try:
                passed, actual_value = check.check_func()
                result = QualityResult(
                    check_name=check.name,
                    passed=passed,
                    actual_value=actual_value,
                    threshold=check.threshold,
                    message=f"{'PASSED' if passed else 'FAILED'}: {check.description}",
                    timestamp=datetime.now()
                )
            except Exception as e:
                result = QualityResult(
                    check_name=check.name,
                    passed=False,
                    actual_value=-1,
                    threshold=check.threshold,
                    message=f"ERROR: {str(e)}",
                    timestamp=datetime.now()
                )

            self.results.append(result)
            logger.info(result.message)

        # Summary
        total = len(self.results)
        passed = sum(1 for r in self.results if r.passed)
        failed = total - passed

        critical_failures = [
            r for r, c in zip(self.results, self.checks)
            if not r.passed and c.severity == "critical"
        ]

        return {
            "total_checks": total,
            "passed": passed,
            "failed": failed,
            "success_rate": passed / total if total > 0 else 0,
            "critical_failures": len(critical_failures),
            "results": self.results,
            "overall_passed": len(critical_failures) == 0
        }
```

---

## Data Contracts

### Contract Definition

```yaml
# contracts/orders_v2.yaml
contract:
  name: orders
  version: "2.0.0"
  owner: data-platform@company.com
  team: Data Engineering
  slack_channel: "#data-platform-alerts"

description: |
  Order events from the e-commerce platform.
  Contains all customer orders with line items.

schema:
  type: object
  required:
    - order_id
    - customer_id
    - created_at
    - total_amount
  properties:
    order_id:
      type: string
      format: uuid
      description: "Unique order identifier"
      pii: false
      breaking_change: never

    customer_id:
      type: string
      description: "Customer identifier (foreign key)"
      pii: true
      retention_days: 365

    created_at:
      type: timestamp
      format: "ISO8601"
      timezone: "UTC"
      description: "Order creation timestamp"

    total_amount:
      type: decimal
      precision: 10
      scale: 2
      minimum: 0
      description: "Total order amount in USD"

    status:
      type: string
      enum: ["pending", "confirmed", "shipped", "delivered", "cancelled"]
      default: "pending"

    line_items:
      type: array
      items:
        type: object
        properties:
          product_id:
            type: string
          quantity:
            type: integer
            minimum: 1
          unit_price:
            type: decimal

# Quality SLAs
quality:
  freshness:
    max_delay_minutes: 60
    check_frequency: "*/15 * * * *"  # Every 15 minutes

  completeness:
    required_fields_null_rate: 0.0
    optional_fields_null_rate: 0.05

  uniqueness:
    order_id: true
    combination: ["order_id", "line_item_id"]

  validity:
    total_amount:
      min: 0
      max: 1000000
    status:
      allowed_values: ["pending", "confirmed", "shipped", "delivered", "cancelled"]

  volume:
    min_daily_records: 1000
    max_daily_records: 1000000
    anomaly_threshold: 0.5  # 50% deviation from average

# Semantic versioning rules
versioning:
  breaking_changes:
    - removing_required_field
    - changing_field_type
    - renaming_field
  non_breaking_changes:
    - adding_optional_field
    - adding_enum_value
    - changing_description

# Consumers
consumers:
  - name: analytics-dashboard
    team: Analytics
    contact: analytics@company.com
    usage: "Daily KPI dashboards"
    required_fields: ["order_id", "customer_id", "total_amount", "created_at"]

  - name: ml-churn-prediction
    team: ML Platform
    contact: ml-team@company.com
    usage: "Customer churn prediction model"
    required_fields: ["customer_id", "created_at", "total_amount"]

  - name: finance-reporting
    team: Finance
    contact: finance@company.com
    usage: "Revenue reconciliation"
    required_fields: ["order_id", "total_amount", "status"]

# Change management
change_process:
  notification_lead_time_days: 14
  approval_required_from:
    - data-platform-lead
    - affected-consumer-teams
  rollback_plan_required: true
```

### Contract Validation

```python
# contracts/validator.py
import yaml
import json
from dataclasses import dataclass
from typing import Dict, List, Any, Optional
from datetime import datetime
import jsonschema

@dataclass
class ContractValidationResult:
    contract_name: str
    version: str
    timestamp: datetime
    passed: bool
    schema_valid: bool
    quality_checks_passed: bool
    sla_checks_passed: bool
    violations: List[Dict[str, Any]]

class ContractValidator:
    """Validate data against contract definitions."""

    def __init__(self, contract_path: str):
        with open(contract_path) as f:
            self.contract = yaml.safe_load(f)

        self.contract_name = self.contract['contract']['name']
        self.version = self.contract['contract']['version']

    def validate_schema(self, data: List[Dict]) -> List[Dict]:
        """Validate data against JSON schema."""
        violations = []
        schema = self.contract['schema']

        for i, record in enumerate(data):
            try:
                jsonschema.validate(record, schema)
            except jsonschema.ValidationError as e:
                violations.append({
                    "type": "schema_violation",
                    "record_index": i,
                    "field": e.path[0] if e.path else None,
                    "message": e.message
                })

        return violations

    def validate_quality_slas(self, connection, table_name: str) -> List[Dict]:
        """Validate quality SLAs."""
        violations = []
        quality = self.contract.get('quality', {})

        # Freshness check
        if 'freshness' in quality:
            max_delay = quality['freshness']['max_delay_minutes']
            query = f"SELECT MAX(created_at) FROM {table_name}"
            result = connection.execute(query).fetchone()
            if result[0]:
                age_minutes = (datetime.now() - result[0]).total_seconds() / 60
                if age_minutes > max_delay:
                    violations.append({
                        "type": "freshness_violation",
                        "sla": f"max_delay_minutes: {max_delay}",
                        "actual": f"{age_minutes:.0f} minutes old",
                        "severity": "critical"
                    })

        # Completeness check
        if 'completeness' in quality:
            for field in self.contract['schema'].get('required', []):
                query = f"""
                    SELECT
                        COUNT(*) as total,
                        SUM(CASE WHEN {field} IS NULL THEN 1 ELSE 0 END) as nulls
                    FROM {table_name}
                """
                result = connection.execute(query).fetchone()
                null_rate = result[1] / result[0] if result[0] > 0 else 0
                max_rate = quality['completeness']['required_fields_null_rate']
                if null_rate > max_rate:
                    violations.append({
                        "type": "completeness_violation",
                        "field": field,
                        "sla": f"null_rate <= {max_rate}",
                        "actual": f"null_rate = {null_rate:.4f}",
                        "severity": "critical"
                    })

        # Uniqueness check
        if 'uniqueness' in quality:
            for field, should_be_unique in quality['uniqueness'].items():
                if field == 'combination':
                    continue
                if should_be_unique:
                    query = f"""
                        SELECT COUNT(*) - COUNT(DISTINCT {field})
                        FROM {table_name}
                    """
                    result = connection.execute(query).fetchone()
                    if result[0] > 0:
                        violations.append({
                            "type": "uniqueness_violation",
                            "field": field,
                            "duplicates": result[0],
                            "severity": "critical"
                        })

        # Volume check
        if 'volume' in quality:
            query = f"SELECT COUNT(*) FROM {table_name} WHERE DATE(created_at) = CURRENT_DATE"
            result = connection.execute(query).fetchone()
            daily_count = result[0]

            if daily_count < quality['volume']['min_daily_records']:
                violations.append({
                    "type": "volume_violation",
                    "sla": f"min_daily_records: {quality['volume']['min_daily_records']}",
                    "actual": daily_count,
                    "severity": "warning"
                })

        return violations

    def validate(self, connection, table_name: str, sample_data: List[Dict] = None) -> ContractValidationResult:
        """Run full contract validation."""
        violations = []

        # Schema validation (on sample data)
        schema_violations = []
        if sample_data:
            schema_violations = self.validate_schema(sample_data)
            violations.extend(schema_violations)

        # Quality SLA validation
        quality_violations = self.validate_quality_slas(connection, table_name)
        violations.extend(quality_violations)

        return ContractValidationResult(
            contract_name=self.contract_name,
            version=self.version,
            timestamp=datetime.now(),
            passed=len([v for v in violations if v.get('severity') == 'critical']) == 0,
            schema_valid=len(schema_violations) == 0,
            quality_checks_passed=len([v for v in quality_violations if v.get('severity') == 'critical']) == 0,
            sla_checks_passed=True,  # Add SLA timing checks
            violations=violations
        )
```

---

## CI/CD for Data Pipelines

### GitHub Actions Workflow

```yaml
# .github/workflows/data-pipeline-ci.yml
name: Data Pipeline CI/CD

on:
  push:
    branches: [main, develop]
    paths:
      - 'dbt/**'
      - 'airflow/**'
      - 'tests/**'
  pull_request:
    branches: [main]

env:
  DBT_PROFILES_DIR: ./dbt
  SNOWFLAKE_ACCOUNT: ${{ secrets.SNOWFLAKE_ACCOUNT }}
  SNOWFLAKE_USER: ${{ secrets.SNOWFLAKE_USER }}
  SNOWFLAKE_PASSWORD: ${{ secrets.SNOWFLAKE_PASSWORD }}

jobs:
  lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: Install dependencies
        run: |
          pip install sqlfluff dbt-core dbt-snowflake

      - name: Lint SQL
        run: |
          sqlfluff lint dbt/models --dialect snowflake

      - name: Lint dbt project
        run: |
          cd dbt && dbt deps && dbt compile

  test:
    runs-on: ubuntu-latest
    needs: lint
    steps:
      - uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: Install dependencies
        run: |
          pip install dbt-core dbt-snowflake pytest great-expectations

      - name: Run dbt tests on CI schema
        run: |
          cd dbt
          dbt deps
          dbt seed --target ci
          dbt run --target ci --select state:modified+
          dbt test --target ci --select state:modified+

      - name: Run data contract tests
        run: |
          pytest tests/contracts/ -v

      - name: Run Great Expectations validation
        run: |
          great_expectations checkpoint run ci_checkpoint

  deploy-staging:
    runs-on: ubuntu-latest
    needs: test
    if: github.ref == 'refs/heads/develop'
    environment: staging
    steps:
      - uses: actions/checkout@v4

      - name: Deploy to staging
        run: |
          cd dbt
          dbt deps
          dbt run --target staging
          dbt test --target staging

      - name: Run data quality checks
        run: |
          python scripts/run_quality_checks.py --env staging

  deploy-production:
    runs-on: ubuntu-latest
    needs: test
    if: github.ref == 'refs/heads/main'
    environment: production
    steps:
      - uses: actions/checkout@v4

      - name: Deploy to production
        run: |
          cd dbt
          dbt deps
          dbt run --target prod --full-refresh-models tag:full_refresh
          dbt run --target prod
          dbt test --target prod

      - name: Notify on success
        if: success()
        run: |
          curl -X POST ${{ secrets.SLACK_WEBHOOK }} \
            -H 'Content-type: application/json' \
            -d '{"text":"dbt production deployment successful!"}'

      - name: Notify on failure
        if: failure()
        run: |
          curl -X POST ${{ secrets.SLACK_WEBHOOK }} \
            -H 'Content-type: application/json' \
            -d '{"text":"dbt production deployment FAILED!"}'
```

### dbt CI Configuration

```yaml
# dbt_project.yml
name: 'analytics'
version: '1.0.0'

config-version: 2
profile: 'analytics'

model-paths: ["models"]
analysis-paths: ["analyses"]
test-paths: ["tests"]
seed-paths: ["seeds"]
macro-paths: ["macros"]
snapshot-paths: ["snapshots"]

target-path: "target"
clean-targets: ["target", "dbt_packages"]

# Slim CI configuration
on-run-start:
  - "{{ dbt_utils.log_info('Starting dbt run') }}"

on-run-end:
  - "{{ dbt_utils.log_info('dbt run complete') }}"

vars:
  # CI testing with limited data
  ci_limit: "{{ 1000 if target.name == 'ci' else none }}"

# Model configurations
models:
  analytics:
    staging:
      +materialized: view
      +schema: staging

    intermediate:
      +materialized: ephemeral

    marts:
      +materialized: table
      +schema: marts

      core:
        +tags: ['core', 'daily']

      marketing:
        +tags: ['marketing', 'daily']
```

### Slim CI with State Comparison

```bash
# scripts/slim_ci.sh
#!/bin/bash
set -e

# Download production manifest for state comparison
aws s3 cp s3://dbt-artifacts/prod/manifest.json ./target/prod_manifest.json

# Run only modified models and their downstream dependencies
dbt run \
  --target ci \
  --select state:modified+ \
  --state ./target/prod_manifest.json

# Test only affected models
dbt test \
  --target ci \
  --select state:modified+ \
  --state ./target/prod_manifest.json

# Upload CI artifacts
dbt docs generate
aws s3 sync ./target s3://dbt-artifacts/ci/${GITHUB_SHA}/
```

---

## Observability and Lineage

### Data Lineage with OpenLineage

```python
# lineage/openlineage_emitter.py
from openlineage.client import OpenLineageClient
from openlineage.client.run import Run, RunEvent, RunState, Job, Dataset
from openlineage.client.facet import (
    SchemaDatasetFacet,
    SchemaField,
    SqlJobFacet,
    DataQualityMetricsInputDatasetFacet
)
from datetime import datetime
import uuid

class DataLineageEmitter:
    """Emit data lineage events to OpenLineage."""

    def __init__(self, api_url: str, namespace: str = "data-platform"):
        self.client = OpenLineageClient(url=api_url)
        self.namespace = namespace

    def emit_job_start(self, job_name: str, inputs: list, outputs: list,
                       sql: str = None) -> str:
        """Emit job start event."""
        run_id = str(uuid.uuid4())

        # Build input datasets
        input_datasets = [
            Dataset(
                namespace=self.namespace,
                name=inp['name'],
                facets={
                    "schema": SchemaDatasetFacet(
                        fields=[
                            SchemaField(name=f['name'], type=f['type'])
                            for f in inp.get('schema', [])
                        ]
                    )
                }
            )
            for inp in inputs
        ]

        # Build output datasets
        output_datasets = [
            Dataset(
                namespace=self.namespace,
                name=out['name'],
                facets={
                    "schema": SchemaDatasetFacet(
                        fields=[
                            SchemaField(name=f['name'], type=f['type'])
                            for f in out.get('schema', [])
                        ]
                    )
                }
            )
            for out in outputs
        ]

        # Build job facets
        job_facets = {}
        if sql:
            job_facets["sql"] = SqlJobFacet(query=sql)

        # Create and emit event
        event = RunEvent(
            eventType=RunState.START,
            eventTime=datetime.utcnow().isoformat() + "Z",
            run=Run(runId=run_id),
            job=Job(namespace=self.namespace, name=job_name, facets=job_facets),
            inputs=input_datasets,
            outputs=output_datasets
        )

        self.client.emit(event)
        return run_id

    def emit_job_complete(self, job_name: str, run_id: str,
                          output_metrics: dict = None):
        """Emit job completion event."""
        output_facets = {}
        if output_metrics:
            output_facets["dataQuality"] = DataQualityMetricsInputDatasetFacet(
                rowCount=output_metrics.get('row_count'),
                bytes=output_metrics.get('bytes')
            )

        event = RunEvent(
            eventType=RunState.COMPLETE,
            eventTime=datetime.utcnow().isoformat() + "Z",
            run=Run(runId=run_id),
            job=Job(namespace=self.namespace, name=job_name),
            inputs=[],
            outputs=[]
        )

        self.client.emit(event)

    def emit_job_fail(self, job_name: str, run_id: str, error_message: str):
        """Emit job failure event."""
        event = RunEvent(
            eventType=RunState.FAIL,
            eventTime=datetime.utcnow().isoformat() + "Z",
            run=Run(runId=run_id, facets={
                "errorMessage": {"message": error_message}
            }),
            job=Job(namespace=self.namespace, name=job_name),
            inputs=[],
            outputs=[]
        )

        self.client.emit(event)


# Usage example
emitter = DataLineageEmitter("http://marquez:5000/api/v1/lineage")

run_id = emitter.emit_job_start(
    job_name="transform_orders",
    inputs=[
        {"name": "raw.orders", "schema": [
            {"name": "id", "type": "string"},
            {"name": "amount", "type": "decimal"}
        ]}
    ],
    outputs=[
        {"name": "analytics.fct_orders", "schema": [
            {"name": "order_id", "type": "string"},
            {"name": "net_amount", "type": "decimal"}
        ]}
    ],
    sql="SELECT id as order_id, amount as net_amount FROM raw.orders"
)

# After job completes
emitter.emit_job_complete(
    job_name="transform_orders",
    run_id=run_id,
    output_metrics={"row_count": 1500000, "bytes": 125000000}
)
```

### Pipeline Monitoring with Prometheus

```python
# monitoring/metrics.py
from prometheus_client import Counter, Gauge, Histogram, start_http_server
from functools import wraps
import time

# Define metrics
PIPELINE_RUNS = Counter(
    'pipeline_runs_total',
    'Total number of pipeline runs',
    ['pipeline_name', 'status']
)

PIPELINE_DURATION = Histogram(
    'pipeline_duration_seconds',
    'Pipeline execution duration',
    ['pipeline_name'],
    buckets=[60, 300, 600, 1800, 3600, 7200]
)

ROWS_PROCESSED = Counter(
    'rows_processed_total',
    'Total rows processed by pipeline',
    ['pipeline_name', 'table_name']
)

DATA_FRESHNESS = Gauge(
    'data_freshness_hours',
    'Hours since last data update',
    ['table_name']
)

DATA_QUALITY_SCORE = Gauge(
    'data_quality_score',
    'Data quality score (0-1)',
    ['table_name', 'check_type']
)

def track_pipeline(pipeline_name: str):
    """Decorator to track pipeline execution."""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            start_time = time.time()
            try:
                result = func(*args, **kwargs)
                PIPELINE_RUNS.labels(pipeline_name=pipeline_name, status='success').inc()
                return result
            except Exception as e:
                PIPELINE_RUNS.labels(pipeline_name=pipeline_name, status='failure').inc()
                raise
            finally:
                duration = time.time() - start_time
                PIPELINE_DURATION.labels(pipeline_name=pipeline_name).observe(duration)
        return wrapper
    return decorator

def record_rows_processed(pipeline_name: str, table_name: str, row_count: int):
    """Record number of rows processed."""
    ROWS_PROCESSED.labels(pipeline_name=pipeline_name, table_name=table_name).inc(row_count)

def update_freshness(table_name: str, hours_since_update: float):
    """Update data freshness metric."""
    DATA_FRESHNESS.labels(table_name=table_name).set(hours_since_update)

def update_quality_score(table_name: str, check_type: str, score: float):
    """Update data quality score."""
    DATA_QUALITY_SCORE.labels(table_name=table_name, check_type=check_type).set(score)

# Start metrics server
if __name__ == '__main__':
    start_http_server(8000)
```

### Alerting Configuration

```yaml
# alerting/prometheus_rules.yml
groups:
  - name: data_quality_alerts
    rules:
      - alert: DataFreshnessAlert
        expr: data_freshness_hours > 24
        for: 15m
        labels:
          severity: critical
          team: data-platform
        annotations:
          summary: "Data freshness SLA violated"
          description: "Table {{ $labels.table_name }} has not been updated for {{ $value }} hours"

      - alert: DataQualityDegraded
        expr: data_quality_score < 0.95
        for: 10m
        labels:
          severity: warning
          team: data-platform
        annotations:
          summary: "Data quality below threshold"
          description: "Table {{ $labels.table_name }} quality score is {{ $value }}"

      - alert: PipelineFailure
        expr: increase(pipeline_runs_total{status="failure"}[1h]) > 0
        for: 5m
        labels:
          severity: critical
          team: data-platform
        annotations:
          summary: "Pipeline failure detected"
          description: "Pipeline {{ $labels.pipeline_name }} has failed"

      - alert: PipelineSlowdown
        expr: histogram_quantile(0.95, rate(pipeline_duration_seconds_bucket[1h])) > 3600
        for: 30m
        labels:
          severity: warning
          team: data-platform
        annotations:
          summary: "Pipeline execution time degraded"
          description: "Pipeline {{ $labels.pipeline_name }} p95 duration is {{ $value }} seconds"

      - alert: LowRowCount
        expr: increase(rows_processed_total[24h]) < 1000
        for: 1h
        labels:
          severity: warning
          team: data-platform
        annotations:
          summary: "Unusually low row count"
          description: "Pipeline {{ $labels.pipeline_name }} processed only {{ $value }} rows in 24h"
```

---

## Incident Response

### Runbook Template

```markdown
# Incident Runbook: Data Pipeline Failure

## Overview
This runbook covers procedures for handling data pipeline failures.

## Severity Levels
- **P1 (Critical)**: Data older than 24 hours, revenue-impacting
- **P2 (High)**: Data older than 4 hours, customer-facing dashboards affected
- **P3 (Medium)**: Data older than 1 hour, internal reports delayed
- **P4 (Low)**: Non-critical pipeline, no business impact

## Initial Response (First 15 minutes)

### 1. Acknowledge the Alert
```bash
# Acknowledge in PagerDuty
curl -X POST https://api.pagerduty.com/incidents/{incident_id}/acknowledge

# Post in #data-incidents Slack channel
```

### 2. Assess Impact
- Which tables are affected?
- Which downstream consumers are impacted?
- What is the data freshness currently?

```sql
-- Check data freshness
SELECT
    table_name,
    MAX(updated_at) as last_update,
    DATEDIFF(hour, MAX(updated_at), CURRENT_TIMESTAMP) as hours_stale
FROM information_schema.tables
WHERE table_schema = 'analytics'
GROUP BY table_name
ORDER BY hours_stale DESC;
```

### 3. Identify Root Cause

#### Check Pipeline Status
```bash
# Airflow
airflow dags list-runs -d <dag_id> --state failed

# dbt
dbt debug
dbt run --select state:failed

# Spark
spark-submit --status <application_id>
```

#### Common Failure Modes

| Symptom | Likely Cause | Fix |
|---------|--------------|-----|
| OOM errors | Data volume spike | Increase memory, add partitioning |
| Timeout | Slow query | Optimize query, check locks |
| Connection refused | Network/auth | Check credentials, VPC rules |
| Schema mismatch | Source change | Update schema, add contract |
| Duplicate key | Upstream bug | Deduplicate, fix source |

## Resolution Procedures

### Restart Failed Pipeline
```bash
# Clear failed Airflow task
airflow tasks clear <dag_id> -t <task_id> -s <start_date> -e <end_date>

# Rerun dbt model
dbt run --select <model_name>+

# Resubmit Spark job
spark-submit --deploy-mode cluster <job.py>
```

### Backfill Missing Data
```bash
# Airflow backfill
airflow dags backfill -s 2024-01-01 -e 2024-01-02 <dag_id>

# dbt incremental refresh
dbt run --full-refresh --select <model_name>
```

### Rollback Procedure
```bash
# dbt rollback (use previous version)
git checkout <previous_sha> -- models/<model>.sql
dbt run --select <model_name>

# Delta Lake time travel
spark.sql("""
    RESTORE TABLE analytics.orders TO VERSION AS OF 10
""")
```

## Post-Incident

### 1. Write Incident Report
- Timeline of events
- Root cause analysis
- Impact assessment
- Remediation steps taken
- Follow-up action items

### 2. Update Monitoring
- Add missing alerts
- Adjust thresholds
- Improve documentation

### 3. Share Learnings
- Post in #data-engineering
- Update runbooks
- Schedule blameless postmortem if P1/P2
```

---

## Cost Optimization

### Query Cost Analysis

```sql
-- Snowflake query cost analysis
SELECT
    query_id,
    user_name,
    warehouse_name,
    execution_time / 1000 as execution_seconds,
    bytes_scanned / 1e9 as gb_scanned,
    credits_used_cloud_services,
    query_text
FROM snowflake.account_usage.query_history
WHERE start_time > DATEADD(day, -7, CURRENT_TIMESTAMP)
ORDER BY credits_used_cloud_services DESC
LIMIT 20;

-- BigQuery cost analysis
SELECT
    user_email,
    query,
    total_bytes_processed / 1e12 as tb_processed,
    total_bytes_processed / 1e12 * 5 as estimated_cost_usd,  -- $5/TB
    creation_time
FROM `project.region-us.INFORMATION_SCHEMA.JOBS_BY_USER`
WHERE creation_time > TIMESTAMP_SUB(CURRENT_TIMESTAMP(), INTERVAL 7 DAY)
ORDER BY total_bytes_processed DESC
LIMIT 20;
```

### Cost Optimization Strategies

```python
# cost/optimizer.py
from dataclasses import dataclass
from typing import List, Dict
import pandas as pd

@dataclass
class CostRecommendation:
    category: str
    current_cost: float
    potential_savings: float
    recommendation: str
    priority: str

class CostOptimizer:
    """Analyze and optimize data platform costs."""

    def __init__(self, connection):
        self.conn = connection

    def analyze_query_costs(self) -> List[CostRecommendation]:
        """Identify expensive queries and optimization opportunities."""
        recommendations = []

        # Find queries scanning full tables
        full_scans = self.conn.execute("""
            SELECT
                query_text,
                COUNT(*) as execution_count,
                AVG(bytes_scanned) as avg_bytes,
                SUM(credits_used) as total_credits
            FROM query_history
            WHERE bytes_scanned > 1e10  -- > 10GB
              AND start_time > DATEADD(day, -7, CURRENT_TIMESTAMP)
            GROUP BY query_text
            HAVING COUNT(*) > 10
            ORDER BY total_credits DESC
        """).fetchall()

        for query, count, avg_bytes, credits in full_scans:
            recommendations.append(CostRecommendation(
                category="Query Optimization",
                current_cost=credits,
                potential_savings=credits * 0.7,  # Estimate 70% savings
                recommendation=f"Add WHERE clause or partitioning to reduce scan. Query runs {count}x/week, scans {avg_bytes/1e9:.1f}GB each time.",
                priority="high"
            ))

        return recommendations

    def analyze_storage_costs(self) -> List[CostRecommendation]:
        """Identify storage optimization opportunities."""
        recommendations = []

        # Find large unused tables
        unused_tables = self.conn.execute("""
            SELECT
                table_name,
                bytes / 1e9 as size_gb,
                last_accessed
            FROM table_metadata
            WHERE last_accessed < DATEADD(day, -90, CURRENT_TIMESTAMP)
              AND bytes > 1e9  -- > 1GB
            ORDER BY bytes DESC
        """).fetchall()

        for table, size, last_accessed in unused_tables:
            monthly_cost = size * 0.023  # $0.023/GB/month for S3
            recommendations.append(CostRecommendation(
                category="Storage",
                current_cost=monthly_cost,
                potential_savings=monthly_cost,
                recommendation=f"Table {table} ({size:.1f}GB) not accessed since {last_accessed}. Consider archiving or deleting.",
                priority="medium"
            ))

        # Find tables without partitioning
        unpartitioned = self.conn.execute("""
            SELECT table_name, bytes / 1e9 as size_gb
            FROM table_metadata
            WHERE partition_column IS NULL
              AND bytes > 10e9  -- > 10GB
        """).fetchall()

        for table, size in unpartitioned:
            recommendations.append(CostRecommendation(
                category="Storage",
                current_cost=0,
                potential_savings=size * 0.1,  # Estimate 10% query cost savings
                recommendation=f"Table {table} ({size:.1f}GB) is not partitioned. Add partitioning to reduce query costs.",
                priority="high"
            ))

        return recommendations

    def analyze_compute_costs(self) -> List[CostRecommendation]:
        """Identify compute optimization opportunities."""
        recommendations = []

        # Find oversized warehouses
        warehouse_util = self.conn.execute("""
            SELECT
                warehouse_name,
                warehouse_size,
                AVG(avg_running_queries) as avg_queries,
                AVG(credits_used) as avg_credits
            FROM warehouse_metering_history
            WHERE start_time > DATEADD(day, -7, CURRENT_TIMESTAMP)
            GROUP BY warehouse_name, warehouse_size
        """).fetchall()

        for wh, size, avg_queries, avg_credits in warehouse_util:
            if avg_queries < 1 and size not in ['X-Small', 'Small']:
                recommendations.append(CostRecommendation(
                    category="Compute",
                    current_cost=avg_credits * 7,  # Weekly
                    potential_savings=avg_credits * 7 * 0.5,
                    recommendation=f"Warehouse {wh} ({size}) has low utilization ({avg_queries:.1f} avg queries). Consider downsizing.",
                    priority="high"
                ))

        return recommendations

    def generate_report(self) -> Dict:
        """Generate comprehensive cost optimization report."""
        all_recommendations = (
            self.analyze_query_costs() +
            self.analyze_storage_costs() +
            self.analyze_compute_costs()
        )

        total_current = sum(r.current_cost for r in all_recommendations)
        total_savings = sum(r.potential_savings for r in all_recommendations)

        return {
            "total_current_monthly_cost": total_current,
            "total_potential_savings": total_savings,
            "savings_percentage": total_savings / total_current * 100 if total_current > 0 else 0,
            "recommendations": [
                {
                    "category": r.category,
                    "current_cost": r.current_cost,
                    "potential_savings": r.potential_savings,
                    "recommendation": r.recommendation,
                    "priority": r.priority
                }
                for r in sorted(all_recommendations, key=lambda x: -x.potential_savings)
            ]
        }
```
