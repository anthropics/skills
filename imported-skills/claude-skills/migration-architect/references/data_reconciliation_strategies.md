# Data Reconciliation Strategies

## Overview

Data reconciliation is the process of ensuring data consistency and integrity across systems during and after migrations. This document provides comprehensive strategies, tools, and implementation patterns for detecting, measuring, and correcting data discrepancies in migration scenarios.

## Core Principles

### 1. Eventually Consistent
Accept that perfect real-time consistency may not be achievable during migrations, but ensure eventual consistency through reconciliation processes.

### 2. Idempotent Operations
All reconciliation operations must be safe to run multiple times without causing additional issues.

### 3. Audit Trail
Maintain detailed logs of all reconciliation actions for compliance and debugging.

### 4. Non-Destructive
Reconciliation should prefer addition over deletion, and always maintain backups before corrections.

## Types of Data Inconsistencies

### 1. Missing Records
Records that exist in source but not in target system.

### 2. Extra Records
Records that exist in target but not in source system.

### 3. Field Mismatches
Records exist in both systems but with different field values.

### 4. Referential Integrity Violations
Foreign key relationships that are broken during migration.

### 5. Temporal Inconsistencies
Data with incorrect timestamps or ordering.

### 6. Schema Drift
Structural differences between source and target schemas.

## Detection Strategies

### 1. Row Count Validation

#### Simple Count Comparison
```sql
-- Compare total row counts
SELECT 
    'source' as system, 
    COUNT(*) as row_count 
FROM source_table
UNION ALL
SELECT 
    'target' as system, 
    COUNT(*) as row_count 
FROM target_table;
```

#### Filtered Count Comparison
```sql
-- Compare counts with business logic filters
WITH source_counts AS (
    SELECT 
        status,
        created_date::date as date,
        COUNT(*) as count
    FROM source_orders
    WHERE created_date >= '2024-01-01'
    GROUP BY status, created_date::date
),
target_counts AS (
    SELECT 
        status,
        created_date::date as date,
        COUNT(*) as count
    FROM target_orders
    WHERE created_date >= '2024-01-01'
    GROUP BY status, created_date::date
)
SELECT 
    COALESCE(s.status, t.status) as status,
    COALESCE(s.date, t.date) as date,
    COALESCE(s.count, 0) as source_count,
    COALESCE(t.count, 0) as target_count,
    COALESCE(s.count, 0) - COALESCE(t.count, 0) as difference
FROM source_counts s
FULL OUTER JOIN target_counts t 
    ON s.status = t.status AND s.date = t.date
WHERE COALESCE(s.count, 0) != COALESCE(t.count, 0);
```

### 2. Checksum-Based Validation

#### Record-Level Checksums
```python
import hashlib
import json

class RecordChecksum:
    def __init__(self, exclude_fields=None):
        self.exclude_fields = exclude_fields or ['updated_at', 'version']
    
    def calculate_checksum(self, record):
        """Calculate MD5 checksum for a database record"""
        # Remove excluded fields and sort for consistency
        filtered_record = {
            k: v for k, v in record.items() 
            if k not in self.exclude_fields
        }
        
        # Convert to sorted JSON string for consistent hashing
        normalized = json.dumps(filtered_record, sort_keys=True, default=str)
        
        return hashlib.md5(normalized.encode('utf-8')).hexdigest()
    
    def compare_records(self, source_record, target_record):
        """Compare two records using checksums"""
        source_checksum = self.calculate_checksum(source_record)
        target_checksum = self.calculate_checksum(target_record)
        
        return {
            'match': source_checksum == target_checksum,
            'source_checksum': source_checksum,
            'target_checksum': target_checksum
        }

# Usage example
checksum_calculator = RecordChecksum(exclude_fields=['updated_at', 'migration_flag'])

source_records = fetch_records_from_source()
target_records = fetch_records_from_target()

mismatches = []
for source_id, source_record in source_records.items():
    if source_id in target_records:
        comparison = checksum_calculator.compare_records(
            source_record, target_records[source_id]
        )
        if not comparison['match']:
            mismatches.append({
                'record_id': source_id,
                'source_checksum': comparison['source_checksum'],
                'target_checksum': comparison['target_checksum']
            })
```

#### Aggregate Checksums
```sql
-- Calculate aggregate checksums for data validation
WITH source_aggregates AS (
    SELECT 
        DATE_TRUNC('day', created_at) as day,
        status,
        COUNT(*) as record_count,
        SUM(amount) as total_amount,
        MD5(STRING_AGG(CAST(id AS VARCHAR) || ':' || CAST(amount AS VARCHAR), '|' ORDER BY id)) as checksum
    FROM source_transactions
    GROUP BY DATE_TRUNC('day', created_at), status
),
target_aggregates AS (
    SELECT 
        DATE_TRUNC('day', created_at) as day,
        status,
        COUNT(*) as record_count,
        SUM(amount) as total_amount,
        MD5(STRING_AGG(CAST(id AS VARCHAR) || ':' || CAST(amount AS VARCHAR), '|' ORDER BY id)) as checksum
    FROM target_transactions
    GROUP BY DATE_TRUNC('day', created_at), status
)
SELECT 
    COALESCE(s.day, t.day) as day,
    COALESCE(s.status, t.status) as status,
    COALESCE(s.record_count, 0) as source_count,
    COALESCE(t.record_count, 0) as target_count,
    COALESCE(s.total_amount, 0) as source_amount,
    COALESCE(t.total_amount, 0) as target_amount,
    s.checksum as source_checksum,
    t.checksum as target_checksum,
    CASE WHEN s.checksum = t.checksum THEN 'MATCH' ELSE 'MISMATCH' END as status
FROM source_aggregates s
FULL OUTER JOIN target_aggregates t 
    ON s.day = t.day AND s.status = t.status
WHERE s.checksum != t.checksum OR s.checksum IS NULL OR t.checksum IS NULL;
```

### 3. Delta Detection

#### Change Data Capture (CDC) Based
```python
class CDCReconciler:
    def __init__(self, kafka_client, database_client):
        self.kafka = kafka_client
        self.db = database_client
        self.processed_changes = set()
    
    def process_cdc_stream(self, topic_name):
        """Process CDC events and track changes for reconciliation"""
        
        consumer = self.kafka.consumer(topic_name)
        
        for message in consumer:
            change_event = json.loads(message.value)
            
            change_id = f"{change_event['table']}:{change_event['key']}:{change_event['timestamp']}"
            
            if change_id in self.processed_changes:
                continue  # Skip duplicate events
            
            try:
                self.apply_change(change_event)
                self.processed_changes.add(change_id)
                
                # Commit offset only after successful processing
                consumer.commit()
                
            except Exception as e:
                # Log failure and continue - will be caught by reconciliation
                self.log_processing_failure(change_id, str(e))
    
    def apply_change(self, change_event):
        """Apply CDC change to target system"""
        
        table = change_event['table']
        operation = change_event['operation']
        key = change_event['key']
        data = change_event.get('data', {})
        
        if operation == 'INSERT':
            self.db.insert(table, data)
        elif operation == 'UPDATE':
            self.db.update(table, key, data)
        elif operation == 'DELETE':
            self.db.delete(table, key)
    
    def reconcile_missed_changes(self, start_timestamp, end_timestamp):
        """Find and apply changes that may have been missed"""
        
        # Query source database for changes in time window
        source_changes = self.db.get_changes_in_window(
            start_timestamp, end_timestamp
        )
        
        missed_changes = []
        
        for change in source_changes:
            change_id = f"{change['table']}:{change['key']}:{change['timestamp']}"
            
            if change_id not in self.processed_changes:
                missed_changes.append(change)
        
        # Apply missed changes
        for change in missed_changes:
            try:
                self.apply_change(change)
                print(f"Applied missed change: {change['table']}:{change['key']}")
            except Exception as e:
                print(f"Failed to apply missed change: {e}")
```

### 4. Business Logic Validation

#### Critical Business Rules Validation
```python
class BusinessLogicValidator:
    def __init__(self, source_db, target_db):
        self.source_db = source_db
        self.target_db = target_db
    
    def validate_financial_consistency(self):
        """Validate critical financial calculations"""
        
        validation_rules = [
            {
                'name': 'daily_transaction_totals',
                'source_query': """
                    SELECT DATE(created_at) as date, SUM(amount) as total
                    FROM source_transactions
                    WHERE created_at >= CURRENT_DATE - INTERVAL '30 days'
                    GROUP BY DATE(created_at)
                """,
                'target_query': """
                    SELECT DATE(created_at) as date, SUM(amount) as total
                    FROM target_transactions
                    WHERE created_at >= CURRENT_DATE - INTERVAL '30 days'
                    GROUP BY DATE(created_at)
                """,
                'tolerance': 0.01  # Allow $0.01 difference for rounding
            },
            {
                'name': 'customer_balance_totals',
                'source_query': """
                    SELECT customer_id, SUM(balance) as total_balance
                    FROM source_accounts
                    GROUP BY customer_id
                    HAVING SUM(balance) > 0
                """,
                'target_query': """
                    SELECT customer_id, SUM(balance) as total_balance
                    FROM target_accounts
                    GROUP BY customer_id
                    HAVING SUM(balance) > 0
                """,
                'tolerance': 0.01
            }
        ]
        
        validation_results = []
        
        for rule in validation_rules:
            source_data = self.source_db.execute_query(rule['source_query'])
            target_data = self.target_db.execute_query(rule['target_query'])
            
            differences = self.compare_financial_data(
                source_data, target_data, rule['tolerance']
            )
            
            validation_results.append({
                'rule_name': rule['name'],
                'differences_found': len(differences),
                'differences': differences[:10],  # First 10 differences
                'status': 'PASS' if len(differences) == 0 else 'FAIL'
            })
        
        return validation_results
    
    def compare_financial_data(self, source_data, target_data, tolerance):
        """Compare financial data with tolerance for rounding differences"""
        
        source_dict = {
            tuple(row[:-1]): row[-1] for row in source_data
        }  # Last column is the amount
        
        target_dict = {
            tuple(row[:-1]): row[-1] for row in target_data
        }
        
        differences = []
        
        # Check for missing records and value differences
        for key, source_value in source_dict.items():
            if key not in target_dict:
                differences.append({
                    'key': key,
                    'source_value': source_value,
                    'target_value': None,
                    'difference_type': 'MISSING_IN_TARGET'
                })
            else:
                target_value = target_dict[key]
                if abs(float(source_value) - float(target_value)) > tolerance:
                    differences.append({
                        'key': key,
                        'source_value': source_value,
                        'target_value': target_value,
                        'difference': float(source_value) - float(target_value),
                        'difference_type': 'VALUE_MISMATCH'
                    })
        
        # Check for extra records in target
        for key, target_value in target_dict.items():
            if key not in source_dict:
                differences.append({
                    'key': key,
                    'source_value': None,
                    'target_value': target_value,
                    'difference_type': 'EXTRA_IN_TARGET'
                })
        
        return differences
```

## Correction Strategies

### 1. Automated Correction

#### Missing Record Insertion
```python
class AutoCorrector:
    def __init__(self, source_db, target_db, dry_run=True):
        self.source_db = source_db
        self.target_db = target_db
        self.dry_run = dry_run
        self.correction_log = []
    
    def correct_missing_records(self, table_name, key_field):
        """Add missing records from source to target"""
        
        # Find records in source but not in target
        missing_query = f"""
            SELECT s.* 
            FROM source_{table_name} s
            LEFT JOIN target_{table_name} t ON s.{key_field} = t.{key_field}
            WHERE t.{key_field} IS NULL
        """
        
        missing_records = self.source_db.execute_query(missing_query)
        
        for record in missing_records:
            correction = {
                'table': table_name,
                'operation': 'INSERT',
                'key': record[key_field],
                'data': record,
                'timestamp': datetime.utcnow()
            }
            
            if not self.dry_run:
                try:
                    self.target_db.insert(table_name, record)
                    correction['status'] = 'SUCCESS'
                except Exception as e:
                    correction['status'] = 'FAILED'
                    correction['error'] = str(e)
            else:
                correction['status'] = 'DRY_RUN'
            
            self.correction_log.append(correction)
        
        return len(missing_records)
    
    def correct_field_mismatches(self, table_name, key_field, fields_to_correct):
        """Correct field value mismatches"""
        
        mismatch_query = f"""
            SELECT s.{key_field}, {', '.join([f's.{f} as source_{f}, t.{f} as target_{f}' for f in fields_to_correct])}
            FROM source_{table_name} s
            JOIN target_{table_name} t ON s.{key_field} = t.{key_field}
            WHERE {' OR '.join([f's.{f} != t.{f}' for f in fields_to_correct])}
        """
        
        mismatched_records = self.source_db.execute_query(mismatch_query)
        
        for record in mismatched_records:
            key_value = record[key_field]
            updates = {}
            
            for field in fields_to_correct:
                source_value = record[f'source_{field}']
                target_value = record[f'target_{field}']
                
                if source_value != target_value:
                    updates[field] = source_value
            
            if updates:
                correction = {
                    'table': table_name,
                    'operation': 'UPDATE',
                    'key': key_value,
                    'updates': updates,
                    'timestamp': datetime.utcnow()
                }
                
                if not self.dry_run:
                    try:
                        self.target_db.update(table_name, {key_field: key_value}, updates)
                        correction['status'] = 'SUCCESS'
                    except Exception as e:
                        correction['status'] = 'FAILED'
                        correction['error'] = str(e)
                else:
                    correction['status'] = 'DRY_RUN'
                
                self.correction_log.append(correction)
        
        return len(mismatched_records)
```

### 2. Manual Review Process

#### Correction Workflow
```python
class ManualReviewSystem:
    def __init__(self, database_client):
        self.db = database_client
        self.review_queue = []
    
    def queue_for_review(self, discrepancy):
        """Add discrepancy to manual review queue"""
        
        review_item = {
            'id': str(uuid.uuid4()),
            'discrepancy_type': discrepancy['type'],
            'table': discrepancy['table'],
            'record_key': discrepancy['key'],
            'source_data': discrepancy.get('source_data'),
            'target_data': discrepancy.get('target_data'),
            'description': discrepancy['description'],
            'severity': discrepancy.get('severity', 'medium'),
            'status': 'PENDING',
            'created_at': datetime.utcnow(),
            'reviewed_by': None,
            'reviewed_at': None,
            'resolution': None
        }
        
        self.review_queue.append(review_item)
        
        # Persist to review database
        self.db.insert('manual_review_queue', review_item)
        
        return review_item['id']
    
    def process_review(self, review_id, reviewer, action, notes=None):
        """Process manual review decision"""
        
        review_item = self.get_review_item(review_id)
        
        if not review_item:
            raise ValueError(f"Review item {review_id} not found")
        
        review_item.update({
            'status': 'REVIEWED',
            'reviewed_by': reviewer,
            'reviewed_at': datetime.utcnow(),
            'resolution': {
                'action': action,  # 'APPLY_SOURCE', 'KEEP_TARGET', 'CUSTOM_FIX'
                'notes': notes
            }
        })
        
        # Apply the resolution
        if action == 'APPLY_SOURCE':
            self.apply_source_data(review_item)
        elif action == 'KEEP_TARGET':
            pass  # No action needed
        elif action == 'CUSTOM_FIX':
            # Custom fix would be applied separately
            pass
        
        # Update review record
        self.db.update('manual_review_queue', 
                      {'id': review_id}, 
                      review_item)
        
        return review_item
    
    def generate_review_report(self):
        """Generate summary report of manual reviews"""
        
        reviews = self.db.query("""
            SELECT 
                discrepancy_type,
                severity,
                status,
                COUNT(*) as count,
                MIN(created_at) as oldest_review,
                MAX(created_at) as newest_review
            FROM manual_review_queue
            GROUP BY discrepancy_type, severity, status
            ORDER BY severity DESC, discrepancy_type
        """)
        
        return reviews
```

### 3. Reconciliation Scheduling

#### Automated Reconciliation Jobs
```python
import schedule
import time
from datetime import datetime, timedelta

class ReconciliationScheduler:
    def __init__(self, reconciler):
        self.reconciler = reconciler
        self.job_history = []
    
    def setup_schedules(self):
        """Set up automated reconciliation schedules"""
        
        # Quick reconciliation every 15 minutes during migration
        schedule.every(15).minutes.do(self.quick_reconciliation)
        
        # Comprehensive reconciliation every 4 hours
        schedule.every(4).hours.do(self.comprehensive_reconciliation)
        
        # Deep validation daily
        schedule.every().day.at("02:00").do(self.deep_validation)
        
        # Weekly business logic validation
        schedule.every().sunday.at("03:00").do(self.business_logic_validation)
    
    def quick_reconciliation(self):
        """Quick count-based reconciliation"""
        
        job_start = datetime.utcnow()
        
        try:
            # Check critical tables only
            critical_tables = [
                'transactions', 'orders', 'customers', 'accounts'
            ]
            
            results = []
            for table in critical_tables:
                count_diff = self.reconciler.check_row_counts(table)
                if abs(count_diff) > 0:
                    results.append({
                        'table': table,
                        'count_difference': count_diff,
                        'severity': 'high' if abs(count_diff) > 100 else 'medium'
                    })
            
            job_result = {
                'job_type': 'quick_reconciliation',
                'start_time': job_start,
                'end_time': datetime.utcnow(),
                'status': 'completed',
                'issues_found': len(results),
                'details': results
            }
            
            # Alert if significant issues found
            if any(r['severity'] == 'high' for r in results):
                self.send_alert(job_result)
        
        except Exception as e:
            job_result = {
                'job_type': 'quick_reconciliation',
                'start_time': job_start,
                'end_time': datetime.utcnow(),
                'status': 'failed',
                'error': str(e)
            }
        
        self.job_history.append(job_result)
    
    def comprehensive_reconciliation(self):
        """Comprehensive checksum-based reconciliation"""
        
        job_start = datetime.utcnow()
        
        try:
            tables_to_check = self.get_migration_tables()
            issues = []
            
            for table in tables_to_check:
                # Sample-based checksum validation
                sample_issues = self.reconciler.validate_sample_checksums(
                    table, sample_size=1000
                )
                issues.extend(sample_issues)
            
            # Auto-correct simple issues
            auto_corrections = 0
            for issue in issues:
                if issue['auto_correctable']:
                    self.reconciler.auto_correct_issue(issue)
                    auto_corrections += 1
                else:
                    # Queue for manual review
                    self.reconciler.queue_for_manual_review(issue)
            
            job_result = {
                'job_type': 'comprehensive_reconciliation',
                'start_time': job_start,
                'end_time': datetime.utcnow(),
                'status': 'completed',
                'total_issues': len(issues),
                'auto_corrections': auto_corrections,
                'manual_reviews_queued': len(issues) - auto_corrections
            }
        
        except Exception as e:
            job_result = {
                'job_type': 'comprehensive_reconciliation',
                'start_time': job_start,
                'end_time': datetime.utcnow(),
                'status': 'failed',
                'error': str(e)
            }
        
        self.job_history.append(job_result)
    
    def run_scheduler(self):
        """Run the reconciliation scheduler"""
        
        print("Starting reconciliation scheduler...")
        
        while True:
            schedule.run_pending()
            time.sleep(60)  # Check every minute
```

## Monitoring and Reporting

### 1. Reconciliation Metrics

```python
class ReconciliationMetrics:
    def __init__(self, prometheus_client):
        self.prometheus = prometheus_client
        
        # Define metrics
        self.inconsistencies_found = Counter(
            'reconciliation_inconsistencies_total',
            'Number of inconsistencies found',
            ['table', 'type', 'severity']
        )
        
        self.reconciliation_duration = Histogram(
            'reconciliation_duration_seconds',
            'Time spent on reconciliation jobs',
            ['job_type']
        )
        
        self.auto_corrections = Counter(
            'reconciliation_auto_corrections_total',
            'Number of automatically corrected inconsistencies',
            ['table', 'correction_type']
        )
        
        self.data_drift_gauge = Gauge(
            'data_drift_percentage',
            'Percentage of records with inconsistencies',
            ['table']
        )
    
    def record_inconsistency(self, table, inconsistency_type, severity):
        """Record a found inconsistency"""
        self.inconsistencies_found.labels(
            table=table,
            type=inconsistency_type,
            severity=severity
        ).inc()
    
    def record_auto_correction(self, table, correction_type):
        """Record an automatic correction"""
        self.auto_corrections.labels(
            table=table,
            correction_type=correction_type
        ).inc()
    
    def update_data_drift(self, table, drift_percentage):
        """Update data drift gauge"""
        self.data_drift_gauge.labels(table=table).set(drift_percentage)
    
    def record_job_duration(self, job_type, duration_seconds):
        """Record reconciliation job duration"""
        self.reconciliation_duration.labels(job_type=job_type).observe(duration_seconds)
```

### 2. Alerting Rules

```yaml
# Prometheus alerting rules for data reconciliation
groups:
  - name: data_reconciliation
    rules:
    - alert: HighDataInconsistency
      expr: reconciliation_inconsistencies_total > 100
      for: 5m
      labels:
        severity: critical
      annotations:
        summary: "High number of data inconsistencies detected"
        description: "{{ $value }} inconsistencies found in the last 5 minutes"
    
    - alert: DataDriftHigh
      expr: data_drift_percentage > 5
      for: 10m
      labels:
        severity: warning
      annotations:
        summary: "Data drift percentage is high"
        description: "{{ $labels.table }} has {{ $value }}% data drift"
    
    - alert: ReconciliationJobFailed
      expr: up{job="reconciliation"} == 0
      for: 2m
      labels:
        severity: critical
      annotations:
        summary: "Reconciliation job is down"
        description: "The data reconciliation service is not responding"
    
    - alert: AutoCorrectionRateHigh
      expr: rate(reconciliation_auto_corrections_total[10m]) > 10
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "High rate of automatic corrections"
        description: "Auto-correction rate is {{ $value }} per second"
```

### 3. Dashboard and Reporting

```python
class ReconciliationDashboard:
    def __init__(self, database_client, metrics_client):
        self.db = database_client
        self.metrics = metrics_client
    
    def generate_daily_report(self, date=None):
        """Generate daily reconciliation report"""
        
        if not date:
            date = datetime.utcnow().date()
        
        # Query reconciliation results for the day
        daily_stats = self.db.query("""
            SELECT 
                table_name,
                inconsistency_type,
                COUNT(*) as count,
                AVG(CASE WHEN resolution = 'AUTO_CORRECTED' THEN 1 ELSE 0 END) as auto_correction_rate
            FROM reconciliation_log
            WHERE DATE(created_at) = %s
            GROUP BY table_name, inconsistency_type
        """, (date,))
        
        # Generate summary
        summary = {
            'date': date.isoformat(),
            'total_inconsistencies': sum(row['count'] for row in daily_stats),
            'auto_correction_rate': sum(row['auto_correction_rate'] * row['count'] for row in daily_stats) / max(sum(row['count'] for row in daily_stats), 1),
            'tables_affected': len(set(row['table_name'] for row in daily_stats)),
            'details_by_table': {}
        }
        
        # Group by table
        for row in daily_stats:
            table = row['table_name']
            if table not in summary['details_by_table']:
                summary['details_by_table'][table] = []
            
            summary['details_by_table'][table].append({
                'inconsistency_type': row['inconsistency_type'],
                'count': row['count'],
                'auto_correction_rate': row['auto_correction_rate']
            })
        
        return summary
    
    def generate_trend_analysis(self, days=7):
        """Generate trend analysis for reconciliation metrics"""
        
        end_date = datetime.utcnow().date()
        start_date = end_date - timedelta(days=days)
        
        trends = self.db.query("""
            SELECT 
                DATE(created_at) as date,
                table_name,
                COUNT(*) as inconsistencies,
                AVG(CASE WHEN resolution = 'AUTO_CORRECTED' THEN 1 ELSE 0 END) as auto_correction_rate
            FROM reconciliation_log
            WHERE DATE(created_at) BETWEEN %s AND %s
            GROUP BY DATE(created_at), table_name
            ORDER BY date, table_name
        """, (start_date, end_date))
        
        # Calculate trends
        trend_analysis = {
            'period': f"{start_date} to {end_date}",
            'trends': {},
            'overall_trend': 'stable'
        }
        
        for table in set(row['table_name'] for row in trends):
            table_data = [row for row in trends if row['table_name'] == table]
            
            if len(table_data) >= 2:
                first_count = table_data[0]['inconsistencies']
                last_count = table_data[-1]['inconsistencies']
                
                if last_count > first_count * 1.2:
                    trend = 'increasing'
                elif last_count < first_count * 0.8:
                    trend = 'decreasing'
                else:
                    trend = 'stable'
                
                trend_analysis['trends'][table] = {
                    'direction': trend,
                    'first_day_count': first_count,
                    'last_day_count': last_count,
                    'change_percentage': ((last_count - first_count) / max(first_count, 1)) * 100
                }
        
        return trend_analysis
```

## Advanced Reconciliation Techniques

### 1. Machine Learning-Based Anomaly Detection

```python
from sklearn.isolation import IsolationForest
from sklearn.preprocessing import StandardScaler
import numpy as np

class MLAnomalyDetector:
    def __init__(self):
        self.models = {}
        self.scalers = {}
    
    def train_anomaly_detector(self, table_name, training_data):
        """Train anomaly detection model for a specific table"""
        
        # Prepare features (convert records to numerical features)
        features = self.extract_features(training_data)
        
        # Scale features
        scaler = StandardScaler()
        scaled_features = scaler.fit_transform(features)
        
        # Train isolation forest
        model = IsolationForest(contamination=0.05, random_state=42)
        model.fit(scaled_features)
        
        # Store model and scaler
        self.models[table_name] = model
        self.scalers[table_name] = scaler
    
    def detect_anomalies(self, table_name, data):
        """Detect anomalous records that may indicate reconciliation issues"""
        
        if table_name not in self.models:
            raise ValueError(f"No trained model for table {table_name}")
        
        # Extract features
        features = self.extract_features(data)
        
        # Scale features
        scaled_features = self.scalers[table_name].transform(features)
        
        # Predict anomalies
        anomaly_scores = self.models[table_name].decision_function(scaled_features)
        anomaly_predictions = self.models[table_name].predict(scaled_features)
        
        # Return anomalous records with scores
        anomalies = []
        for i, (record, score, is_anomaly) in enumerate(zip(data, anomaly_scores, anomaly_predictions)):
            if is_anomaly == -1:  # Isolation forest returns -1 for anomalies
                anomalies.append({
                    'record_index': i,
                    'record': record,
                    'anomaly_score': score,
                    'severity': 'high' if score < -0.5 else 'medium'
                })
        
        return anomalies
    
    def extract_features(self, data):
        """Extract numerical features from database records"""
        
        features = []
        
        for record in data:
            record_features = []
            
            for key, value in record.items():
                if isinstance(value, (int, float)):
                    record_features.append(value)
                elif isinstance(value, str):
                    # Convert string to hash-based feature
                    record_features.append(hash(value) % 10000)
                elif isinstance(value, datetime):
                    # Convert datetime to timestamp
                    record_features.append(value.timestamp())
                else:
                    # Default value for other types
                    record_features.append(0)
            
            features.append(record_features)
        
        return np.array(features)
```

### 2. Probabilistic Reconciliation

```python
import random
from typing import List, Dict, Tuple

class ProbabilisticReconciler:
    def __init__(self, confidence_threshold=0.95):
        self.confidence_threshold = confidence_threshold
    
    def statistical_sampling_validation(self, table_name: str, population_size: int) -> Dict:
        """Use statistical sampling to validate large datasets"""
        
        # Calculate sample size for 95% confidence, 5% margin of error
        confidence_level = 0.95
        margin_of_error = 0.05
        
        z_score = 1.96  # for 95% confidence
        p = 0.5  # assume 50% error rate for maximum sample size
        
        sample_size = (z_score ** 2 * p * (1 - p)) / (margin_of_error ** 2)
        
        if population_size < 10000:
            # Finite population correction
            sample_size = sample_size / (1 + (sample_size - 1) / population_size)
        
        sample_size = min(int(sample_size), population_size)
        
        # Generate random sample
        sample_ids = self.generate_random_sample(table_name, sample_size)
        
        # Validate sample
        sample_results = self.validate_sample_records(table_name, sample_ids)
        
        # Calculate population estimates
        error_rate = sample_results['errors'] / sample_size
        estimated_errors = int(population_size * error_rate)
        
        # Calculate confidence interval
        standard_error = (error_rate * (1 - error_rate) / sample_size) ** 0.5
        margin_of_error_actual = z_score * standard_error
        
        confidence_interval = (
            max(0, error_rate - margin_of_error_actual),
            min(1, error_rate + margin_of_error_actual)
        )
        
        return {
            'table_name': table_name,
            'population_size': population_size,
            'sample_size': sample_size,
            'sample_error_rate': error_rate,
            'estimated_total_errors': estimated_errors,
            'confidence_interval': confidence_interval,
            'confidence_level': confidence_level,
            'recommendation': self.generate_recommendation(error_rate, confidence_interval)
        }
    
    def generate_random_sample(self, table_name: str, sample_size: int) -> List[int]:
        """Generate random sample of record IDs"""
        
        # Get total record count and ID range
        id_range = self.db.query(f"SELECT MIN(id), MAX(id) FROM {table_name}")[0]
        min_id, max_id = id_range
        
        # Generate random IDs
        sample_ids = []
        attempts = 0
        max_attempts = sample_size * 10  # Avoid infinite loop
        
        while len(sample_ids) < sample_size and attempts < max_attempts:
            candidate_id = random.randint(min_id, max_id)
            
            # Check if ID exists
            exists = self.db.query(f"SELECT 1 FROM {table_name} WHERE id = %s", (candidate_id,))
            
            if exists and candidate_id not in sample_ids:
                sample_ids.append(candidate_id)
            
            attempts += 1
        
        return sample_ids
    
    def validate_sample_records(self, table_name: str, sample_ids: List[int]) -> Dict:
        """Validate a sample of records"""
        
        validation_results = {
            'total_checked': len(sample_ids),
            'errors': 0,
            'error_details': []
        }
        
        for record_id in sample_ids:
            # Get record from both source and target
            source_record = self.source_db.get_record(table_name, record_id)
            target_record = self.target_db.get_record(table_name, record_id)
            
            if not target_record:
                validation_results['errors'] += 1
                validation_results['error_details'].append({
                    'id': record_id,
                    'error_type': 'MISSING_IN_TARGET'
                })
            elif not self.records_match(source_record, target_record):
                validation_results['errors'] += 1
                validation_results['error_details'].append({
                    'id': record_id,
                    'error_type': 'DATA_MISMATCH',
                    'differences': self.find_differences(source_record, target_record)
                })
        
        return validation_results
    
    def generate_recommendation(self, error_rate: float, confidence_interval: Tuple[float, float]) -> str:
        """Generate recommendation based on error rate and confidence"""
        
        if confidence_interval[1] < 0.01:  # Less than 1% error rate with confidence
            return "Data quality is excellent. Continue with normal reconciliation schedule."
        elif confidence_interval[1] < 0.05:  # Less than 5% error rate with confidence
            return "Data quality is acceptable. Monitor closely and investigate sample errors."
        elif confidence_interval[0] > 0.1:  # More than 10% error rate with confidence
            return "Data quality is poor. Immediate comprehensive reconciliation required."
        else:
            return "Data quality is uncertain. Increase sample size for better estimates."
```

## Performance Optimization

### 1. Parallel Processing

```python
import asyncio
import multiprocessing as mp
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor

class ParallelReconciler:
    def __init__(self, max_workers=None):
        self.max_workers = max_workers or mp.cpu_count()
    
    async def parallel_table_reconciliation(self, tables: List[str]):
        """Reconcile multiple tables in parallel"""
        
        async with asyncio.Semaphore(self.max_workers):
            tasks = [
                self.reconcile_table_async(table) 
                for table in tables
            ]
            
            results = await asyncio.gather(*tasks, return_exceptions=True)
            
            # Process results
            summary = {
                'total_tables': len(tables),
                'successful': 0,
                'failed': 0,
                'results': {}
            }
            
            for table, result in zip(tables, results):
                if isinstance(result, Exception):
                    summary['failed'] += 1
                    summary['results'][table] = {
                        'status': 'failed',
                        'error': str(result)
                    }
                else:
                    summary['successful'] += 1
                    summary['results'][table] = result
            
            return summary
    
    def parallel_chunk_processing(self, table_name: str, chunk_size: int = 10000):
        """Process table reconciliation in parallel chunks"""
        
        # Get total record count
        total_records = self.db.get_record_count(table_name)
        num_chunks = (total_records + chunk_size - 1) // chunk_size
        
        # Create chunk specifications
        chunks = []
        for i in range(num_chunks):
            start_id = i * chunk_size
            end_id = min((i + 1) * chunk_size - 1, total_records - 1)
            chunks.append({
                'table': table_name,
                'start_id': start_id,
                'end_id': end_id,
                'chunk_number': i + 1
            })
        
        # Process chunks in parallel
        with ProcessPoolExecutor(max_workers=self.max_workers) as executor:
            chunk_results = list(executor.map(self.process_chunk, chunks))
        
        # Aggregate results
        total_inconsistencies = sum(r['inconsistencies'] for r in chunk_results)
        total_corrections = sum(r['corrections'] for r in chunk_results)
        
        return {
            'table': table_name,
            'total_records': total_records,
            'chunks_processed': len(chunks),
            'total_inconsistencies': total_inconsistencies,
            'total_corrections': total_corrections,
            'chunk_details': chunk_results
        }
    
    def process_chunk(self, chunk_spec: Dict) -> Dict:
        """Process a single chunk of records"""
        
        # This runs in a separate process
        table = chunk_spec['table']
        start_id = chunk_spec['start_id']
        end_id = chunk_spec['end_id']
        
        # Initialize database connections for this process
        local_source_db = SourceDatabase()
        local_target_db = TargetDatabase()
        
        # Get records in chunk
        source_records = local_source_db.get_records_range(table, start_id, end_id)
        target_records = local_target_db.get_records_range(table, start_id, end_id)
        
        # Reconcile chunk
        inconsistencies = 0
        corrections = 0
        
        for source_record in source_records:
            target_record = target_records.get(source_record['id'])
            
            if not target_record:
                inconsistencies += 1
                # Auto-correct if possible
                try:
                    local_target_db.insert(table, source_record)
                    corrections += 1
                except Exception:
                    pass  # Log error in production
            elif not self.records_match(source_record, target_record):
                inconsistencies += 1
                # Auto-correct field mismatches
                try:
                    updates = self.calculate_updates(source_record, target_record)
                    local_target_db.update(table, source_record['id'], updates)
                    corrections += 1
                except Exception:
                    pass  # Log error in production
        
        return {
            'chunk_number': chunk_spec['chunk_number'],
            'start_id': start_id,
            'end_id': end_id,
            'records_processed': len(source_records),
            'inconsistencies': inconsistencies,
            'corrections': corrections
        }
```

### 2. Incremental Reconciliation

```python
class IncrementalReconciler:
    def __init__(self, source_db, target_db):
        self.source_db = source_db
        self.target_db = target_db
        self.last_reconciliation_times = {}
    
    def incremental_reconciliation(self, table_name: str):
        """Reconcile only records changed since last reconciliation"""
        
        last_reconciled = self.get_last_reconciliation_time(table_name)
        
        # Get records modified since last reconciliation
        modified_source = self.source_db.get_records_modified_since(
            table_name, last_reconciled
        )
        
        modified_target = self.target_db.get_records_modified_since(
            table_name, last_reconciled
        )
        
        # Create lookup dictionaries
        source_dict = {r['id']: r for r in modified_source}
        target_dict = {r['id']: r for r in modified_target}
        
        # Find all record IDs to check
        all_ids = set(source_dict.keys()) | set(target_dict.keys())
        
        inconsistencies = []
        
        for record_id in all_ids:
            source_record = source_dict.get(record_id)
            target_record = target_dict.get(record_id)
            
            if source_record and not target_record:
                inconsistencies.append({
                    'type': 'missing_in_target',
                    'table': table_name,
                    'id': record_id,
                    'source_record': source_record
                })
            elif not source_record and target_record:
                inconsistencies.append({
                    'type': 'extra_in_target',
                    'table': table_name,
                    'id': record_id,
                    'target_record': target_record
                })
            elif source_record and target_record:
                if not self.records_match(source_record, target_record):
                    inconsistencies.append({
                        'type': 'data_mismatch',
                        'table': table_name,
                        'id': record_id,
                        'source_record': source_record,
                        'target_record': target_record,
                        'differences': self.find_differences(source_record, target_record)
                    })
        
        # Update last reconciliation time
        self.update_last_reconciliation_time(table_name, datetime.utcnow())
        
        return {
            'table': table_name,
            'reconciliation_time': datetime.utcnow(),
            'records_checked': len(all_ids),
            'inconsistencies_found': len(inconsistencies),
            'inconsistencies': inconsistencies
        }
    
    def get_last_reconciliation_time(self, table_name: str) -> datetime:
        """Get the last reconciliation timestamp for a table"""
        
        result = self.source_db.query("""
            SELECT last_reconciled_at
            FROM reconciliation_metadata
            WHERE table_name = %s
        """, (table_name,))
        
        if result:
            return result[0]['last_reconciled_at']
        else:
            # First time reconciliation - start from beginning of migration
            return self.get_migration_start_time()
    
    def update_last_reconciliation_time(self, table_name: str, timestamp: datetime):
        """Update the last reconciliation timestamp"""
        
        self.source_db.execute("""
            INSERT INTO reconciliation_metadata (table_name, last_reconciled_at)
            VALUES (%s, %s)
            ON CONFLICT (table_name)
            DO UPDATE SET last_reconciled_at = %s
        """, (table_name, timestamp, timestamp))
```

This comprehensive guide provides the framework and tools necessary for implementing robust data reconciliation strategies during migrations, ensuring data integrity and consistency while minimizing business disruption.