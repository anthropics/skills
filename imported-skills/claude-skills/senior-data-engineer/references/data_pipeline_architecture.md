# Data Pipeline Architecture

Comprehensive guide to designing and implementing production data pipelines.

## Table of Contents

1. [Architecture Patterns](#architecture-patterns)
2. [Batch Processing](#batch-processing)
3. [Stream Processing](#stream-processing)
4. [Exactly-Once Semantics](#exactly-once-semantics)
5. [Error Handling](#error-handling)
6. [Data Ingestion Patterns](#data-ingestion-patterns)
7. [Orchestration](#orchestration)

---

## Architecture Patterns

### Lambda Architecture

The Lambda architecture combines batch and stream processing for comprehensive data handling.

```
                    ┌─────────────────────────────────────┐
                    │           Data Sources              │
                    └─────────────────┬───────────────────┘
                                      │
                    ┌─────────────────▼───────────────────┐
                    │         Message Queue (Kafka)        │
                    └───────┬─────────────────┬───────────┘
                            │                 │
              ┌─────────────▼─────┐   ┌───────▼─────────────┐
              │    Batch Layer    │   │    Speed Layer      │
              │   (Spark/Airflow) │   │   (Flink/Spark SS)  │
              └─────────────┬─────┘   └───────┬─────────────┘
                            │                 │
              ┌─────────────▼─────┐   ┌───────▼─────────────┐
              │   Master Dataset  │   │   Real-time Views   │
              │   (Data Lake)     │   │   (Redis/Druid)     │
              └─────────────┬─────┘   └───────┬─────────────┘
                            │                 │
                    ┌───────▼─────────────────▼───────┐
                    │          Serving Layer           │
                    │   (Merged Batch + Real-time)     │
                    └─────────────────────────────────┘
```

**Components:**

1. **Batch Layer**
   - Processes complete historical data
   - Creates precomputed batch views
   - Handles complex transformations, ML training
   - Reprocessable from raw data

2. **Speed Layer**
   - Processes real-time data stream
   - Creates real-time views for recent data
   - Low latency, simpler transformations
   - Compensates for batch layer delay

3. **Serving Layer**
   - Merges batch and real-time views
   - Responds to queries
   - Provides unified interface

**Implementation Example:**

```python
# Batch layer: Daily aggregation with Spark
def batch_daily_aggregation(spark, date):
    """Process full day of data for batch views."""
    raw_df = spark.read.parquet(f"s3://data-lake/raw/events/date={date}")

    aggregated = raw_df.groupBy("user_id", "event_type") \
        .agg(
            count("*").alias("event_count"),
            sum("revenue").alias("total_revenue"),
            max("timestamp").alias("last_event")
        )

    aggregated.write \
        .mode("overwrite") \
        .partitionBy("event_type") \
        .parquet(f"s3://data-lake/batch-views/daily_agg/date={date}")

# Speed layer: Real-time aggregation with Spark Structured Streaming
def speed_realtime_aggregation(spark):
    """Process streaming data for real-time views."""
    stream_df = spark.readStream \
        .format("kafka") \
        .option("kafka.bootstrap.servers", "kafka:9092") \
        .option("subscribe", "events") \
        .load()

    parsed = stream_df.select(
        from_json(col("value").cast("string"), event_schema).alias("data")
    ).select("data.*")

    aggregated = parsed \
        .withWatermark("timestamp", "5 minutes") \
        .groupBy(
            window("timestamp", "1 minute"),
            "user_id",
            "event_type"
        ) \
        .agg(count("*").alias("event_count"))

    query = aggregated.writeStream \
        .format("redis") \
        .option("host", "redis") \
        .outputMode("update") \
        .start()

    return query
```

### Kappa Architecture

Kappa simplifies Lambda by using only stream processing with replay capability.

```
                    ┌─────────────────────────────────────┐
                    │           Data Sources              │
                    └─────────────────┬───────────────────┘
                                      │
                    ┌─────────────────▼───────────────────┐
                    │    Immutable Log (Kafka/Kinesis)     │
                    │         (Long retention)             │
                    └─────────────────┬───────────────────┘
                                      │
                    ┌─────────────────▼───────────────────┐
                    │        Stream Processor              │
                    │      (Flink/Spark Streaming)         │
                    └─────────────────┬───────────────────┘
                                      │
                    ┌─────────────────▼───────────────────┐
                    │         Serving Layer                │
                    │    (Database/Data Warehouse)         │
                    └─────────────────────────────────────┘
```

**Key Principles:**

1. **Single Processing Path**: All data processed as streams
2. **Immutable Log**: Kafka/Kinesis as source of truth with long retention
3. **Reprocessing via Replay**: Re-run stream processor from beginning when needed

**Reprocessing Strategy:**

```python
# Reprocessing in Kappa architecture
class KappaReprocessor:
    """Handle reprocessing by replaying from Kafka."""

    def __init__(self, kafka_config, flink_job):
        self.kafka = kafka_config
        self.job = flink_job

    def reprocess(self, from_timestamp: str):
        """Reprocess all data from a specific timestamp."""

        # 1. Start new consumer group reading from timestamp
        new_consumer_group = f"reprocess-{uuid.uuid4()}"

        # 2. Configure stream processor with new group
        self.job.set_config({
            "group.id": new_consumer_group,
            "auto.offset.reset": "none"  # We'll set offset manually
        })

        # 3. Seek to timestamp
        offsets = self._get_offsets_for_timestamp(from_timestamp)
        self.job.seek_to_offsets(offsets)

        # 4. Write to new output table/topic
        output_table = f"events_reprocessed_{datetime.now().strftime('%Y%m%d')}"
        self.job.set_output(output_table)

        # 5. Run until caught up
        self.job.run_until_caught_up()

        # 6. Swap output tables atomically
        self._atomic_table_swap("events", output_table)

    def _get_offsets_for_timestamp(self, timestamp):
        """Get Kafka offsets for a specific timestamp."""
        consumer = KafkaConsumer(bootstrap_servers=self.kafka["brokers"])
        partitions = consumer.partitions_for_topic("events")

        offsets = {}
        for partition in partitions:
            tp = TopicPartition("events", partition)
            offset = consumer.offsets_for_times({tp: timestamp})
            offsets[tp] = offset[tp].offset

        return offsets
```

### Medallion Architecture (Bronze/Silver/Gold)

Common in data lakehouses (Databricks, Delta Lake).

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Bronze    │────▶│   Silver    │────▶│    Gold     │
│  (Raw Data) │     │ (Cleansed)  │     │ (Analytics) │
└─────────────┘     └─────────────┘     └─────────────┘
     │                    │                    │
     ▼                    ▼                    ▼
 Landing zone        Validated,          Aggregated,
 Append-only         deduplicated,       business-ready
 Schema evolution    standardized        Star schema
```

**Implementation with Delta Lake:**

```python
# Bronze: Raw ingestion
def ingest_to_bronze(spark, source_path, bronze_path):
    """Ingest raw data to bronze layer."""
    df = spark.read.format("json").load(source_path)

    # Add metadata
    df = df.withColumn("_ingested_at", current_timestamp()) \
           .withColumn("_source_file", input_file_name())

    df.write \
        .format("delta") \
        .mode("append") \
        .option("mergeSchema", "true") \
        .save(bronze_path)

# Silver: Cleansing and validation
def bronze_to_silver(spark, bronze_path, silver_path):
    """Transform bronze to silver with cleansing."""
    bronze_df = spark.read.format("delta").load(bronze_path)

    # Read last processed version
    last_version = get_last_processed_version(silver_path, "bronze")

    # Get only new records
    new_records = bronze_df.filter(col("_commit_version") > last_version)

    # Cleanse and validate
    silver_df = new_records \
        .filter(col("user_id").isNotNull()) \
        .filter(col("event_type").isin(["click", "view", "purchase"])) \
        .withColumn("event_date", to_date("timestamp")) \
        .dropDuplicates(["event_id"])

    # Merge to silver (upsert)
    silver_table = DeltaTable.forPath(spark, silver_path)

    silver_table.alias("target") \
        .merge(
            silver_df.alias("source"),
            "target.event_id = source.event_id"
        ) \
        .whenMatchedUpdateAll() \
        .whenNotMatchedInsertAll() \
        .execute()

# Gold: Business aggregations
def silver_to_gold(spark, silver_path, gold_path):
    """Create business-ready aggregations in gold layer."""
    silver_df = spark.read.format("delta").load(silver_path)

    # Daily user metrics
    daily_metrics = silver_df \
        .groupBy("user_id", "event_date") \
        .agg(
            count("*").alias("total_events"),
            countDistinct("session_id").alias("sessions"),
            sum(when(col("event_type") == "purchase", col("revenue")).otherwise(0)).alias("revenue"),
            max("timestamp").alias("last_activity")
        )

    # Write as gold table
    daily_metrics.write \
        .format("delta") \
        .mode("overwrite") \
        .partitionBy("event_date") \
        .save(gold_path + "/daily_user_metrics")
```

---

## Batch Processing

### Apache Spark Best Practices

#### Memory Management

```python
# Optimal Spark configuration for batch jobs
spark = SparkSession.builder \
    .appName("BatchETL") \
    .config("spark.executor.memory", "8g") \
    .config("spark.executor.cores", "4") \
    .config("spark.driver.memory", "4g") \
    .config("spark.sql.shuffle.partitions", "200") \
    .config("spark.sql.adaptive.enabled", "true") \
    .config("spark.sql.adaptive.coalescePartitions.enabled", "true") \
    .config("spark.serializer", "org.apache.spark.serializer.KryoSerializer") \
    .getOrCreate()
```

**Memory Tuning Guidelines:**

| Data Size | Executors | Memory/Executor | Cores/Executor |
|-----------|-----------|-----------------|----------------|
| < 10 GB   | 2-4       | 4-8 GB          | 2-4            |
| 10-100 GB | 10-20     | 8-16 GB         | 4-8            |
| 100+ GB   | 50+       | 16-32 GB        | 4-8            |

#### Partition Optimization

```python
# Repartition vs Coalesce
# Repartition: Full shuffle, use for increasing partitions
df_repartitioned = df.repartition(100, "date")  # Partition by column

# Coalesce: No shuffle, use for decreasing partitions
df_coalesced = df.coalesce(10)  # Reduce partitions without shuffle

# Optimal partition size: 128-256 MB each
# Calculate partitions:
# num_partitions = total_data_size_mb / 200

# Check current partitions
print(f"Current partitions: {df.rdd.getNumPartitions()}")

# Repartition for optimal join performance
large_df = large_df.repartition(200, "join_key")
small_df = small_df.repartition(200, "join_key")
result = large_df.join(small_df, "join_key")
```

#### Join Optimization

```python
# Broadcast join for small tables (< 10MB by default)
from pyspark.sql.functions import broadcast

# Explicit broadcast hint
result = large_df.join(broadcast(small_df), "key")

# Increase broadcast threshold if needed
spark.conf.set("spark.sql.autoBroadcastJoinThreshold", "100m")

# Sort-merge join for large tables
spark.conf.set("spark.sql.join.preferSortMergeJoin", "true")

# Bucket tables for frequent joins
df.write \
    .bucketBy(100, "customer_id") \
    .sortBy("customer_id") \
    .mode("overwrite") \
    .saveAsTable("bucketed_orders")
```

#### Caching Strategy

```python
# Cache when:
# 1. DataFrame is used multiple times
# 2. After expensive transformations
# 3. Before iterative operations

# Use MEMORY_AND_DISK for large datasets
from pyspark import StorageLevel

df.persist(StorageLevel.MEMORY_AND_DISK)

# Cache only necessary columns
df.select("id", "value").cache()

# Unpersist when done
df.unpersist()

# Check storage
spark.catalog.clearCache()  # Clear all caches
```

### Airflow DAG Patterns

#### Idempotent Tasks

```python
# Always design idempotent tasks
from airflow.decorators import dag, task
from airflow.utils.dates import days_ago
from datetime import timedelta

@dag(
    schedule_interval="@daily",
    start_date=days_ago(7),
    catchup=True,
    default_args={
        "retries": 3,
        "retry_delay": timedelta(minutes=5),
    }
)
def idempotent_etl():

    @task
    def extract(execution_date=None):
        """Idempotent extraction - same date always returns same data."""
        date_str = execution_date.strftime("%Y-%m-%d")

        # Query for specific date only
        query = f"""
            SELECT * FROM source_table
            WHERE DATE(created_at) = '{date_str}'
        """
        return query_database(query)

    @task
    def transform(data):
        """Pure function - no side effects."""
        return [transform_record(r) for r in data]

    @task
    def load(data, execution_date=None):
        """Idempotent load - delete before insert or use MERGE."""
        date_str = execution_date.strftime("%Y-%m-%d")

        # Option 1: Delete and reinsert
        execute_sql(f"DELETE FROM target WHERE date = '{date_str}'")
        insert_data(data)

        # Option 2: Use MERGE/UPSERT
        # MERGE INTO target USING source ON target.id = source.id
        # WHEN MATCHED THEN UPDATE
        # WHEN NOT MATCHED THEN INSERT

    raw = extract()
    transformed = transform(raw)
    load(transformed)

dag = idempotent_etl()
```

#### Backfill Pattern

```python
from airflow import DAG
from airflow.operators.python import PythonOperator
from airflow.utils.dates import days_ago
from datetime import datetime, timedelta

def process_date(ds, **kwargs):
    """Process a single date - supports backfill."""
    logical_date = datetime.strptime(ds, "%Y-%m-%d")

    # Always process specific date, not "latest"
    data = extract_for_date(logical_date)
    transformed = transform(data)

    # Use partition/date-specific target
    load_to_partition(transformed, partition=ds)

with DAG(
    "backfillable_etl",
    schedule_interval="@daily",
    start_date=datetime(2024, 1, 1),
    catchup=True,  # Enable backfill
    max_active_runs=3,  # Limit parallel backfills
) as dag:

    process = PythonOperator(
        task_id="process",
        python_callable=process_date,
        provide_context=True,
    )

# Backfill command:
# airflow dags backfill -s 2024-01-01 -e 2024-01-31 backfillable_etl
```

---

## Stream Processing

### Apache Kafka Architecture

#### Topic Design

```bash
# Create topic with proper configuration
kafka-topics.sh --create \
    --bootstrap-server localhost:9092 \
    --topic user-events \
    --partitions 24 \
    --replication-factor 3 \
    --config retention.ms=604800000 \        # 7 days
    --config retention.bytes=107374182400 \  # 100GB
    --config cleanup.policy=delete \
    --config min.insync.replicas=2 \         # Durability
    --config segment.bytes=1073741824        # 1GB segments
```

**Partition Count Guidelines:**

| Throughput | Partitions | Notes |
|------------|------------|-------|
| < 10K msg/s | 6-12 | Single consumer can handle |
| 10K-100K msg/s | 24-48 | Multiple consumers needed |
| > 100K msg/s | 100+ | Scale consumers with partitions |

**Partition Key Selection:**

```python
# Good partition keys: Even distribution, related data together
# For user events: user_id (events for same user on same partition)
# For orders: order_id (if no ordering needed) or customer_id (if needed)

from kafka import KafkaProducer
import json

producer = KafkaProducer(
    bootstrap_servers=['localhost:9092'],
    value_serializer=lambda v: json.dumps(v).encode('utf-8'),
    key_serializer=lambda k: k.encode('utf-8')
)

def send_event(event):
    # Use user_id as key for user-based partitioning
    producer.send(
        topic='user-events',
        key=event['user_id'],  # Partition key
        value=event
    )
```

### Spark Structured Streaming

#### Watermarks and Late Data

```python
from pyspark.sql.functions import window, col

# Read stream
events = spark.readStream \
    .format("kafka") \
    .option("kafka.bootstrap.servers", "localhost:9092") \
    .option("subscribe", "events") \
    .load() \
    .select(from_json(col("value").cast("string"), schema).alias("data")) \
    .select("data.*")

# Add watermark for late data handling
# Data arriving more than 10 minutes late will be dropped
windowed_counts = events \
    .withWatermark("event_time", "10 minutes") \
    .groupBy(
        window("event_time", "5 minutes", "1 minute"),  # 5-min windows, 1-min slide
        "event_type"
    ) \
    .count()

# Write with append mode (only final results for complete windows)
query = windowed_counts.writeStream \
    .format("delta") \
    .outputMode("append") \
    .option("checkpointLocation", "/checkpoints/windowed_counts") \
    .start()
```

**Watermark Behavior:**

```
Timeline: ─────────────────────────────────────────▶
Events:   E1   E2   E3        E4(late)    E5
          │    │    │         │           │
Time:     10:00 10:02 10:05   10:03       10:15
          ▲                   ▲
          │                   │
          Current            Arrives at 10:15
          watermark          but event_time=10:03
          = max_event_time
            - threshold
          = 10:05 - 10min    If watermark > event_time:
          = 9:55               Event is dropped (too late)
```

#### Stateful Operations

```python
from pyspark.sql.functions import pandas_udf, PandasUDFType
from pyspark.sql.streaming.state import GroupState, GroupStateTimeout

# Session windows using flatMapGroupsWithState
def session_aggregation(key, events, state):
    """Aggregate events into sessions with 30-minute timeout."""

    # Get or initialize state
    if state.exists:
        session = state.get
    else:
        session = {"start": None, "events": [], "total": 0}

    # Process new events
    for event in events:
        if session["start"] is None:
            session["start"] = event.timestamp
        session["events"].append(event)
        session["total"] += event.value

    # Set timeout (session expires after 30 min of inactivity)
    state.setTimeoutDuration("30 minutes")

    # Check if session should close
    if state.hasTimedOut():
        # Emit completed session
        output = {
            "user_id": key,
            "session_start": session["start"],
            "event_count": len(session["events"]),
            "total_value": session["total"]
        }
        state.remove()
        yield output
    else:
        # Update state
        state.update(session)

# Apply stateful operation
sessions = events \
    .groupByKey(lambda e: e.user_id) \
    .flatMapGroupsWithState(
        session_aggregation,
        outputMode="append",
        stateTimeout=GroupStateTimeout.ProcessingTimeTimeout()
    )
```

---

## Exactly-Once Semantics

### Producer Idempotence

```python
from kafka import KafkaProducer

# Enable idempotent producer
producer = KafkaProducer(
    bootstrap_servers=['localhost:9092'],
    acks='all',                    # Wait for all replicas
    enable_idempotence=True,       # Exactly-once per partition
    max_in_flight_requests_per_connection=5,  # Max with idempotence
    retries=2147483647,            # Infinite retries
    value_serializer=lambda v: json.dumps(v).encode('utf-8')
)

# Producer will deduplicate based on sequence numbers
for i in range(100):
    producer.send('topic', {'id': i, 'data': 'value'})

producer.flush()
```

### Transactional Processing

```python
from kafka import KafkaProducer, KafkaConsumer
from kafka.errors import KafkaError

# Transactional producer
producer = KafkaProducer(
    bootstrap_servers=['localhost:9092'],
    transactional_id='my-transactional-id',  # Enable transactions
    enable_idempotence=True,
    acks='all'
)

producer.init_transactions()

def process_with_transactions(consumer, producer):
    """Read-process-write with exactly-once semantics."""

    try:
        producer.begin_transaction()

        # Read
        records = consumer.poll(timeout_ms=1000)

        for tp, messages in records.items():
            for message in messages:
                # Process
                result = transform(message.value)

                # Write to output topic
                producer.send('output-topic', result)

        # Commit offsets and transaction atomically
        producer.send_offsets_to_transaction(
            consumer.position(consumer.assignment()),
            consumer.group_id
        )
        producer.commit_transaction()

    except KafkaError as e:
        producer.abort_transaction()
        raise
```

### Spark Exactly-Once to External Systems

```python
# Use foreachBatch with idempotent writes
def write_to_database_idempotent(batch_df, batch_id):
    """Write batch with exactly-once semantics."""

    # Add batch_id for deduplication
    batch_with_id = batch_df.withColumn("batch_id", lit(batch_id))

    # Use MERGE for idempotent writes
    batch_with_id.write \
        .format("jdbc") \
        .option("url", "jdbc:postgresql://localhost/db") \
        .option("dbtable", "staging_events") \
        .option("driver", "org.postgresql.Driver") \
        .mode("append") \
        .save()

    # Merge staging to final (idempotent)
    execute_sql("""
        MERGE INTO events AS target
        USING staging_events AS source
        ON target.event_id = source.event_id
        WHEN MATCHED THEN UPDATE SET *
        WHEN NOT MATCHED THEN INSERT *
    """)

    # Clean staging
    execute_sql("TRUNCATE staging_events")

query = events.writeStream \
    .foreachBatch(write_to_database_idempotent) \
    .option("checkpointLocation", "/checkpoints/to-postgres") \
    .start()
```

---

## Error Handling

### Dead Letter Queue (DLQ)

```python
class DeadLetterQueue:
    """Handle failed records with dead letter queue pattern."""

    def __init__(self, dlq_topic: str, producer: KafkaProducer):
        self.dlq_topic = dlq_topic
        self.producer = producer

    def send_to_dlq(self, record, error: Exception, context: dict):
        """Send failed record to DLQ with error metadata."""

        dlq_record = {
            "original_record": record,
            "error_type": type(error).__name__,
            "error_message": str(error),
            "timestamp": datetime.utcnow().isoformat(),
            "context": context,
            "retry_count": context.get("retry_count", 0)
        }

        self.producer.send(
            self.dlq_topic,
            value=json.dumps(dlq_record).encode('utf-8')
        )

def process_with_dlq(consumer, processor, dlq):
    """Process records with DLQ for failures."""

    for message in consumer:
        try:
            result = processor.process(message.value)
            # Success - commit offset
            consumer.commit()

        except ValidationError as e:
            # Non-retryable - send to DLQ immediately
            dlq.send_to_dlq(
                message.value,
                e,
                {"topic": message.topic, "partition": message.partition}
            )
            consumer.commit()  # Don't retry

        except TemporaryError as e:
            # Retryable - don't commit, let consumer retry
            # After max retries, send to DLQ
            retry_count = message.headers.get("retry_count", 0)
            if retry_count >= MAX_RETRIES:
                dlq.send_to_dlq(message.value, e, {"retry_count": retry_count})
                consumer.commit()
            else:
                raise  # Will be retried
```

### Circuit Breaker

```python
from dataclasses import dataclass
from datetime import datetime, timedelta
from enum import Enum
import threading

class CircuitState(Enum):
    CLOSED = "closed"      # Normal operation
    OPEN = "open"          # Failing, reject calls
    HALF_OPEN = "half_open"  # Testing if recovered

@dataclass
class CircuitBreaker:
    """Circuit breaker for external service calls."""

    failure_threshold: int = 5
    recovery_timeout: timedelta = timedelta(seconds=30)
    success_threshold: int = 3

    def __post_init__(self):
        self.state = CircuitState.CLOSED
        self.failure_count = 0
        self.success_count = 0
        self.last_failure_time = None
        self.lock = threading.Lock()

    def call(self, func, *args, **kwargs):
        """Execute function with circuit breaker protection."""

        with self.lock:
            if self.state == CircuitState.OPEN:
                if self._should_attempt_reset():
                    self.state = CircuitState.HALF_OPEN
                else:
                    raise CircuitOpenError("Circuit is open")

        try:
            result = func(*args, **kwargs)
            self._record_success()
            return result

        except Exception as e:
            self._record_failure()
            raise

    def _record_success(self):
        with self.lock:
            if self.state == CircuitState.HALF_OPEN:
                self.success_count += 1
                if self.success_count >= self.success_threshold:
                    self.state = CircuitState.CLOSED
                    self.failure_count = 0
                    self.success_count = 0
            elif self.state == CircuitState.CLOSED:
                self.failure_count = 0

    def _record_failure(self):
        with self.lock:
            self.failure_count += 1
            self.last_failure_time = datetime.now()

            if self.state == CircuitState.HALF_OPEN:
                self.state = CircuitState.OPEN
                self.success_count = 0
            elif self.failure_count >= self.failure_threshold:
                self.state = CircuitState.OPEN

    def _should_attempt_reset(self):
        if self.last_failure_time is None:
            return True
        return datetime.now() - self.last_failure_time >= self.recovery_timeout

# Usage
circuit = CircuitBreaker(failure_threshold=5, recovery_timeout=timedelta(seconds=60))

def call_external_api(data):
    return circuit.call(external_api.process, data)
```

---

## Data Ingestion Patterns

### Change Data Capture (CDC)

```python
# Using Debezium with Kafka Connect
# connector-config.json
{
    "name": "postgres-cdc-connector",
    "config": {
        "connector.class": "io.debezium.connector.postgresql.PostgresConnector",
        "database.hostname": "postgres",
        "database.port": "5432",
        "database.user": "debezium",
        "database.password": "password",
        "database.dbname": "source_db",
        "database.server.name": "source",
        "table.include.list": "public.orders,public.customers",
        "plugin.name": "pgoutput",
        "publication.name": "dbz_publication",
        "slot.name": "debezium_slot",
        "transforms": "unwrap",
        "transforms.unwrap.type": "io.debezium.transforms.ExtractNewRecordState",
        "transforms.unwrap.drop.tombstones": "false"
    }
}
```

**Processing CDC Events:**

```python
def process_cdc_event(event):
    """Process Debezium CDC event."""

    operation = event.get("op")

    if operation == "c":  # Create (INSERT)
        after = event.get("after")
        return {"action": "insert", "data": after}

    elif operation == "u":  # Update
        before = event.get("before")
        after = event.get("after")
        return {"action": "update", "before": before, "after": after}

    elif operation == "d":  # Delete
        before = event.get("before")
        return {"action": "delete", "data": before}

    elif operation == "r":  # Read (snapshot)
        after = event.get("after")
        return {"action": "snapshot", "data": after}
```

### Bulk Ingestion

```python
# Efficient bulk loading to data warehouse
from concurrent.futures import ThreadPoolExecutor
import boto3

class BulkIngester:
    """Bulk ingest data to Snowflake via S3."""

    def __init__(self, s3_bucket: str, snowflake_conn):
        self.s3 = boto3.client('s3')
        self.bucket = s3_bucket
        self.snowflake = snowflake_conn

    def ingest_dataframe(self, df, table_name: str, mode: str = "append"):
        """Bulk ingest DataFrame to Snowflake."""

        # 1. Write to S3 as Parquet (compressed, columnar)
        s3_path = f"s3://{self.bucket}/staging/{table_name}/{uuid.uuid4()}"
        df.write.parquet(s3_path)

        # 2. Create external stage if not exists
        self.snowflake.execute(f"""
            CREATE STAGE IF NOT EXISTS {table_name}_stage
            URL = '{s3_path}'
            CREDENTIALS = (AWS_KEY_ID='...' AWS_SECRET_KEY='...')
            FILE_FORMAT = (TYPE = 'PARQUET')
        """)

        # 3. COPY INTO (much faster than INSERT)
        if mode == "overwrite":
            self.snowflake.execute(f"TRUNCATE TABLE {table_name}")

        self.snowflake.execute(f"""
            COPY INTO {table_name}
            FROM @{table_name}_stage
            FILE_FORMAT = (TYPE = 'PARQUET')
            MATCH_BY_COLUMN_NAME = CASE_INSENSITIVE
            ON_ERROR = 'CONTINUE'
        """)

        # 4. Cleanup staging files
        self._cleanup_s3(s3_path)
```

---

## Orchestration

### Dependency Management

```python
from airflow import DAG
from airflow.operators.python import PythonOperator
from airflow.sensors.external_task import ExternalTaskSensor
from airflow.utils.task_group import TaskGroup
from datetime import timedelta

with DAG("complex_pipeline") as dag:

    # Wait for upstream DAG
    wait_for_source = ExternalTaskSensor(
        task_id="wait_for_source_etl",
        external_dag_id="source_etl_dag",
        external_task_id="final_task",
        execution_delta=timedelta(hours=0),
        timeout=3600,
        mode="poke",
        poke_interval=60,
    )

    # Parallel extraction group
    with TaskGroup("extract") as extract_group:
        extract_orders = PythonOperator(
            task_id="extract_orders",
            python_callable=extract_orders_func,
        )
        extract_customers = PythonOperator(
            task_id="extract_customers",
            python_callable=extract_customers_func,
        )
        extract_products = PythonOperator(
            task_id="extract_products",
            python_callable=extract_products_func,
        )

    # Sequential transformation
    with TaskGroup("transform") as transform_group:
        join_data = PythonOperator(
            task_id="join_data",
            python_callable=join_func,
        )
        aggregate = PythonOperator(
            task_id="aggregate",
            python_callable=aggregate_func,
        )
        join_data >> aggregate

    # Load
    load = PythonOperator(
        task_id="load",
        python_callable=load_func,
    )

    # Define dependencies
    wait_for_source >> extract_group >> transform_group >> load
```

### Dynamic DAG Generation

```python
from airflow import DAG
from airflow.operators.python import PythonOperator
from datetime import datetime
import yaml

def create_etl_dag(config: dict) -> DAG:
    """Factory function to create ETL DAGs from config."""

    dag = DAG(
        dag_id=f"etl_{config['source']}_{config['destination']}",
        schedule_interval=config.get('schedule', '@daily'),
        start_date=datetime(2024, 1, 1),
        catchup=False,
        tags=['etl', 'auto-generated'],
    )

    with dag:
        extract = PythonOperator(
            task_id='extract',
            python_callable=create_extract_func(config['source']),
        )

        transform = PythonOperator(
            task_id='transform',
            python_callable=create_transform_func(config['transformations']),
        )

        load = PythonOperator(
            task_id='load',
            python_callable=create_load_func(config['destination']),
        )

        extract >> transform >> load

    return dag

# Load configurations
with open('/config/etl_pipelines.yaml') as f:
    configs = yaml.safe_load(f)

# Generate DAGs
for config in configs['pipelines']:
    dag_id = f"etl_{config['source']}_{config['destination']}"
    globals()[dag_id] = create_etl_dag(config)
```
