---
name: marklogic-flux
description: >
  MarkLogic Flux for data movement: modern replacement for MLCP and CoRB 2. Import/export data
  (CSV, JSON, XML, Parquet, Avro, JDBC), reprocess documents, copy between databases, build RAG
  pipelines, integrate with Gradle, and automate data workflows. Supports cloud storage (S3, Azure).
---

# MarkLogic Flux

Unified command-line tool and API for all MarkLogic data movement: import, export, reprocess, copy. Modern replacement for MLCP and CoRB 2 with Apache Spark performance, cloud storage support, and RAG pipeline capabilities.

## When to Use This Skill

Apply this skill when tasks involve:
- Importing data from files (CSV, JSON, XML, Parquet, Avro, ORC)
- Exporting MarkLogic documents to files or databases
- Reprocessing existing documents (bulk updates, transformations)
- Copying data between MarkLogic databases
- Loading data from JDBC sources (RDBMS)
- Building RAG pipelines with text splitting and embeddings
- Migrating from MLCP or CoRB to Flux
- Automating data workflows in Gradle projects
- Working with cloud storage (S3, Azure)

## Overview

**MarkLogic Flux** is a unified data movement tool that consolidates and modernizes MLCP (MarkLogic Content Pump) and CoRB 2 (Content Reprocessing Batch) capabilities. Built on Apache Spark, it provides better performance, modern format support, and both CLI and API interfaces.

**Key Capabilities:**
- ✅ Import from files, JDBC, cloud storage, custom sources
- ✅ Export to files, databases, cloud storage, custom destinations
- ✅ Reprocess existing documents with custom code
- ✅ Copy data between databases with metadata preservation
- ✅ RAG pipeline support (text splitting, embeddings)
- ✅ Apache Spark-based for distributed processing
- ✅ Embeddable API for Gradle/Java integration
- ✅ Modern formats: Parquet, Avro, ORC

## Installation

### Prerequisites

- **MarkLogic Server** installed and running
- **Java 11+** installed
- **Flux binary** downloaded from [MarkLogic Developer Portal](https://developer.marklogic.com/)

### Download and Setup

```bash
# Download Flux (replace with actual version)
wget https://developer.marklogic.com/download/binaries/flux/flux-1.4.0.zip

# Extract
unzip flux-1.4.0.zip
cd flux-1.4.0

# Verify installation
./bin/flux --version
```

### Add to PATH (Optional)

```bash
# Add to ~/.bashrc or ~/.zshrc
export PATH=$PATH:/path/to/flux-1.4.0/bin

# Now use directly
flux --version
```

## CLI Command Structure

### Basic Pattern

```bash
flux <command> [options]

# General format
flux <command> \
    --connection-string "user:password@host:port" \
    [command-specific options] \
    [common options]
```

### Command Categories

| Category | Commands | Purpose |
|----------|----------|---------|
| **Import** | `import-files`, `import-delimited-files`, `import-json-files`, `import-xml-files`, `import-parquet-files`, `import-avro-files`, `import-orc-files`, `import-jdbc`, `import-archives`, `custom-import` | Load data into MarkLogic |
| **Export** | `export-files`, `export-parquet-files`, `export-avro-files`, `export-delimited-files`, `export-jdbc`, `export-archives`, `custom-export` | Extract data from MarkLogic |
| **Process** | `reprocess`, `copy`, `custom-code` | Transform or move data within MarkLogic |

## Essential Configuration

### Connection String Format

```bash
# Basic format
user:password@host:port

# With database
user:password@host:port/database-name

# URL-encoded special characters
user:sp%40r%3Ak@host:8000
```

### Connection Options

```bash
# Method 1: Connection string (recommended)
--connection-string "admin:admin@localhost:8004"

# Method 2: Individual options
--host localhost
--port 8004
--username admin
--password password
--database content-db

# SSL Configuration (one-way)
--connection-string "admin:admin@localhost:8004"
--ssl-protocol TLSv1.2
--truststore-path /path/to/truststore.jks
--truststore-password secret

# SSL Configuration (two-way)
--keystore-path /path/to/keystore.jks
--keystore-password secret
--truststore-path /path/to/truststore.jks
--truststore-password secret

# Connection type
--connection-type DIRECT  # Bypass load balancer (faster)
--connection-type GATEWAY # Default: use load balancer
```

## Essential Workflows

### Workflow 1: Import CSV Files

**Phase 1: Prepare data**
```bash
# Place CSV file (can be gzipped)
data/
  └── employees.csv.gz
```

**Phase 2: Import with options**
```bash
flux import-delimited-files \
    --path data/employees.csv.gz \
    --connection-string "admin:admin@localhost:8004" \
    --collections employee \
    --permissions employee-role,read,employee-role,update \
    --uri-template "/employee/{id}.json" \
    --json-root-name Employee
```

**Expected timing:**
- Small files (< 10K rows): 5-15 seconds
- Medium files (10K-100K rows): 30-120 seconds
- Large files (> 100K rows): Use `--batch-size` and `--thread-count` tuning

**When to use:**
- ✅ Initial data loads from CSV/TSV
- ✅ Periodic data imports from exports
- ✅ Migration from relational databases
- ❌ Real-time streaming (use REST API instead)

### Workflow 2: Export Documents to Files

**Phase 1: Define export criteria**
```bash
# Option A: Export by collection
--collections employee

# Option B: Export by query
--string-query "Engineering"

# Option C: Export by structured query
--query '{"query": {"term-query": {"text": "hello"}}}'

# Option D: Export by URI list
--uris-file uris.txt
```

**Phase 2: Export with compression**
```bash
flux export-files \
    --connection-string "admin:admin@localhost:8004" \
    --collections employee \
    --path export \
    --compression zip \
    --zip-file-count 1 \
    --pretty-print
```

**Expected timing:**
- Small datasets (< 1K docs): 5-15 seconds
- Medium datasets (1K-100K docs): 30-300 seconds
- Large datasets (> 100K docs): Use partitioning

**When to use:**
- ✅ Backup/archive documents
- ✅ Data migration to other systems
- ✅ Extract for analytics/reporting
- ✅ Export to cloud storage (S3, Azure)

### Workflow 3: Reprocess Existing Documents

**Phase 1: Write reprocessing code**
```javascript
// Add collection to documents
declareUpdate();
xdmp.documentAddCollections(URI, 'processed');
```

**Phase 2: Execute reprocessing**
```bash
flux reprocess \
    --connection-string "admin:admin@localhost:8004" \
    --read-javascript "cts.uris(null, null, cts.collectionQuery('employee'))" \
    --write-javascript "declareUpdate(); xdmp.documentAddCollections(URI, 'processed')" \
    --batch-size 100 \
    --thread-count 32 \
    --log-progress 10000
```

**Expected timing:**
- Simple updates (< 10K docs): 10-60 seconds
- Complex processing (10K-100K docs): 2-10 minutes
- Large datasets (> 100K docs): Use forest partitions

**When to use:**
- ✅ Bulk metadata updates (collections, permissions, properties)
- ✅ Document transformations
- ✅ Data enrichment
- ✅ Fixing data quality issues
- ❌ One-time scripts (use Query Console)

### Workflow 4: Copy Between Databases

**Phase 1: Identify source and target**
```bash
# Source: localhost:8004 (content-db)
# Target: localhost:8000 (archive-db)
```

**Phase 2: Copy with metadata**
```bash
flux copy \
    --connection-string "admin:admin@localhost:8004" \
    --collections employee \
    --output-connection-string "admin:admin@localhost:8000" \
    --output-database archive-db \
    --output-collections archived \
    --categories content,collections,permissions,metadata
```

**Expected timing:**
- Small datasets (< 10K docs): 30-120 seconds
- Medium datasets (10K-100K docs): 2-10 minutes
- Large datasets (> 100K docs): Use DIRECT connection

**When to use:**
- ✅ Database migrations
- ✅ Environment synchronization (dev → test)
- ✅ Archival workflows
- ✅ Data subsetting

### Workflow 5: Import from JDBC (RDBMS)

**Phase 1: Prepare JDBC driver**
```bash
# Place JDBC driver JAR in flux/ext directory
flux/
  └── ext/
      └── postgresql-42.6.0.jar
```

**Phase 2: Import with SQL query**
```bash
flux import-jdbc \
    --jdbc-url "jdbc:postgresql://localhost/mydb?user=postgres&password=secret" \
    --jdbc-driver "org.postgresql.Driver" \
    --query "SELECT * FROM customers WHERE active = true" \
    --connection-string "admin:admin@localhost:8004" \
    --collections customer \
    --permissions app-role,read,app-role,update \
    --uri-template "/customer/{customer_id}.json" \
    --json-root-name Customer
```

**Expected timing:**
- Small queries (< 10K rows): 30-120 seconds
- Medium queries (10K-100K rows): 2-10 minutes
- Large queries (> 100K rows): Use pagination or incremental loads

**When to use:**
- ✅ Initial migration from RDBMS
- ✅ Periodic data synchronization
- ✅ Data warehouse ETL
- ❌ Real-time replication (use CDC tools)

## Core Command Reference

### Import Commands

| Command | Purpose | Input Format | Best For |
|---------|---------|--------------|----------|
| `import-files` | Generic file import | Any text/binary | Mixed file types |
| `import-delimited-files` | CSV/TSV import | CSV, TSV | Tabular data |
| `import-json-files` | JSON import | JSON, JSONL | JSON documents |
| `import-xml-files` | XML import | XML | XML documents |
| `import-parquet-files` | Parquet import | Parquet | Big data formats |
| `import-avro-files` | Avro import | Avro | Hadoop ecosystem |
| `import-orc-files` | ORC import | ORC | Hive/Spark data |
| `import-jdbc` | Database import | SQL query results | RDBMS migration |
| `import-archives` | Archive import | ZIP archives with metadata | Backup restoration |
| `custom-import` | Custom source | Any Spark-readable | Specialized sources |

### Export Commands

| Command | Purpose | Output Format | Best For |
|---------|---------|---------------|----------|
| `export-files` | Generic export | Original format | Document backup |
| `export-parquet-files` | Parquet export | Parquet | Big data analytics |
| `export-avro-files` | Avro export | Avro | Hadoop ecosystem |
| `export-delimited-files` | CSV export | CSV, TSV | Excel/analytics |
| `export-jdbc` | Database export | RDBMS tables | Data warehouse |
| `export-archives` | Archive export | ZIP with metadata | Full backup |
| `custom-export` | Custom destination | Custom format | Specialized targets |

### Processing Commands

| Command | Purpose | Use Case |
|---------|---------|----------|
| `reprocess` | Execute custom code on existing documents | Bulk updates, transformations |
| `copy` | Copy documents between databases | Migrations, synchronization |
| `custom-code` | Execute arbitrary Spark code | Advanced workflows |

## Common Options Reference

### Document Options

```bash
# Collections
--collections collection1,collection2
--output-collections new-collection1,new-collection2

# Permissions
--permissions role,read,role,update
--output-permissions admin-role,update

# URI Control
--uri-template "/prefix/{field}/suffix.json"
--uri-prefix "/documents/"
--uri-suffix ".json"
--uri-replace "pattern,replacement"

# Document Type
--document-type JSON|XML|TEXT|BINARY
```

### Performance Options

```bash
# Batch and Thread Control
--batch-size 100           # Documents per batch
--thread-count 32          # Parallel threads
--spark-master-url local[16]  # Spark workers

# Connection Optimization
--connection-type DIRECT   # Bypass load balancer
--disable-gzipped-responses # For small responses

# Progress Monitoring
--log-progress 10000       # Log every N documents
--log-read-progress 10000  # Log read progress
```

### Query Options (Export)

```bash
# Collection Filter
--collections collection1,collection2

# Directory Filter
--directory /path/

# String Query (Google-style)
--string-query "search terms"

# Structured Query (JSON)
--query '{"query": {"term-query": {"text": "hello"}}}'

# URI List
--uris "/doc1.json\n/doc2.json"
--uris-file uris.txt

# Limit Results
--limit 100
```

### File Options

```bash
# Path Configuration
--path /path/to/files      # Local filesystem
--path s3a://bucket/path   # Amazon S3
--path wasbs://container@account.blob.core.windows.net/path  # Azure

# Compression
--compression gzip|zip
--zip-file-count 1         # Number of ZIP files

# Encoding and Format
--encoding UTF-8|ISO-8859-1
--pretty-print             # Format JSON/XML output
```

### Preview and Testing Options

```bash
# Preview Data
--preview 10               # Show first 10 records
--preview-drop column1,column2  # Hide columns
--preview-list             # List available data
--preview-schema           # Show schema

# Count Records
--count                    # Count without processing

# Limit Processing
--limit 100               # Process only first 100
```

## Gradle Integration

### Setup Dependencies

**buildSrc/build.gradle:**
```gradle
repositories {
    mavenCentral()
}

dependencies {
    implementation "com.marklogic:flux-api:1.4.0"
}

configurations.all {
    resolutionStrategy.eachDependency { DependencyResolveDetails details ->
        if (details.requested.group.startsWith('com.fasterxml.jackson')) {
            details.useVersion '2.15.2'
            details.because 'Must ensure the Jackson version preferred by Spark is used'
        }
    }
}
```

### Custom Flux Task Class

**buildSrc/src/main/groovy/FluxReprocessTask.groovy:**
```groovy
import org.gradle.api.DefaultTask
import org.gradle.api.tasks.TaskAction
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.Optional
import com.marklogic.flux.api.Flux
import org.apache.spark.sql.SparkSession

class FluxReprocessTask extends DefaultTask {

    @Input String reader
    @Input String writer
    @Input Integer threads = 32
    @Input Integer batch = 1
    @Input Integer progress = 10000

    @Optional @Input List<String> readVars = []
    @Optional @Input List<String> writeVars = []

    @TaskAction
    void runReprocess() {
        String conn = FluxHelpers.toFluxConn(project)

        Map<String,String> readerVars = kvListToMap(readVars)
        Map<String,String> writerVars = kvListToMap(writeVars)

        boolean sslFlag = project.findProperty('sslFlag')?.toString()?.toBoolean() ?: false

        SparkSession spark = null
        try {
            spark = SparkSession.builder()
                .appName("FluxReprocess-" + name)
                .master("local[*]")
                .getOrCreate()
            spark.sparkContext().setLogLevel("INFO")

            Flux.reprocess()
                .connection { c ->
                    c.connectionString(conn)
                    if (sslFlag) c.sslProtocol("default")
                }
                .withSparkSession(spark)
                .from { r ->
                    def rr = r.invoke(reader).logProgress(progress)
                    rr = applyVars(rr, readerVars)
                    rr
                }
                .to { w ->
                    def ww = w.invoke(writer)
                        .batchSize(batch)
                        .threadCount(threads)
                        .logProgress(progress)
                    ww = applyVars(ww, writerVars)
                    ww
                }
                .execute()

            println "Flux reprocess '${name}' completed successfully."
        } catch (Throwable ex) {
            ex.printStackTrace()
            throw new RuntimeException("Flux reprocess '${name}' failed", ex)
        } finally {
            if (spark != null) {
                try { spark.stop() } catch (Exception ignore) {}
            }
        }
    }

    private Map<String,String> kvListToMap(List<String> kvList) {
        Map<String,String> map = [:]
        kvList?.each { kv ->
            def parts = kv.split('=', 2)
            if (parts.length == 2) {
                map[parts[0]] = parts[1]
            }
        }
        return map
    }

    private static applyVars(reader, Map<String,String> vars) {
        vars.each { k, v -> reader = reader.var(k, v) }
        return reader
    }
}

class FluxHelpers {
    static String toFluxConn(Project project) {
        def user = project.findProperty("mlUsername") ?: "admin"
        def pass = project.findProperty("mlPassword") ?: "admin"
        def host = project.findProperty("mlHost") ?: "localhost"
        def port = project.findProperty("mlRestPort") ?: "8004"
        return "${user}:${pass}@${host}:${port}"
    }
}
```

### Define Gradle Tasks

**build.gradle:**
```gradle
// Task 1: Add collections to documents
tasks.register("addProcessedCollection", FluxReprocessTask) {
    group = "Data Processing"
    description = "Add 'processed' collection to all employee documents"
    reader = "/queries/employee-uris.xqy"
    writer = "/transforms/add-collection.xqy"
    threads = 32
    batch = 1
    progress = 10000
}

// Task 2: Update document metadata
tasks.register("updateMetadata", FluxReprocessTask) {
    group = "Data Processing"
    description = "Update document metadata"
    reader = "/queries/document-uris.xqy"
    writer = "/transforms/update-metadata.xqy"
    threads = 16
    batch = 10
    progress = 5000
    readVars = ["status=active"]
    writeVars = ["timestamp=${new Date().time}"]
}

// Task 3: Import CSV using API
tasks.register("importEmployees") {
    group = "Data Loading"
    description = "Import employee CSV files"
    doLast {
        Flux.importDelimitedFiles()
            .connectionString(FluxHelpers.toFluxConn(project))
            .from { options ->
                options.paths("data/employees.csv")
                    .encoding("UTF-8")
            }
            .to { options ->
                options.collections("employee")
                    .permissionsString("app-role,read,app-role,update")
                    .uriTemplate("/employee/{id}.json")
                    .jsonRootName("Employee")
            }
            .execute()
        println "Employee import completed."
    }
}

// Task 4: Export to files
tasks.register("exportEmployees") {
    group = "Data Export"
    description = "Export employee documents to ZIP"
    doLast {
        Flux.exportFiles()
            .connectionString(FluxHelpers.toFluxConn(project))
            .from { options ->
                options.collections("employee")
            }
            .to { options ->
                options.path("export/employees")
                    .compression("zip")
                    .zipFileCount(1)
                    .prettyPrint()
            }
            .execute()
        println "Employee export completed."
    }
}
```

### Run Gradle Tasks

```bash
# List tasks
./gradlew tasks --group="Data Processing"

# Run single task
./gradlew addProcessedCollection

# Run with environment
./gradlew updateMetadata -PenvironmentName=dev

# Run multiple tasks
./gradlew importEmployees addProcessedCollection
```

## Common Patterns

### Pattern 1: CSV Import with URI Template

```bash
# Import with field-based URIs
flux import-delimited-files \
    --path data/products.csv \
    --connection-string "admin:admin@localhost:8004" \
    --collections product \
    --permissions app-role,read,app-role,update \
    --uri-template "/product/{category}/{id}.json" \
    --json-root-name Product \
    --batch-size 100 \
    --thread-count 32
```

### Pattern 2: Export with Query Filter

```bash
# Export only active employees
flux export-files \
    --connection-string "admin:admin@localhost:8004" \
    --query '{"query": {"and-query": {"queries": [
        {"collection-query": {"uris": ["employee"]}},
        {"range-query": {"json-property": "status", "value": "active"}}
    ]}}}' \
    --path export/active-employees \
    --compression zip \
    --zip-file-count 1 \
    --pretty-print
```

### Pattern 3: Reprocess with Variables

```bash
# Add timestamp to documents
flux reprocess \
    --connection-string "admin:admin@localhost:8004" \
    --read-javascript "var collection; cts.uris(null, null, cts.collectionQuery(collection))" \
    --read-var "collection=employee" \
    --write-javascript "
        var URI;
        var timestamp;
        declareUpdate();
        const doc = cts.doc(URI);
        doc.lastModified = timestamp;
        xdmp.documentInsert(URI, doc);
    " \
    --write-var "timestamp=${date +%Y-%m-%d}" \
    --batch-size 100 \
    --thread-count 32
```

### Pattern 4: Copy with Transformation

```bash
# Copy and add collection
flux copy \
    --connection-string "admin:admin@localhost:8004" \
    --collections source-collection \
    --output-connection-string "admin:admin@localhost:8000" \
    --output-database target-db \
    --output-collections target-collection,copied \
    --output-permissions admin,update \
    --categories content,collections,permissions
```

### Pattern 5: Import from PostgreSQL

```bash
# Import customers from PostgreSQL
flux import-jdbc \
    --jdbc-url "jdbc:postgresql://localhost/sales?user=postgres&password=secret" \
    --jdbc-driver "org.postgresql.Driver" \
    --query "
        SELECT
            c.customer_id,
            c.name,
            c.email,
            c.status,
            COUNT(o.order_id) as order_count
        FROM customers c
        LEFT JOIN orders o ON c.customer_id = o.customer_id
        WHERE c.created_date >= '2024-01-01'
        GROUP BY c.customer_id, c.name, c.email, c.status
    " \
    --connection-string "admin:admin@localhost:8004" \
    --collections customer,imported \
    --permissions app-role,read,app-role,update \
    --uri-template "/customer/{customer_id}.json" \
    --json-root-name Customer \
    --batch-size 50 \
    --thread-count 16
```

### Pattern 6: Export to S3

```bash
# Export to Amazon S3 bucket
flux export-files \
    --connection-string "admin:admin@localhost:8004" \
    --collections backup \
    --path s3a://my-bucket/marklogic-backup/ \
    --s3-add-credentials \
    --compression zip \
    --zip-file-count 10
```

### Pattern 7: Reprocess with Forest Partitions (Large Scale)

```bash
# Reprocess millions of documents efficiently
flux reprocess \
    --connection-string "admin:admin@localhost:8004" \
    --read-partitions-javascript "xdmp.databaseForests(xdmp.database())" \
    --read-javascript "
        cts.uris(null, null, cts.collectionQuery('large-collection'), 0, [PARTITION])
    " \
    --write-javascript "
        var URI;
        declareUpdate();
        xdmp.documentAddCollections(URI, 'reprocessed');
    " \
    --batch-size 100 \
    --thread-count 64 \
    --log-progress 100000
```

### Pattern 8: Options File for Reusability

**options/import-employees.txt:**
```
--connection-string
admin:admin@localhost:8004
--path
data/employees.csv
--collections
employee
--permissions
app-role,read,app-role,update
--uri-template
/employee/{id}.json
--json-root-name
Employee
--batch-size
100
--thread-count
32
```

**Usage:**
```bash
flux import-delimited-files @options/import-employees.txt
```

### Pattern 9: RAG Pipeline (Text Splitting + Embeddings)

```bash
# Copy with text splitting and embeddings for RAG
flux copy \
    --connection-string "admin:admin@localhost:8004" \
    --collections source-documents \
    --output-connection-string "admin:admin@localhost:8004" \
    --output-collections rag-chunks \
    --splitter text \
    --splitter-text-max-chunk-size 1000 \
    --splitter-text-max-overlap-size 100 \
    --embedder minilm \
    --embedder-chunks-json-pointer /chunks \
    --embedder-text-json-pointer /text \
    --embedder-embedding-json-pointer /embedding
```

## Advanced Features

### Forest-Based Partitioning

For large-scale reprocessing, use forest-based partitions to parallelize across Spark workers:

```bash
flux reprocess \
    --connection-string "admin:admin@localhost:8004" \
    --read-partitions-javascript "xdmp.databaseForests(xdmp.database())" \
    --read-javascript "
        cts.uris(null, null, cts.collectionQuery('example'), 0, [PARTITION])
    " \
    --write-javascript "var URI; console.log(URI)" \
    --spark-master-url local[32]
```

**Key Points:**
- Creates one Spark partition per forest
- `[PARTITION]` placeholder replaced with forest ID
- Maximizes parallelism for large datasets

### Snapshot Management

Flux uses point-in-time queries for consistent reads:

```bash
# Default: uses snapshot
flux export-files \
    --connection-string "admin:admin@localhost:8004" \
    --collections example \
    --path export

# Disable snapshot (if merge timestamp not configured)
flux export-files \
    --connection-string "admin:admin@localhost:8004" \
    --collections example \
    --path export \
    --no-snapshot
```

**Configure merge timestamp in MarkLogic:**
```xquery
xquery version "1.0-ml";
import module namespace admin = "http://marklogic.com/xdmp/admin" at "/MarkLogic/admin.xqy";

let $config := admin:get-configuration()
let $dbid := xdmp:database("content-db")
let $config := admin:database-set-merge-timestamp($config, $dbid, -864000000000) (: 24 hours :)
return admin:save-configuration($config)
```

### Custom Spark Code

Execute arbitrary Spark transformations:

```bash
flux custom-code \
    --code "
        spark.read()
            .format('marklogic')
            .option('spark.marklogic.client.uri', 'user:password@localhost:8004')
            .option('spark.marklogic.read.optic.query', 'op.fromView(\"example\", \"employees\", \"\")')
            .load()
            .filter('salary > 50000')
            .groupBy('department')
            .count()
            .show()
    "
```

## MLCP Migration Guide

### MLCP vs Flux Command Mapping

| MLCP Command | Flux Equivalent |
|--------------|-----------------|
| `mlcp.sh import -mode local` | `flux import-files` |
| `mlcp.sh export -mode local` | `flux export-files` |
| `mlcp.sh copy` | `flux copy` |
| CoRB 2 reprocessing | `flux reprocess` |

### MLCP Import → Flux Import

**MLCP:**
```bash
mlcp.sh import \
    -mode local \
    -host localhost \
    -port 8004 \
    -username admin \
    -password admin \
    -input_file_path data/employees.csv \
    -document_type json \
    -output_collections employee \
    -output_permissions app-role,read,app-role,update \
    -output_uri_replace ".*,'/employee/'" \
    -thread_count 32
```

**Flux:**
```bash
flux import-delimited-files \
    --path data/employees.csv \
    --connection-string "admin:admin@localhost:8004" \
    --collections employee \
    --permissions app-role,read,app-role,update \
    --uri-prefix "/employee/" \
    --thread-count 32
```

### MLCP Export → Flux Export

**MLCP:**
```bash
mlcp.sh export \
    -mode local \
    -host localhost \
    -port 8004 \
    -username admin \
    -password admin \
    -output_file_path export \
    -collection_filter employee \
    -compress true \
    -thread_count 32
```

**Flux:**
```bash
flux export-files \
    --connection-string "admin:admin@localhost:8004" \
    --collections employee \
    --path export \
    --compression gzip \
    --thread-count 32
```

### CoRB 2 → Flux Reprocess

**CoRB 2 (via ml-gradle):**
```gradle
task reprocessEmployees(type: com.marklogic.gradle.task.CoRBTask) {
    moduleRoot = "/"
    urisModule = "/corb/employee-uris.xqy"
    processModule = "/corb/process-employee.xqy"
    threadCount = 32
    batchSize = 1
}
```

**Flux (via Gradle):**
```gradle
tasks.register("reprocessEmployees", FluxReprocessTask) {
    reader = "/corb/employee-uris.xqy"
    writer = "/corb/process-employee.xqy"
    threads = 32
    batch = 1
    progress = 10000
}
```

## Best Practices

**Performance:**
- Use `--connection-type DIRECT` for direct cluster access (no load balancer)
- Tune `--batch-size` and `--thread-count` based on cluster capacity
- Use forest-based partitions for large-scale reprocessing
- Enable `--log-progress` for monitoring long-running operations

**Security:**
- Never hardcode passwords; use environment variables
- Use SSL for production: `--ssl-protocol TLSv1.2`
- Apply least-privilege permissions
- Store JDBC passwords in Gradle properties, not code

**Reliability:**
- Use `--preview` and `--count` to validate before full runs
- Test with `--limit 100` on small sample first
- Use options files for repeatable operations
- Enable logging: `--log-progress 10000`

**Data Quality:**
- Validate URI templates produce unique URIs
- Test collections and permissions on small batches
- Use `--pretty-print` for debugging
- Preview data with `--preview 10` before import

## Troubleshooting

**Connection issues:**
```bash
# Test connectivity
flux import-files \
    --connection-string "admin:admin@localhost:8004" \
    --path test.txt \
    --preview

# Check SSL configuration
flux export-files \
    --connection-string "admin:admin@localhost:8004" \
    --collections test \
    --ssl-protocol TLSv1.2 \
    --truststore-path /path/to/truststore.jks \
    --truststore-password secret \
    --preview
```

**Performance issues:**
```bash
# Increase parallelism
flux reprocess \
    --connection-string "admin:admin@localhost:8004" \
    --batch-size 200 \
    --thread-count 64 \
    --spark-master-url local[32]

# Use direct connection (bypass load balancer)
flux import-files \
    --connection-string "admin:admin@localhost:8004" \
    --connection-type DIRECT \
    --path data
```

**Memory issues:**
```bash
# Set Spark memory (via environment variable)
export SPARK_SUBMIT_OPTS="-Xmx4g"

flux import-files \
    --path large-files \
    --connection-string "admin:admin@localhost:8004"
```

**JDBC driver not found:**
```bash
# Copy JDBC driver to flux/ext directory
cp postgresql-42.6.0.jar /path/to/flux-1.4.0/ext/

# Verify
ls flux-1.4.0/ext/
```

## Integration with CI/CD

### GitHub Actions Example

```yaml
name: Data Processing Pipeline

on:
  schedule:
    - cron: '0 2 * * *'  # Daily at 2 AM
  workflow_dispatch:

jobs:
  import-data:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Download Flux
        run: |
          wget https://developer.marklogic.com/download/binaries/flux/flux-1.4.0.zip
          unzip flux-1.4.0.zip

      - name: Import employees
        run: |
          ./flux-1.4.0/bin/flux import-delimited-files \
            --path data/employees.csv \
            --connection-string "${{ secrets.ML_USER }}:${{ secrets.ML_PASS }}@${{ secrets.ML_HOST }}:8004" \
            --collections employee,imported-$(date +%Y%m%d) \
            --permissions app-role,read,app-role,update \
            --uri-template "/employee/{id}.json"

      - name: Reprocess data
        run: |
          ./flux-1.4.0/bin/flux reprocess \
            --connection-string "${{ secrets.ML_USER }}:${{ secrets.ML_PASS }}@${{ secrets.ML_HOST }}:8004" \
            --read-javascript "cts.uris(null, null, cts.collectionQuery('employee'))" \
            --write-javascript "declareUpdate(); xdmp.documentAddCollections(URI, 'processed')" \
            --batch-size 100 \
            --thread-count 32
```

## Bundled Resources

### Scripts (`scripts/`)

**`flux-import.sh`** - Wrapper for common import operations
```bash
./scripts/flux-import.sh employees data/employees.csv
```

**`flux-export-backup.sh`** - Export with timestamp
```bash
./scripts/flux-export-backup.sh production
```

**`flux-reprocess.sh`** - Reprocess with progress logging
```bash
./scripts/flux-reprocess.sh add-timestamp
```

### Example Configs (`assets/`)

- `flux-import-options.txt` - Sample import options file
- `flux-export-options.txt` - Sample export options file
- `flux-reprocess-options.txt` - Sample reprocess options file
- `FluxReprocessTask.groovy` - Complete Gradle task class

### Detailed Reference (`references/`)

- `COMMAND_REFERENCE.md` - Complete list of all Flux commands
- `GRADLE_INTEGRATION.md` - Deep dive on Gradle API usage
- `MIGRATION_GUIDE.md` - Detailed MLCP/CoRB to Flux migration

## Related Skills

For complete MarkLogic development workflow:
- Use **marklogic-ml-gradle** skill for application deployment
- Use **data-manipulation** skill for XQuery data operations
- Use **search-and-query** skill for MarkLogic search capabilities
- Use **xquery-stdlib** skill for XQuery standard functions

This skill focuses on Flux data movement and processing workflows.
