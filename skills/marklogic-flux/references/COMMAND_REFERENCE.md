# MarkLogic Flux Command Reference

Complete reference for all MarkLogic Flux commands with options.

## Import Commands

### import-files
Generic file import - supports any file type.

```bash
flux import-files \
    --path <directory-or-file> \
    --connection-string "user:password@host:port" \
    --collections <collections> \
    --permissions <permissions>
```

**Key Options:**
- `--path` - Directory or file path
- `--document-type` - JSON, XML, TEXT, BINARY (auto-detected if not specified)
- `--uri-template` - URI template with {filename} placeholder
- `--encoding` - File encoding (UTF-8, ISO-8859-1, etc.)
- `--filter` - Glob pattern to filter files

### import-delimited-files
Import CSV/TSV files as JSON or XML documents.

```bash
flux import-delimited-files \
    --path <csv-file> \
    --connection-string "user:password@host:port" \
    --json-root-name <root-element> \
    --collections <collections>
```

**Key Options:**
- `--json-root-name` - Root name for JSON documents
- `--xml-root-name` - Root name for XML documents
- `--xml-namespace` - XML namespace
- `--delimiter` - Field delimiter (default: comma)
- `--uri-template` - URI template with column names as placeholders

### import-json-files
Import JSON or JSONL files.

```bash
flux import-json-files \
    --path <json-files> \
    --connection-string "user:password@host:port" \
    --collections <collections>
```

**Key Options:**
- `--json-lines` - Treat as JSONL (one JSON per line)
- `--json-root-name` - Wrap in root object

### import-xml-files
Import XML files.

```bash
flux import-xml-files \
    --path <xml-files> \
    --connection-string "user:password@host:port" \
    --collections <collections>
```

### import-parquet-files
Import Parquet files (columnar format).

```bash
flux import-parquet-files \
    --path <parquet-files> \
    --connection-string "user:password@host:port" \
    --json-root-name <root-name>
```

### import-avro-files
Import Avro files (binary serialization format).

```bash
flux import-avro-files \
    --path <avro-files> \
    --connection-string "user:password@host:port" \
    --json-root-name <root-name>
```

### import-orc-files
Import ORC files (optimized row columnar).

```bash
flux import-orc-files \
    --path <orc-files> \
    --connection-string "user:password@host:port" \
    --json-root-name <root-name>
```

### import-jdbc
Import data from RDBMS via JDBC.

```bash
flux import-jdbc \
    --jdbc-url "jdbc:postgresql://host/db?user=u&password=p" \
    --jdbc-driver "org.postgresql.Driver" \
    --query "SELECT * FROM table" \
    --connection-string "user:password@host:port"
```

**Key Options:**
- `--jdbc-url` - JDBC connection URL
- `--jdbc-driver` - JDBC driver class name
- `--query` - SQL query
- Driver JAR must be in `flux/ext/` directory

### import-archives
Import MarkLogic archive files (created with export-archives).

```bash
flux import-archives \
    --path <archive-directory> \
    --connection-string "user:password@host:port"
```

**Key Options:**
- `--categories` - Metadata to restore (content, collections, permissions, metadata, properties)
- Preserves all original metadata

## Export Commands

### export-files
Export documents to files in original format.

```bash
flux export-files \
    --connection-string "user:password@host:port" \
    --collections <collections> \
    --path <output-directory>
```

**Key Options:**
- `--compression` - gzip, zip, or none
- `--zip-file-count` - Number of ZIP files to create
- `--pretty-print` - Format JSON/XML output
- `--encoding` - Output encoding
- `--file-count` - Number of output files

### export-parquet-files
Export rows to Parquet files.

```bash
flux export-parquet-files \
    --connection-string "user:password@host:port" \
    --query "op.fromView('schema', 'view', '')" \
    --path <output-directory>
```

**Key Options:**
- Requires Optic query (TDE views or op.fromDocUris)
- Efficient for analytics workflows

### export-avro-files
Export rows to Avro files.

```bash
flux export-avro-files \
    --connection-string "user:password@host:port" \
    --query "op.fromView('schema', 'view', '')" \
    --path <output-directory>
```

### export-delimited-files
Export rows to CSV/TSV files.

```bash
flux export-delimited-files \
    --connection-string "user:password@host:port" \
    --query "op.fromView('schema', 'view', '')" \
    --path <output-file.csv>
```

**Key Options:**
- `--delimiter` - Field delimiter
- `--header` - Include header row (default: true)

### export-jdbc
Export rows to RDBMS via JDBC.

```bash
flux export-jdbc \
    --connection-string "user:password@host:port" \
    --query "op.fromView('schema', 'view', '')" \
    --jdbc-url "jdbc:postgresql://host/db?user=u&password=p" \
    --jdbc-driver "org.postgresql.Driver" \
    --table "target_table"
```

### export-archives
Export documents with metadata to archive files.

```bash
flux export-archives \
    --connection-string "user:password@host:port" \
    --collections <collections> \
    --path <output-directory>
```

**Key Options:**
- `--categories` - Metadata to export (content, collections, permissions, metadata, properties)
- Preserves all metadata for restoration

## Processing Commands

### reprocess
Execute custom JavaScript code on existing documents.

```bash
flux reprocess \
    --connection-string "user:password@host:port" \
    --read-javascript "cts.uris(null, null, cts.collectionQuery('example'))" \
    --write-javascript "declareUpdate(); xdmp.documentAddCollections(URI, 'new')"
```

**Key Options:**
- `--read-javascript` - JavaScript to generate URIs
- `--read-xquery` - XQuery to generate URIs
- `--write-javascript` - JavaScript to process each URI
- `--write-xquery` - XQuery to process each URI
- `--read-var` - Variables for read query
- `--write-var` - Variables for write query
- `--read-partitions-javascript` - JavaScript for partition values
- `--batch-size` - URIs per batch
- Special variable: `URI` - current document URI(s)

### copy
Copy documents between databases.

```bash
flux copy \
    --connection-string "user:password@host:port" \
    --collections <source-collections> \
    --output-connection-string "user:password@target-host:port" \
    --output-database <target-database>
```

**Key Options:**
- All query options (collections, query, string-query, etc.)
- `--output-*` options for target database
- `--categories` - Metadata to copy
- Can copy within same cluster or between clusters

### custom-code
Execute arbitrary Spark code.

```bash
flux custom-code \
    --code "spark.read().format('marklogic')...show()"
```

**Key Options:**
- Direct access to SparkSession
- For advanced Spark workflows

## Common Options (All Commands)

### Connection Options

```bash
# Connection String (Recommended)
--connection-string "user:password@host:port/database"

# Individual Options
--host <hostname>
--port <port>
--username <user>
--password <password>
--database <database>

# Connection Type
--connection-type DIRECT|GATEWAY

# SSL Configuration
--ssl-protocol TLSv1.2
--keystore-path <path>
--keystore-password <password>
--truststore-path <path>
--truststore-password <password>

# Authentication
--auth-type BASIC|DIGEST|CLOUD|CERTIFICATE|KERBEROS|OAUTH|SAML
```

### Document Options

```bash
# Collections
--collections <col1,col2>
--output-collections <col1,col2>

# Permissions
--permissions <role,capability,role,capability>
--output-permissions <role,capability>

# URI Control
--uri-template "/path/{field}.json"
--uri-prefix "/prefix/"
--uri-suffix ".json"
--uri-replace "pattern,replacement"
```

### Query Options (Export/Copy)

```bash
# Collection Filter
--collections <collections>

# Directory Filter
--directory <directory>

# String Query
--string-query "search terms"

# Structured Query
--query '{"query": {...}}'

# URI List
--uris "/uri1\n/uri2"
--uris-file <file>

# Limit
--limit <number>
```

### Performance Options

```bash
# Batch Processing
--batch-size <size>
--thread-count <threads>

# Spark Configuration
--spark-master-url local[N]
--partitions-per-forest <number>
--repartition <number>

# Connection Optimization
--connection-type DIRECT
--disable-gzipped-responses

# Logging
--log-progress <interval>
--log-read-progress <interval>
```

### Preview and Testing

```bash
# Preview Data
--preview <rows>
--preview-drop <columns>
--preview-list
--preview-schema

# Count Without Processing
--count

# Limit Processing
--limit <number>
```

### File Options

```bash
# Path
--path <path>

# Compression
--compression gzip|zip
--zip-file-count <number>

# Format
--encoding <encoding>
--pretty-print

# Filtering
--filter <glob-pattern>
```

### Cloud Storage Options

```bash
# Amazon S3
--path s3a://bucket/path
--s3-add-credentials
--s3-access-key-id <key>
--s3-secret-access-key <secret>
--s3-endpoint <endpoint>

# Azure Blob Storage
--path wasbs://container@account.blob.core.windows.net/path
--azure-storage-account <account>
--azure-storage-sas-token <token>
```

### RAG Pipeline Options

```bash
# Text Splitting
--splitter text|json|regex
--splitter-text-max-chunk-size <size>
--splitter-text-max-overlap-size <size>
--splitter-json-pointer <pointer>

# Embeddings
--embedder minilm|sentence-transformers
--embedder-chunks-json-pointer <pointer>
--embedder-text-json-pointer <pointer>
--embedder-embedding-json-pointer <pointer>
```

## Options File Format

Create a text file with one option per line:

```
# Import options
--connection-string
admin:admin@localhost:8004
--path
data/files
--collections
imported
```

Use with: `flux import-files @options.txt`

## Environment Variables

```bash
# Spark Memory
export SPARK_SUBMIT_OPTS="-Xmx4g"

# Hadoop Config (for S3/Azure)
export HADOOP_CONF_DIR=/path/to/hadoop/conf
```

## Exit Codes

- `0` - Success
- `1` - Error occurred
- Check logs for detailed error messages
