# MLCP and CoRB Migration Guide

Complete guide for migrating from MLCP (MarkLogic Content Pump) and CoRB 2 to MarkLogic Flux.

## Why Migrate to Flux?

**Benefits:**
- ✅ Single tool for all data movement (import, export, reprocess)
- ✅ Better performance via Apache Spark
- ✅ Modern format support (Parquet, Avro, ORC)
- ✅ Cloud storage integration (S3, Azure)
- ✅ RAG pipeline capabilities
- ✅ Active development and support
- ✅ Embeddable API for Gradle/Java

**Migration Path:**
- MLCP → Flux import/export commands
- CoRB 2 → Flux reprocess command
- Both tools remain supported but Flux is recommended for new projects

## MLCP Command Mapping

### Import Operations

**MLCP Import:**
```bash
mlcp.sh import \
    -mode local \
    -host localhost \
    -port 8004 \
    -username admin \
    -password admin \
    -input_file_path data/docs \
    -document_type json \
    -output_collections imported \
    -output_permissions role,read,role,update \
    -output_uri_prefix /documents/ \
    -thread_count 32
```

**Flux Equivalent:**
```bash
flux import-files \
    --path data/docs \
    --connection-string "admin:admin@localhost:8004" \
    --document-type JSON \
    --collections imported \
    --permissions role,read,role,update \
    --uri-prefix /documents/ \
    --thread-count 32
```

### Export Operations

**MLCP Export:**
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

**Flux Equivalent:**
```bash
flux export-files \
    --connection-string "admin:admin@localhost:8004" \
    --collections employee \
    --path export \
    --compression gzip \
    --thread-count 32
```

### CSV Import

**MLCP CSV Import:**
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
    -output_permissions role,read,role,update \
    -output_uri_replace ".*,'/employee/'" \
    -transform_module /transforms/csv-transform.xqy
```

**Flux Equivalent:**
```bash
flux import-delimited-files \
    --path data/employees.csv \
    --connection-string "admin:admin@localhost:8004" \
    --collections employee \
    --permissions role,read,role,update \
    --uri-prefix /employee/ \
    --json-root-name Employee \
    --transform csv-transform \
    --transform-params "param,value"
```

### Copy Between Databases

**MLCP Copy:**
```bash
mlcp.sh copy \
    -mode local \
    -input_host localhost \
    -input_port 8004 \
    -input_username admin \
    -input_password admin \
    -output_host localhost \
    -output_port 8000 \
    -output_username admin \
    -output_password admin \
    -collection_filter employee \
    -thread_count 32
```

**Flux Equivalent:**
```bash
flux copy \
    --connection-string "admin:admin@localhost:8004" \
    --collections employee \
    --output-connection-string "admin:admin@localhost:8000" \
    --thread-count 32
```

## MLCP Option Mapping

| MLCP Option | Flux Equivalent | Notes |
|-------------|----------------|-------|
| `-mode local` | (not needed) | Flux always runs locally |
| `-host` | `--host` or in `--connection-string` | Connection string preferred |
| `-port` | `--port` or in `--connection-string` | Connection string preferred |
| `-username` | `--username` or in `--connection-string` | Connection string preferred |
| `-password` | `--password` or in `--connection-string` | Connection string preferred |
| `-database` | `--database` or in `--connection-string` | Connection string preferred |
| `-input_file_path` | `--path` | |
| `-output_file_path` | `--path` | |
| `-document_type` | `--document-type` | |
| `-output_collections` | `--collections` | |
| `-output_permissions` | `--permissions` | |
| `-output_uri_prefix` | `--uri-prefix` | |
| `-output_uri_suffix` | `--uri-suffix` | |
| `-output_uri_replace` | `--uri-replace` | |
| `-thread_count` | `--thread-count` | |
| `-batch_size` | `--batch-size` | |
| `-transform_module` | `--transform` | |
| `-transform_param` | `--transform-params` | |
| `-collection_filter` | `--collections` | |
| `-directory_filter` | `--directory` | |
| `-compress` | `--compression` | Values: gzip, zip |
| `-ssl` | `--ssl-protocol` | |
| `-input_compressed` | (auto-detected) | Flux auto-detects .gz, .zip |

## CoRB Migration

### Basic CoRB Reprocessing

**CoRB XML Configuration:**
```xml
<property name="XCC-CONNECTION-URI" value="xcc://admin:admin@localhost:8004"/>
<property name="URIS-MODULE" value="/corb/employee-uris.xqy"/>
<property name="PROCESS-MODULE" value="/corb/process-employee.xqy"/>
<property name="THREAD-COUNT" value="32"/>
<property name="BATCH-SIZE" value="1"/>
```

**Flux Equivalent:**
```bash
flux reprocess \
    --connection-string "admin:admin@localhost:8004" \
    --read-invoke /corb/employee-uris.xqy \
    --write-invoke /corb/process-employee.xqy \
    --thread-count 32 \
    --batch-size 1 \
    --log-progress 10000
```

### CoRB with Variables

**CoRB:**
```xml
<property name="XCC-CONNECTION-URI" value="xcc://admin:admin@localhost:8004"/>
<property name="URIS-MODULE" value="/corb/uris.xqy"/>
<property name="PROCESS-MODULE" value="/corb/process.xqy"/>
<property name="URIS-MODULE.collection" value="employee"/>
<property name="PROCESS-MODULE.status" value="active"/>
```

**Flux Equivalent:**
```bash
flux reprocess \
    --connection-string "admin:admin@localhost:8004" \
    --read-invoke /corb/uris.xqy \
    --read-var "collection=employee" \
    --write-invoke /corb/process.xqy \
    --write-var "status=active" \
    --thread-count 32 \
    --batch-size 1
```

### CoRB Gradle Task Migration

**Old CoRB Task:**
```gradle
task reprocessEmployees(type: com.marklogic.gradle.task.CoRBTask) {
    moduleRoot = "/"
    urisModule = "/corb/employee-uris.xqy"
    processModule = "/corb/process-employee.xqy"
    threadCount = 32
    batchSize = 1
    additionalOptions = [
        "collection": "employee"
    ]
}
```

**New Flux Task:**
```gradle
tasks.register("reprocessEmployees", FluxReprocessTask) {
    group = "Data Processing"
    description = "Reprocess employee documents"
    reader = "/corb/employee-uris.xqy"
    writer = "/corb/process-employee.xqy"
    threads = 32
    batch = 1
    progress = 10000
    readVars = ["collection=employee"]
}
```

## Migration Checklist

### Phase 1: Assessment (1-2 days)

- [ ] Inventory all MLCP commands in scripts
- [ ] Inventory all CoRB jobs
- [ ] Identify custom MLCP transforms
- [ ] Identify CoRB module dependencies
- [ ] Document current data workflows

### Phase 2: Testing (1-2 weeks)

- [ ] Install Flux on test environment
- [ ] Convert one MLCP import to Flux
- [ ] Convert one MLCP export to Flux
- [ ] Convert one CoRB job to Flux
- [ ] Test performance comparison
- [ ] Validate data integrity

### Phase 3: Migration (2-4 weeks)

- [ ] Convert all MLCP imports to Flux
- [ ] Convert all MLCP exports to Flux
- [ ] Convert all CoRB jobs to Flux
- [ ] Update Gradle tasks
- [ ] Update CI/CD pipelines
- [ ] Create Flux options files
- [ ] Document new commands

### Phase 4: Validation (1 week)

- [ ] Run all Flux commands end-to-end
- [ ] Verify data integrity
- [ ] Benchmark performance
- [ ] Update documentation
- [ ] Train team members
- [ ] Decommission MLCP/CoRB (optional)

## Common Migration Issues

### Issue 1: Connection String Format

**Problem:** MLCP uses `-host`, `-port`, `-username`, `-password`

**Solution:** Combine into Flux connection string
```bash
# MLCP
-host localhost -port 8004 -username admin -password admin

# Flux
--connection-string "admin:admin@localhost:8004"
```

### Issue 2: URI Templates

**Problem:** MLCP `-output_uri_replace` uses regex

**Solution:** Flux `--uri-template` uses field placeholders
```bash
# MLCP
-output_uri_replace ".*customers/(.*)\.csv,'/customer/$1.json'"

# Flux
--uri-template "/customer/{id}.json"
```

### Issue 3: Transform Modules

**Problem:** MLCP transforms use `-transform_module` and `-transform_param`

**Solution:** Flux uses `--transform` and `--transform-params`
```bash
# MLCP
-transform_module /transforms/enrich.xqy
-transform_param "source,external,date,2024-01-01"

# Flux
--transform enrich
--transform-params "source,external,date,2024-01-01"
```

### Issue 4: Compressed Input

**Problem:** MLCP requires `-input_compressed true`

**Solution:** Flux auto-detects .gz and .zip files
```bash
# MLCP
-input_file_path data.csv.gz -input_compressed true

# Flux (auto-detected)
--path data.csv.gz
```

### Issue 5: CoRB Batch Processing

**Problem:** CoRB batches URIs in PROCESS-MODULE

**Solution:** Flux provides URIs as comma-separated string in `URI` variable
```javascript
// CoRB (receives array)
var uris; // external variable
for (var uri of uris) {
    // process uri
}

// Flux (receives comma-separated string)
var URI; // provided by Flux
for (var uri of URI.split(',')) {
    // process uri
}
```

## Performance Comparison

| Operation | MLCP | Flux | Speedup |
|-----------|------|------|---------|
| Import 1M JSON docs | 15 min | 10 min | 1.5x |
| Export 1M docs | 20 min | 12 min | 1.7x |
| Reprocess 1M docs | 30 min (CoRB) | 18 min | 1.7x |

**Performance Tips:**
- Use `--connection-type DIRECT` for cluster access
- Increase `--thread-count` to match app server threads
- Use `--batch-size` appropriate for operation
- Enable forest-based partitions for large datasets

## Best Practices for Migration

1. **Start Small:** Migrate one workflow at a time
2. **Test Thoroughly:** Validate data integrity after migration
3. **Keep MLCP/CoRB:** Run both tools in parallel initially
4. **Document Changes:** Update runbooks and documentation
5. **Train Team:** Ensure team understands new commands
6. **Use Options Files:** Create reusable Flux option files
7. **Leverage Gradle:** Use Flux API for complex workflows
8. **Monitor Performance:** Compare before/after metrics

## Getting Help

- **Documentation:** https://docs.marklogic.com/guide/flux
- **GitHub Issues:** https://github.com/marklogic/flux
- **MarkLogic Community:** https://community.marklogic.com/
- **Support:** Open ticket with MarkLogic Support

## Next Steps

After migration:
1. Remove MLCP/CoRB dependencies from build files
2. Update CI/CD pipelines
3. Archive old scripts
4. Share learnings with team
5. Explore new Flux features (RAG, cloud storage)
