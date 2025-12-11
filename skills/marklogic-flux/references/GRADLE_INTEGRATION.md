# MarkLogic Flux Gradle Integration Guide

Complete guide for integrating MarkLogic Flux with Gradle build workflows.

## Setup

### Add Flux Dependency

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

## Custom Task Classes

### FluxReprocessTask

Complete implementation for reprocessing documents:

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
```

### Helper Classes

**buildSrc/src/main/groovy/FluxHelpers.groovy:**
```groovy
import org.gradle.api.Project

class FluxHelpers {
    static String toFluxConn(Project project) {
        def user = project.findProperty("mlUsername") ?: "admin"
        def pass = project.findProperty("mlPassword") ?: "admin"
        def host = project.findProperty("mlHost") ?: "localhost"
        def port = project.findProperty("mlRestPort") ?: "8004"
        return "${user}:${pass}@${host}:${port}"
    }

    static String getConnectionString(Project project, String env = null) {
        def envSuffix = env ? "-${env}" : ""
        def user = project.findProperty("mlUsername${envSuffix}") ?: "admin"
        def pass = project.findProperty("mlPassword${envSuffix}") ?: "admin"
        def host = project.findProperty("mlHost${envSuffix}") ?: "localhost"
        def port = project.findProperty("mlRestPort${envSuffix}") ?: "8004"
        return "${user}:${pass}@${host}:${port}"
    }
}
```

## Task Patterns

### Pattern 1: Simple Import Task

```gradle
tasks.register("importEmployees") {
    group = "Data Loading"
    description = "Import employee CSV files"
    doLast {
        Flux.importDelimitedFiles()
            .connectionString(FluxHelpers.toFluxConn(project))
            .from { options ->
                options.paths("data/employees.csv")
            }
            .to { options ->
                options.collections("employee")
                    .permissionsString("app-role,read,app-role,update")
                    .uriTemplate("/employee/{id}.json")
            }
            .execute()
        println "Import completed."
    }
}
```

### Pattern 2: Export Task with Environment

```gradle
tasks.register("exportEmployees") {
    group = "Data Export"
    description = "Export employee documents"
    doLast {
        def env = project.findProperty("env") ?: "dev"
        def outputDir = "export/${env}/employees"

        Flux.exportFiles()
            .connectionString(FluxHelpers.getConnectionString(project, env))
            .from { options ->
                options.collections("employee")
            }
            .to { options ->
                options.path(outputDir)
                    .compression("zip")
                    .zipFileCount(1)
            }
            .execute()
        println "Export to ${outputDir} completed."
    }
}
```

### Pattern 3: Reprocess with Variables

```gradle
tasks.register("addTimestamp", FluxReprocessTask) {
    group = "Data Processing"
    description = "Add timestamp to employee documents"
    reader = "/queries/employee-uris.xqy"
    writer = "/transforms/add-timestamp.xqy"
    threads = 32
    batch = 1
    progress = 10000
    writeVars = ["timestamp=${new Date().time}"]
}
```

### Pattern 4: Conditional Task

```gradle
tasks.register("conditionalImport") {
    group = "Data Loading"
    description = "Import if file exists"
    doLast {
        def csvFile = file("data/new-employees.csv")
        if (!csvFile.exists()) {
            println "No new employees file found. Skipping import."
            return
        }

        Flux.importDelimitedFiles()
            .connectionString(FluxHelpers.toFluxConn(project))
            .from { options ->
                options.paths(csvFile.absolutePath)
            }
            .to { options ->
                options.collections("employee", "new")
                    .permissionsString("app-role,read,app-role,update")
            }
            .execute()
        println "Imported ${csvFile.name}"
    }
}
```

### Pattern 5: Multi-Step Workflow

```gradle
tasks.register("loadAndProcess") {
    group = "Data Workflows"
    description = "Load data and process it"
    doLast {
        def conn = FluxHelpers.toFluxConn(project)

        // Step 1: Import
        println "Step 1: Importing data..."
        Flux.importDelimitedFiles()
            .connectionString(conn)
            .from { it.paths("data/employees.csv") }
            .to { it.collections("employee", "unprocessed") }
            .execute()

        // Step 2: Reprocess
        println "Step 2: Processing data..."
        SparkSession spark = SparkSession.builder()
            .appName("LoadAndProcess")
            .master("local[*]")
            .getOrCreate()

        try {
            Flux.reprocess()
                .connectionString(conn)
                .withSparkSession(spark)
                .from { it.invoke("/queries/unprocessed-uris.xqy") }
                .to { it.invoke("/transforms/process-employee.xqy") }
                .execute()
        } finally {
            spark.stop()
        }

        println "Workflow completed."
    }
}
```

### Pattern 6: Copy Between Environments

```gradle
tasks.register("copyToTest") {
    group = "Data Migration"
    description = "Copy employee data from dev to test"
    doLast {
        def sourceConn = FluxHelpers.getConnectionString(project, "dev")
        def targetConn = FluxHelpers.getConnectionString(project, "test")

        Flux.copy()
            .connectionString(sourceConn)
            .from { options ->
                options.collections("employee")
                    .stringQuery("status:active")
            }
            .to { options ->
                options.connectionString(targetConn)
                    .collections("employee", "migrated")
                    .categories("content", "collections", "permissions")
            }
            .execute()
        println "Copy from dev to test completed."
    }
}
```

## Advanced Patterns

### Pattern 7: Parallel Imports

```gradle
tasks.register("parallelImports") {
    group = "Data Loading"
    description = "Import multiple datasets in parallel"
    doLast {
        def conn = FluxHelpers.toFluxConn(project)
        def datasets = [
            [file: "data/employees.csv", collection: "employee"],
            [file: "data/departments.csv", collection: "department"],
            [file: "data/locations.csv", collection: "location"]
        ]

        datasets.parallelStream().forEach { dataset ->
            println "Importing ${dataset.file}..."
            Flux.importDelimitedFiles()
                .connectionString(conn)
                .from { it.paths(dataset.file) }
                .to { it.collections(dataset.collection) }
                .execute()
        }
        println "All imports completed."
    }
}
```

### Pattern 8: Import with Validation

```gradle
tasks.register("importWithValidation") {
    group = "Data Loading"
    description = "Import and validate data"
    doLast {
        def csvFile = file("data/employees.csv")

        // Validate file exists
        if (!csvFile.exists()) {
            throw new FileNotFoundException("File not found: ${csvFile}")
        }

        // Count rows before import
        def lineCount = csvFile.readLines().size() - 1 // Exclude header
        println "Importing ${lineCount} employees..."

        def conn = FluxHelpers.toFluxConn(project)

        Flux.importDelimitedFiles()
            .connectionString(conn)
            .from { it.paths(csvFile.absolutePath) }
            .to { it.collections("employee") }
            .execute()

        // Validate import (simplified - would use REST API in production)
        println "Import completed. Expected: ${lineCount} documents"
    }
}
```

### Pattern 9: Export with Timestamp

```gradle
tasks.register("exportBackup") {
    group = "Data Export"
    description = "Export backup with timestamp"
    doLast {
        def timestamp = new Date().format("yyyyMMdd_HHmmss")
        def collection = project.findProperty("collection") ?: "employee"
        def outputDir = "backup/${collection}/${timestamp}"

        Flux.exportArchives()
            .connectionString(FluxHelpers.toFluxConn(project))
            .from { options ->
                options.collections(collection)
            }
            .to { options ->
                options.path(outputDir)
                    .categories("content", "collections", "permissions", "metadata")
            }
            .execute()

        println "Backup completed: ${outputDir}"
        println "Backup size: ${new File(outputDir).directorySize()} bytes"
    }
}
```

### Pattern 10: Scheduled Task

```gradle
tasks.register("dailySync") {
    group = "Data Workflows"
    description = "Daily data synchronization"
    doLast {
        def today = new Date().format("yyyy-MM-dd")
        println "Running daily sync for ${today}..."

        def conn = FluxHelpers.toFluxConn(project)

        // Import new data
        Flux.importDelimitedFiles()
            .connectionString(conn)
            .from { it.paths("data/daily/${today}.csv") }
            .to { it.collections("daily-import", today) }
            .execute()

        // Process imported data
        SparkSession spark = SparkSession.builder()
            .appName("DailySync")
            .master("local[*]")
            .getOrCreate()

        try {
            Flux.reprocess()
                .connectionString(conn)
                .withSparkSession(spark)
                .from { it
                    .javascript("cts.uris(null, null, cts.collectionQuery('${today}'))")
                }
                .to { it
                    .javascript("declareUpdate(); xdmp.documentAddCollections(URI, 'processed')")
                }
                .execute()
        } finally {
            spark.stop()
        }

        println "Daily sync completed for ${today}"
    }
}
```

## Environment Configuration

### gradle.properties

```properties
# Local development
mlHost=localhost
mlRestPort=8004
mlUsername=admin
mlPassword=admin

# SSL flag
sslFlag=false
```

### gradle-dev.properties

```properties
mlHost-dev=dev-server.example.com
mlRestPort-dev=8010
mlUsername-dev=dev-user
mlPassword-dev=dev-password
```

### gradle-test.properties

```properties
mlHost-test=test-server.example.com
mlRestPort-test=9010
mlUsername-test=test-user
mlPassword-test=test-password
sslFlag=true
```

## Testing

### Unit Test with Spock

```groovy
import spock.lang.Specification
import com.marklogic.flux.api.Flux

class FluxTaskSpec extends Specification {

    def "test import creates task"() {
        given:
        def project = ProjectBuilder.builder().build()

        when:
        project.tasks.register("testImport") {
            doLast {
                // Mock import
            }
        }

        then:
        project.tasks.findByName("testImport") != null
    }
}
```

## Troubleshooting

### Issue 1: ClassNotFoundException

**Problem:** `java.lang.ClassNotFoundException: com.marklogic.flux.api.Flux`

**Solution:** Add dependency to buildSrc/build.gradle
```gradle
dependencies {
    implementation "com.marklogic:flux-api:1.4.0"
}
```

### Issue 2: Jackson Version Conflicts

**Problem:** `com.fasterxml.jackson.databind.JsonMappingException`

**Solution:** Force Jackson version in buildSrc
```gradle
configurations.all {
    resolutionStrategy.eachDependency { details ->
        if (details.requested.group.startsWith('com.fasterxml.jackson')) {
            details.useVersion '2.15.2'
        }
    }
}
```

### Issue 3: Spark Memory Issues

**Problem:** `java.lang.OutOfMemoryError: Java heap space`

**Solution:** Set Spark memory in gradle.properties
```properties
org.gradle.jvmargs=-Xmx4g
```

## Best Practices

1. **Use Custom Task Classes:** Create reusable task types
2. **Externalize Configuration:** Use gradle.properties for environments
3. **Add Error Handling:** Wrap Flux calls in try-catch
4. **Log Progress:** Use `.logProgress()` for long operations
5. **Validate Inputs:** Check file existence before import
6. **Clean Up Resources:** Always stop SparkSession in finally block
7. **Document Tasks:** Add group and description to all tasks
8. **Version Control:** Store task code in buildSrc, not build.gradle

## Next Steps

- Create custom task classes for your workflows
- Set up environment-specific properties
- Add Flux tasks to CI/CD pipelines
- Migrate existing MLCP/CoRB tasks to Flux
- Explore Flux RAG capabilities for AI workflows
