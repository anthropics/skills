import org.gradle.api.DefaultTask
import org.gradle.api.tasks.TaskAction
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.Optional
import org.gradle.api.Project
import com.marklogic.flux.api.Flux
import org.apache.spark.sql.SparkSession

/**
 * Custom Gradle task for running MarkLogic Flux reprocess operations.
 *
 * Usage:
 * tasks.register("myTask", FluxReprocessTask) {
 *     reader = "/queries/my-uris.xqy"
 *     writer = "/transforms/my-transform.xqy"
 *     threads = 32
 *     batch = 1
 *     progress = 10000
 *     readVars = ["status=active", "date=2024-01-01"]
 *     writeVars = ["collection=processed"]
 * }
 */
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

/**
 * Helper class for Flux Gradle integration
 */
class FluxHelpers {
    static String toFluxConn(Project project) {
        def user = project.findProperty("mlUsername") ?: "admin"
        def pass = project.findProperty("mlPassword") ?: "admin"
        def host = project.findProperty("mlHost") ?: "localhost"
        def port = project.findProperty("mlRestPort") ?: "8004"
        return "${user}:${pass}@${host}:${port}"
    }
}
