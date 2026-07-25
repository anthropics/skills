---
name: azure-hdinsight
description: Expert knowledge for Azure HDInsight development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when working with HDInsight Spark/Hive/Kafka/HBase clusters, Ambari/Oozie pipelines, or Azure-integrated storage/BI, and other Azure HDInsight related development tasks. Not for Azure Databricks (use azure-databricks), Azure Synapse Analytics (use azure-synapse-analytics), Azure Stream Analytics (use azure-stream-analytics).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure HDInsight Skill

This skill provides expert guidance for Azure HDInsight. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L132 | Diagnosing and fixing HDInsight cluster issues: creation/auth, networking, storage, Ambari/HDFS/Hive/HBase/Kafka/Spark/YARN problems, performance, disk/CPU, and known error codes/workarounds. |
| Best Practices | L133-L174 | Best practices for designing, securing, monitoring, scaling, and tuning HDInsight clusters and workloads (Hadoop, Spark, Hive, HBase, Kafka), including storage, migration, and performance optimization. |
| Decision Making | L175-L200 | Planning HDInsight capacity, networking, storage, and VM sizes, plus detailed migration/upgrade paths for Hadoop, HBase, Kafka, Ambari, and HDInsight versions and load balancers. |
| Architecture & Design Patterns | L201-L215 | HDInsight cluster architecture, security, networking, HA/DR, migration from on-prem Hadoop, shared storage, streaming design, and operational pipelines with Ambari/Oozie |
| Limits & Quotas | L216-L225 | HDInsight capacity limits, node configs, Kafka-specific limits, metastore constraints, log sizing/retention, and how to request/manage CPU core quota increases. |
| Security | L226-L269 | Securing HDInsight clusters: identity and access (Entra, LDAP, Ranger, RBAC), network isolation (NSG, Private Link), TLS/encryption, Kafka/Hive/Spark security, and security best practices. |
| Configuration | L270-L326 | Configuring and tuning HDInsight clusters: networking/VPN, Ambari/Hive/Spark/HBase settings, autoscale, monitoring/logging, SSH/Jupyter/VS Code access, and script-based customizations. |
| Integrations & Coding Patterns | L327-L394 | Patterns and code samples for integrating HDInsight (Hive, Spark, Kafka, HBase, MapReduce, Sqoop) with tools, SDKs, REST/CLI, and external services like SQL, Cosmos DB, Power BI, IoT, and Synapse |
| Deployment | L395-L408 | Creating, configuring, migrating, and automating HDInsight clusters (Hadoop, HBase, Kafka) using portal, CLI, PowerShell, ARM/REST, Data Factory, Marketplace, AMA, and runbooks |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Address reliability issues on older HDInsight images | https://learn.microsoft.com/en-us/azure/hdinsight/cluster-reliability-issues |
| Fix component version validation errors in HDInsight ARM templates | https://learn.microsoft.com/en-us/azure/hdinsight/component-version-validation-error-arm-templates |
| Troubleshoot Azure HDInsight cluster creation errors | https://learn.microsoft.com/en-us/azure/hdinsight/create-cluster-error-dictionary |
| Troubleshoot authentication issues for secure HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/domain-joined-authentication-issues |
| Run diagnostic script when HDInsight cluster creation fails with DomainNotFound | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/sample-script |
| Fix DomainNotFound errors during HDInsight cluster creation | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/troubleshoot-domainnotfound |
| Fix Apache Ambari directory alerts in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-ambari-troubleshoot-directory-alerts |
| Troubleshoot Ambari UI down hosts and services in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-ambari-troubleshoot-down-hosts-services |
| Fix Apache Ambari UI 502 errors on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-ambari-troubleshoot-fivezerotwo-error |
| Resolve Apache Ambari heartbeat issues in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-ambari-troubleshoot-heartbeat-issues |
| Troubleshoot Apache Ambari Metrics Collector on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-ambari-troubleshoot-metricservice-issues |
| Resolve Apache Ambari stale alerts in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-ambari-troubleshoot-stale-alerts |
| Fix local HDFS stuck in safe mode on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-hdfs-troubleshoot-safe-mode |
| Fix HDInsight cluster creation failures | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-troubleshoot-cluster-creation-fails |
| Convert service principal certificates to base-64 for HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-troubleshoot-converting-service-principal-certificate |
| Resolve Data Lake storage file access issues in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-troubleshoot-data-lake-files |
| Fix InvalidNetworkSecurityGroupSecurityRules for HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-troubleshoot-invalidnetworksecuritygroupsecurityrules-cluster-creation-fails |
| Resolve HDInsight node disk space exhaustion | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-troubleshoot-out-disk-space |
| Fix Watchdog BUG soft lockup CPU errors in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-troubleshoot-soft-lockup-cpu |
| Resolve node addition failures in HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-troubleshoot-unable-add-nodes |
| Troubleshoot login failures to HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-troubleshoot-unable-log-in-cluster |
| Manage and troubleshoot disk space issues in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/troubleshoot-disk-space |
| Resolve InvalidNetworkConfigurationErrorCode in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/troubleshoot-invalidnetworkconfigurationerrorcode-cluster-creation-fails |
| Restore Key Vault access for encrypted HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/troubleshoot-lost-key-vault-access |
| Fix port conflicts when starting HDInsight services | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/troubleshoot-port-conflict |
| Fix 'account does not support http' storage errors in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/troubleshoot-wasbs-storage-exception |
| Fix invalid BCFile errors when reading YARN logs | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/troubleshoot-yarn-log-invalid-bcfile |
| Resolve BindException address-in-use on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-bindexception-address-use |
| Fix HBase hbck inconsistency errors on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-hbase-hbck-inconsistencies |
| Troubleshoot pegged CPU on HBase region servers | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-pegged-cpu-region-server |
| Resolve Apache Phoenix connectivity issues on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-phoenix-connectivity |
| Fix missing data in Phoenix views after HDP upgrade | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-phoenix-no-data |
| Fix HBase REST service not responding on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-rest-not-spending |
| Fix HBase Master startup failures on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-start-fails |
| Resolve storage exceptions after connection reset | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-storage-exception-reset |
| Resolve timeouts with hbase hbck on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-timeouts-hbase-hbck |
| Troubleshoot HBase region server issues on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/hbase-troubleshoot-unassigned-regions |
| Fix HBase TTL data retention issues on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/troubleshoot-data-retention-issues-expired-data |
| Troubleshoot HBase REST API issues on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/troubleshoot-rest-api |
| Access and interpret YARN application logs on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-access-yarn-app-logs-linux |
| Enable and collect Hadoop heap dumps on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-collect-debug-heap-dump-linux |
| Resolve Hive out-of-memory errors on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-hive-out-of-memory-error-oom |
| Lookup and resolve Hadoop stack trace errors on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-stack-trace-error-messages |
| Understand and resolve WebHCat errors on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-templeton-webhcat-debug-errors |
| Known issues and troubleshooting for Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-known-issues |
| Fix Ambari access failures after certificate rotation | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-known-issues-ambari-access-certificate-issue |
| Resolve Ambari user switch issues on HDInsight 5.1 | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-known-issues-ambari-users-cache |
| Recover HDInsight headnodes from /tmp disk usage leak | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-known-issues-cluster-head-node-unresponsive |
| Mitigate conda version regression on HDInsight 5.1 | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-known-issues-conda-version-regression |
| Resolve Ranger startup failures on ESP HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-known-issues-ranger-cluster-create-failure |
| Diagnose slow or failing jobs on HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-troubleshoot-failed-cluster |
| HDInsight troubleshooting guide index | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-troubleshoot-guide |
| Troubleshoot HDFS issues in Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-troubleshoot-hdfs |
| Common Hive issues and fixes on Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-troubleshoot-hive |
| Troubleshoot YARN issues in Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-troubleshoot-yarn |
| Restore error messages in Ambari Hive View on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-error-message-hive-view |
| Resolve Hive log disk space issues on HDInsight head nodes | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-hive-logs-diskspace-full-headnodes |
| Fix Hive View inaccessibility due to Zookeeper issues | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-inaccessible-hive-view |
| Troubleshoot Hive join OutOfMemory GC overhead errors | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-outofmemory-overhead-exceeded |
| Resolve permission denied errors creating Hive tables | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-permission-error-create-table |
| Diagnose poor Hive LLAP query performance in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-query-performance |
| Fix slow reducers and data skew in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-slow-reducer |
| Troubleshoot Apache Tez application hangs in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-tez-hangs |
| Fix slow or failing Ambari Tez View in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-tez-view-slow |
| Fix Hive View query result timeout in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-view-time-out |
| Correct Hive JDBC URL in Zeppelin interpreter on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/interactive-query-troubleshoot-zookeeperhiveclientexception-hiveserver-configs |
| Resolve Ambari Hive View gateway timeout exceptions | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/troubleshoot-gateway-timeout |
| Troubleshoot Hive LLAP workload management issues | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/troubleshoot-workload-management-issues |
| Resolve Kafka broker startup failures from full disks | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/kafka-troubleshoot-full-disk |
| Fix HDInsight Kafka error: insufficient fault domains | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/kafka-troubleshoot-insufficient-domains |
| Debug Spark apps using HDInsight History Server extensions | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-azure-spark-history-server |
| Debug Spark job failures with IntelliJ Azure Toolkit | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-intellij-tool-failure-debug |
| Remotely debug Apache Spark apps on HDInsight via IntelliJ | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-intellij-tool-plugin-debug-jobs-remotely |
| Debug HDInsight Spark jobs with YARN and Spark UIs | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-job-debugging |
| Known issues and workarounds for HDInsight Spark clusters | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-known-issues |
| Troubleshoot Spark Streaming apps stopping after 24 days | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-application-stops |
| Fix Jupyter 404 'Blocking Cross Origin API' on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-blocking-cross-origin |
| Resolve RequestBodyTooLarge errors in HDInsight Spark streaming | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-event-log-requestbodytoolarge |
| Fix IllegalArgumentException in HDInsight Spark activities | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-illegalargumentexception |
| Resolve InvalidClassException version mismatch in HDInsight Spark | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-job-fails-invalidclassexception |
| Fix NoClassDefFoundError for Spark-Kafka on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-job-fails-noclassdeffounderror |
| Improve slow Spark jobs with many Azure Storage files | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-job-slowness-container |
| Resolve OutOfMemoryError in HDInsight Spark clusters | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-outofmemory |
| Resolve RpcTimeoutException and 502 errors in Spark Thrift on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-rpctimeoutexception |
| Troubleshoot large result downloads via JDBC/ODBC and Thrift on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-troubleshoot-sparkexception-kryo-serialization-failed |
| Common Spark issues and fixes on Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-troubleshoot-spark |
| Debug WASB file operations for HDInsight storage issues | https://learn.microsoft.com/en-us/azure/hdinsight/spark/troubleshoot-debug-wasb |
| Fix Jupyter Notebook creation issues on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/troubleshoot-jupyter-notebook-convert |
| Troubleshoot Apache Oozie workflows on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/troubleshoot-oozie |
| Resolve Azure HDInsight resource creation capacity errors | https://learn.microsoft.com/en-us/azure/hdinsight/troubleshoot-resource-creation-fails |
| Troubleshoot script action failures in Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/troubleshoot-script-action |
| Work around Sqoop import/export failures on ESP HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/troubleshoot-sqoop |

### Best Practices
| Topic | URL |
|-------|-----|
| Use Azure Monitor logs for HDInsight availability | https://learn.microsoft.com/en-us/azure/hdinsight/cluster-availability-monitor-logs |
| Apply cluster management best practices in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/cluster-management-best-practices |
| Apply general best practices for HDInsight Enterprise Security | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/general-guidelines |
| Plan and execute data migration to Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-on-premises-migration-best-practices-data-migration |
| Apply infrastructure best practices for Azure HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-on-premises-migration-best-practices-infrastructure |
| Implement storage best practices for HDInsight migrations | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-on-premises-migration-best-practices-storage |
| Optimize HDInsight HBase with Accelerated Writes | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-accelerated-writes |
| Apply HBase performance advisor recommendations on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-advisor |
| Tune Apache Phoenix performance on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-phoenix-performance |
| Tune Apache HBase performance on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/troubleshoot-hbase-performance-issues |
| Scale HiveServer2 on HDInsight using edge nodes | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-apps-install-hiveserver2 |
| Monitor HDInsight availability with Apache Ambari | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-cluster-availability |
| Create HDInsight clusters with secure transfer-enabled storage accounts | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-create-linux-clusters-with-secure-transfer-storage |
| Apply Linux-specific tips for Hadoop on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-linux-information |
| Optimize Apache Hive query performance on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-optimize-hive-query |
| Monitor and optimize HDInsight cluster performance | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-key-scenarios-to-monitor |
| Schedule and apply OS patches for HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-os-patching |
| Apply pre-creation best practices for HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-overview-before-you-start |
| Manually scale HDInsight clusters for workload patterns | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-scaling-best-practices |
| Apply gateway best practices for Hive on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/gateway-best-practices |
| Operate LLAP schedule-based autoscale on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/llap-schedule-based-autoscale-best-practices |
| Configure Kafka partition replicas for high availability | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-high-availability |
| Mirror Kafka topics between HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-mirroring |
| Tune Kafka on HDInsight for optimal performance | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-performance-tuning |
| Configure managed disks to scale Kafka on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-scalability |
| Migrate HDInsight Log Analytics data to new tables | https://learn.microsoft.com/en-us/azure/hdinsight/log-analytics-migration |
| Use Azure Storage effectively as HDInsight default filesystem | https://learn.microsoft.com/en-us/azure/hdinsight/overview-azure-storage |
| Leverage Data Lake Storage Gen2 with HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/overview-data-lake-storage-gen2 |
| Optimize Apache Spark job performance on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-perf |
| Manage Python packages for Jupyter on HDInsight Spark | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-python-package-installation |
| Configure Spark Streaming on HDInsight for exactly-once processing | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-streaming-exactly-once |
| Optimize Apache Spark cluster configuration on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/optimize-cluster-configuration |
| Optimize data processing operations for Spark on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/optimize-data-processing |
| Optimize data storage for Apache Spark on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/optimize-data-storage |
| Tune Apache Spark memory usage on HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/spark/optimize-memory-usage |
| Safely manage JAR dependencies on HDInsight Spark | https://learn.microsoft.com/en-us/azure/hdinsight/spark/safely-manage-jar-dependency |
| Apply Apache Spark performance guidelines on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/spark-best-practices |
| Use SparkCruise to optimize Spark queries on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/spark-cruise |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan ETL at scale with Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-etl-at-scale |
| Assess benefits of migrating on-premises Hadoop to Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-on-premises-migration-motivation |
| Choose HDInsight tools for custom MapReduce jobs | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-run-custom-programs |
| Choose backup and replication options for HBase | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-backup-replication |
| Migrate Apache HBase clusters to HDInsight 5.1 | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-migrate-hdinsight-5-1 |
| Migrate HBase to HDInsight 5.1 with a new storage account | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-migrate-hdinsight-5-1-new-storage-account |
| Migrate Apache HBase clusters to a newer HDInsight version | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-migrate-new-version |
| Migrate HBase to new HDInsight version and storage account | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-migrate-new-version-new-storage-account |
| Plan HDInsight cluster capacity and performance | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-capacity-planning |
| Plan migrations for retiring HDInsight components | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-component-retirements-and-action-required |
| Compare storage services for Azure HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-compare-storage-options |
| Plan Azure HDInsight virtual network deployment | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-plan-virtual-network-deployment |
| Upgrade Azure HDInsight to Apache Ranger 2.3.0 | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-ranger-5-1-migration |
| Assess and migrate from retired HDInsight versions | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-retired-versions |
| Select appropriate VM sizes for HDInsight nodes | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-selecting-vm-size |
| Plan migration to newer Azure HDInsight cluster versions | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-upgrade-cluster |
| Size HDInsight Interactive Query (LLAP) clusters | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/hive-llap-sizing-guide |
| Use Kafka MirrorMaker 2.0 for migration and replication | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/kafka-mirrormaker-2-0-guide |
| Migrate Apache Kafka workloads from HDInsight 4.0 to 5.1 | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/migrate-5-1-versions |
| Migrate Apache Kafka workloads from HDInsight 3.6 to 4.0 | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/migrate-versions |
| Migrate HDInsight clusters from Basic to Standard Load Balancer | https://learn.microsoft.com/en-us/azure/hdinsight/load-balancer-migration-guidelines |
| Migrate Ambari configurations from HDInsight 4.x to 5.x | https://learn.microsoft.com/en-us/azure/hdinsight/migrate-ambari-recent-version-hdinsight |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Use Apache Ambari for HDInsight cluster management | https://learn.microsoft.com/en-us/azure/hdinsight/apache-ambari-usage |
| Understand HDInsight architecture with Enterprise Security Package | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/apache-domain-joined-architecture |
| Design architecture for migrating on-premises Hadoop to HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-on-premises-migration-best-practices-architecture |
| Choose HDInsight business continuity architectures | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-business-continuity-architecture |
| Study HDInsight high availability and DR case design | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-high-availability-case-study |
| Understand HDInsight high availability architecture components | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-high-availability-components |
| Share one Data Lake Storage account across multiple HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-multiple-clusters-data-lake-store |
| Operationalize HDInsight data pipelines with Oozie | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-operationalize-data-pipeline |
| Design scalable streaming architectures with HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-streaming-at-scale-overview |
| Azure HDInsight virtual network architecture and resources | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-virtual-network-architecture |
| Design highly available Spark Streaming jobs on YARN in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-streaming-high-availability |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review Azure HDInsight service limits and behaviors | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-faq |
| Plan HDInsight log sizes and retention policies | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-log-management |
| Use supported node configurations for HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-supported-node-configuration |
| Use external metastores and understand HDInsight default metastore limits | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-use-external-metadata-stores |
| Kafka on HDInsight limits, configs, and behaviors | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/kafka-faq |
| Request and manage HDInsight CPU core quota increases | https://learn.microsoft.com/en-us/azure/hdinsight/quota-increase-request |

### Security
| Topic | URL |
|-------|-----|
| Configure managed identity access to Blob storage for HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/configure-azure-blob-storage |
| Configure double disk encryption for HDInsight data at rest | https://learn.microsoft.com/en-us/azure/hdinsight/disk-encryption |
| Configure HDInsight clusters with Entra Domain Services integration | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/apache-domain-joined-configure-using-azure-adds |
| Create and configure HDInsight Enterprise Security Package clusters | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/apache-domain-joined-create-configure-enterprise-security-cluster |
| Manage users, roles, and security for HDInsight ESP clusters | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/apache-domain-joined-manage |
| Configure Apache Ranger policies for HBase with ESP | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/apache-domain-joined-run-hbase |
| Configure Apache Ranger Hive policies in HDInsight ESP | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/apache-domain-joined-run-hive |
| Set Apache Ranger policies for Kafka with ESP | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/apache-domain-joined-run-kafka |
| Implement encryption in transit for Azure HDInsight nodes | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/encryption-in-transit |
| Plan enterprise security options for Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/hdinsight-security-overview |
| Secure Oozie workflows with HDInsight Enterprise Security | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/hdinsight-use-oozie-domain-joined-clusters |
| Set up Azure HDInsight ID Broker for OAuth and MFA | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/identity-broker |
| Configure LDAP sync for Ranger and Ambari in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/ldap-sync |
| Manage SSH access for Entra domain accounts on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/domain-joined/ssh-domain-accounts |
| Configure Private Link for HDInsight Kafka REST Proxy | https://learn.microsoft.com/en-us/azure/hdinsight/enable-private-link-on-kafka-rest-proxy-hdi-cluster |
| Implement Enterprise Security Package for HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/enterprise-security-package |
| Apply security and DevOps best practices for Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-on-premises-migration-best-practices-security-devops |
| Manage Ambari Views permissions on ESP-enabled HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-authorize-users-to-ambari |
| Implement non-interactive .NET auth for HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-create-non-interactive-authentication-dotnet-applications |
| Use managed identities with Azure HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-managed-identities |
| Allow HDInsight management IPs in NSGs and routes | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-management-ip-addresses |
| Migrate to granular role-based access for HDInsight cluster configurations | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-migrate-granular-access-cluster-configurations |
| Enable Azure Private Link for HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-private-link |
| Restrict public connectivity for Azure HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-restrict-public-connectivity |
| Safely rotate HDInsight storage account access keys | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-rotate-storage-keys |
| Use HDInsight NSG service tags for management traffic | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-service-tags |
| Restrict HDInsight Blob data access using SAS tokens | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-storage-sharedaccesssignature-permissions |
| Synchronize Microsoft Entra users to HDInsight ESP clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-sync-aad-users-to-cluster |
| Create and manage Entra ID-authenticated HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/create-clusters-with-entra |
| Configure ARM templates for Entra ID-enabled HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/manage-entra-id-enabled-azure-hdinsight-clusters-with-arm-templates |
| Manage Entra ID-enabled HDInsight clusters via REST API | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/manage-entra-id-enabled-cluster-with-rest-api |
| Configure security options for Hive in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/hdinsight-security-options-for-hive |
| Set up TLS and client auth for ESP Kafka clusters | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-esp-kafka-ssl-encryption-authentication |
| Configure TLS encryption and client auth for HDInsight Kafka | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-ssl-encryption-authentication |
| Secure Spark–Kafka streaming integration on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/secure-spark-kafka-streaming-integration-scenario |
| Fetch OAuth tokens from HDInsight to access Azure services | https://learn.microsoft.com/en-us/azure/hdinsight/msi-support-to-access-azure-services |
| Apply built-in Azure Policy definitions for HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/policy-reference |
| Configure Ranger policies for Spark SQL in HDInsight ESP | https://learn.microsoft.com/en-us/azure/hdinsight/spark/ranger-policies-for-spark |
| Configure TLS versions for Azure HDInsight gateways | https://learn.microsoft.com/en-us/azure/hdinsight/transport-layer-security |
| Configure HDInsight managed identity for SQL authentication | https://learn.microsoft.com/en-us/azure/hdinsight/use-managed-identity-for-sql-database-authentication-in-azure-hdinsight |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Ambari Web UI auto-logout timeout in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/ambari-web-ui-auto-logout |
| Connect HDInsight clusters to on-premises networks with VPN and DNS | https://learn.microsoft.com/en-us/azure/hdinsight/connect-on-premises-network |
| Configure HBase cluster replication in Azure VNets | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-replication |
| Use HBCK2 to repair HBase on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/how-to-use-hbck2-tool |
| Check HDInsight 4.0 open-source component versions | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-40-component-versioning |
| Check HDInsight 5.x open-source component versions | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-5x-component-versioning |
| Manage HDInsight clusters using Azure CLI commands | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-administer-use-command-line |
| Automate HDInsight cluster management with PowerShell | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-administer-use-powershell |
| Configure and use empty edge nodes in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-apps-use-edge-node |
| Configure HDInsight Autoscale policies and limits | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-autoscale-clusters |
| Tune HDInsight cluster settings using Ambari | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-changing-configs-via-ambari |
| Review bundled open-source components and versions in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-component-versioning |
| Configure Azure HDInsight VS Code extension settings | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-config-for-vscode |
| Create and configure VNets, NSGs, and DNS for HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-create-virtual-network |
| Configure custom Ambari database for HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-custom-ambari-db |
| Preload Apache Hive libraries during HDInsight cluster creation | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-add-hive-libraries |
| Add extra Azure Storage accounts to existing HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-add-storage |
| Programmatically customize HDInsight cluster configuration with bootstrap | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-customize-cluster-bootstrap |
| Customize HDInsight clusters using script actions | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-customize-cluster-linux |
| Connect to Azure HDInsight clusters using SSH | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-linux-use-ssh-unix |
| Enable Azure Monitor logs for HDInsight cluster operations | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-oms-log-analytics-tutorial |
| Reference ports for Hadoop services on HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-port-settings-for-services |
| Configure and customize HDInsight clusters across tools | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-provision-linux-clusters |
| Develop script actions to configure Azure HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-script-actions-linux |
| Configure SSH tunneling to access HDInsight web UIs | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-linux-ambari-ssh-tunnel |
| Secure HDInsight outbound traffic using Azure Firewall | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-restrict-outbound-traffic |
| Custom-tune HDInsight Autoscale advanced settings | https://learn.microsoft.com/en-us/azure/hdinsight/how-to-custom-configure-hdinsight-autoscale |
| Configure Apache Hive replication on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/apache-hive-replication |
| Migrate Hive default metastore to external SQL Database on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/hive-default-metastore-export-import |
| Configure Hive LLAP workload management pools in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/hive-workload-management |
| Use Hive LLAP workload management commands in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/workload-management-commands |
| Enable automatic topic creation in HDInsight Kafka | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-auto-create-topics |
| Configure VPN and VNet access to HDInsight Kafka | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-connect-vpn-gateway |
| Configure Azure Monitor logs for HDInsight Kafka | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-log-analytics-operations-management |
| Configure cross-VNet connectivity to HDInsight Kafka | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/connect-kafka-cluster-with-vm-in-different-vnet |
| Configure cross-VNet client connectivity to HDInsight Kafka | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/connect-kafka-with-vnet |
| Configure monitoring and alerts for Azure HDInsight with Azure Monitor | https://learn.microsoft.com/en-us/azure/hdinsight/monitor-hdinsight |
| Reference of monitoring data for Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/monitor-hdinsight-reference |
| Configure non-Azure Firewall network virtual appliances for HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/network-virtual-appliance |
| Optimize HBase performance with Ambari configuration | https://learn.microsoft.com/en-us/azure/hdinsight/optimize-hbase-ambari |
| Optimize Hive performance via Ambari settings in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/optimize-hive-ambari |
| Tune Pig properties with Ambari on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/optimize-pig-ambari |
| Configure selective logging for AMA on HDInsight via script actions | https://learn.microsoft.com/en-us/azure/hdinsight/selective-logging-analysis |
| Configure selective logging for HDInsight clusters with script actions | https://learn.microsoft.com/en-us/azure/hdinsight/selective-logging-analysis-azure-logs |
| Configure service endpoint policies for HDInsight virtual networks | https://learn.microsoft.com/en-us/azure/hdinsight/service-endpoint-policies |
| Set up PySpark interactive environment with VS Code HDInsight Tools | https://learn.microsoft.com/en-us/azure/hdinsight/set-up-pyspark-interactive-environment |
| Configure HDInsight IO Cache to speed up Spark | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-improve-performance-iocache |
| Use HDInsight Spark Jupyter kernels effectively | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-jupyter-notebook-kernels |
| Configure Jupyter on HDInsight to use Maven packages | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-jupyter-notebook-use-external-packages |
| Configure and scope Spark dependencies on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-manage-dependencies |
| Tune Spark resource configuration on HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-resource-manager |
| Configure Apache Spark settings on Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-settings |
| Transfer files to Azure HDInsight using SCP | https://learn.microsoft.com/en-us/azure/hdinsight/use-scp |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Configure Ambari email alerts with SendGrid in HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/apache-ambari-email |
| Stream from Kafka to Azure Cosmos DB with Spark | https://learn.microsoft.com/en-us/azure/hdinsight/apache-kafka-spark-structured-streaming-cosmosdb |
| Execute common HDInsight tasks with Azure CLI samples | https://learn.microsoft.com/en-us/azure/hdinsight/azure-cli-samples |
| Connect Excel to HDInsight Hadoop via Power Query | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-connect-excel-power-query |
| Query HDInsight Hive from Java using JDBC | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-connect-hive-jdbc-driver |
| Visualize HDInsight Hive data in Power BI via ODBC | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-connect-hive-power-bi |
| Integrate C# UDFs with Hive and Pig on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-hive-pig-udf-dotnet-csharp |
| Call WebHCat REST API for Hive with Curl | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-hive-curl |
| Submit Hive jobs using HDInsight .NET SDK | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-hive-dotnet-sdk |
| Run HDInsight Hive queries with Azure PowerShell | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-hive-powershell |
| Use Visual Studio Data Lake tools for Hive on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-hive-visual-studio |
| Submit MapReduce jobs to HDInsight using Curl and WebHCat | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-mapreduce-curl |
| Submit MapReduce jobs to HDInsight with .NET SDK | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-mapreduce-dotnet-sdk |
| Run HDInsight MapReduce jobs using Azure PowerShell | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-mapreduce-powershell |
| Run MapReduce jobs on HDInsight via SSH | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-mapreduce-ssh |
| Submit Sqoop jobs to HDInsight via Curl and WebHCat | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-sqoop-curl |
| Run Sqoop jobs on HDInsight using .NET SDK | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-sqoop-dotnet-sdk |
| Use Sqoop on HDInsight Linux headnodes for SQL integration | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-sqoop-mac-linux |
| Submit Sqoop jobs to HDInsight with PowerShell | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-use-sqoop-powershell |
| Use Visual Studio Data Lake Tools with HDInsight Hadoop | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/apache-hadoop-visual-studio-tools-get-started |
| Configure Beeline connections to HDInsight HiveServer2 | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/connect-install-beeline |
| Run Sqoop jobs between HDInsight and Azure SQL Database | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/hdinsight-use-sqoop |
| Use Python UDFs with Hive and Pig on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/python-udf-hdinsight |
| Submit Hadoop jobs to HDInsight via .NET, curl, and PowerShell | https://learn.microsoft.com/en-us/azure/hdinsight/hadoop/submit-apache-hadoop-jobs-programmatically |
| Build and deploy a Java HBase client with Maven | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-build-java-maven-linux |
| Run HBase SQL queries with Phoenix and Zeppelin | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-phoenix-zeppelin |
| Use the HBase .NET SDK with HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-rest-sdk |
| Use Phoenix Query Server REST SDK on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-using-phoenix-query-server-rest-sdk |
| Use HDInsight .NET SDK for cluster management tasks | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-administer-use-dotnet-sdk |
| Use Spark DStreams with Kafka on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-apache-spark-with-kafka |
| Install custom Hadoop applications on Azure HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-apps-install-custom-applications |
| Use Spark & Hive Tools for VS Code with HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-for-vscode |
| Use the Azure HDInsight SDK for Go with Hadoop clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-go-sdk-overview |
| Install and access Hue on Azure HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-hue-linux |
| Manage HDInsight Hadoop clusters using Ambari REST API | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-manage-ambari-rest-api |
| Run .NET MapReduce jobs on Linux-based HDInsight using Mono | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-migrate-dotnet-to-linux |
| Define and run Oozie workflows on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-use-oozie-linux-mac |
| Use Spark HBase Connector between HDInsight Spark and HBase | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-using-spark-query-hbase |
| Manage Entra-enabled HDInsight clusters using .NET SDK | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/manage-hadoop-cluster-dot-net-sdk |
| Run Hive queries on Entra-enabled HDInsight using PowerShell | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/run-apache-hive-queries-using-powershell-on-entra-enabled-hdinsight-cluster |
| Run Hive queries on HDInsight using the REST API | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/run-apache-hive-queries-using-rest-api |
| Run Hive queries on Entra-enabled HDInsight with .NET SDK | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/run-hive-queries-using-dot-net-sdk |
| Submit MapReduce jobs to Entra-enabled HDInsight using .NET SDK | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/run-map-reduce-jobs-dot-net-sdk |
| Run MapReduce jobs on Entra-enabled HDInsight with PowerShell | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/run-map-reduce-jobs-entra-id-enabled-using-powershell |
| Run MapReduce jobs on Entra-enabled HDInsight via REST API | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/run-map-reduce-rest-jobs |
| Submit Spark jobs to Entra-enabled HDInsight via Livy REST API | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-with-entra-authentication/run-spark-jobs-using-rest-api |
| Use Power BI DirectQuery with HDInsight Hive | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/apache-hadoop-connect-hive-power-bi-directquery |
| Integrate Spark and Hive using Hive Warehouse Connector | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/apache-hive-warehouse-connector |
| Run Spark operations via Hive Warehouse Connector | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/apache-hive-warehouse-connector-operations |
| Use Hive Warehouse Connector from Zeppelin via Livy | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/apache-hive-warehouse-connector-zeppelin |
| Use Hive Warehouse Connector APIs on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/hive-warehouse-connector-apis |
| Use Hive Warehouse Connector 2.x APIs on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/interactive-query/hive-warehouse-connector-v2-apis |
| Integrate HDInsight Kafka with Azure IoT Hub | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-connector-iot-hub |
| Use Kafka REST Proxy with HDInsight clusters | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/rest-proxy |
| Use Kafka REST Proxy on HDInsight via Azure CLI | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/tutorial-cli-rest-proxy |
| Connect Synapse Spark pools to HDInsight external Hive Metastore | https://learn.microsoft.com/en-us/azure/hdinsight/share-hive-metastore-with-synapse |
| Analyze Application Insights telemetry with Spark on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-analyze-application-insight-logs |
| Connect HDInsight Spark to Azure SQL Database | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-connect-to-sql-database |
| Create and submit Scala Spark apps from Eclipse to HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-eclipse-tool-plugin |
| Develop and submit Spark apps with IntelliJ Azure Toolkit | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-intellij-tool-plugin |
| Submit remote Spark jobs to HDInsight using Livy REST API | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-livy-rest-interface |
| Integrate Microsoft Cognitive Toolkit with Spark on HDInsight | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-microsoft-cognitive-toolkit |
| Run Azure Machine Learning AutoML on HDInsight Spark | https://learn.microsoft.com/en-us/azure/hdinsight/spark/apache-spark-run-machine-learning-automl |
| Run Apache Pig workloads on HDInsight Hadoop | https://learn.microsoft.com/en-us/azure/hdinsight/use-pig |

### Deployment
| Topic | URL |
|-------|-----|
| Migrate HDInsight monitoring to Azure Monitor Agent (AMA) | https://learn.microsoft.com/en-us/azure/hdinsight/azure-monitor-agent |
| Deploy HBase clusters in Azure Virtual Networks | https://learn.microsoft.com/en-us/azure/hdinsight/hbase/apache-hbase-provision-vnet |
| Publish Azure HDInsight applications to Azure Marketplace | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-apps-publish-applications |
| Operationalize on-demand HDInsight Hadoop clusters with Data Factory | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-create-linux-clusters-adf |
| Deploy HDInsight clusters using ARM templates | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-create-linux-clusters-arm-templates |
| Provision HDInsight 4.0 clusters using Azure CLI | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-create-linux-clusters-azure-cli |
| Create Linux HDInsight clusters using PowerShell scripts | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-create-linux-clusters-azure-powershell |
| Create HDInsight clusters via Azure REST and ARM templates | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-create-linux-clusters-curl-rest |
| Create Linux-based HDInsight clusters via Azure portal | https://learn.microsoft.com/en-us/azure/hdinsight/hdinsight-hadoop-create-linux-clusters-portal |
| Migrate HDInsight Kafka clusters using MirrorMaker 2 | https://learn.microsoft.com/en-us/azure/hdinsight/kafka/apache-kafka-mirror-maker-2 |
| Provision and delete HDInsight clusters via Automation runbooks | https://learn.microsoft.com/en-us/azure/hdinsight/manage-clusters-runbooks |