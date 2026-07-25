---
name: azure-databricks
description: Expert knowledge for Azure Databricks development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using Unity Catalog, Lakehouse/Lakeflow, Lakebase, SQL warehouses, or ML/GenAI model serving, and other Azure Databricks related development tasks. Not for Azure Synapse Analytics (use azure-synapse-analytics), Azure HDInsight (use azure-hdinsight), Azure Machine Learning (use azure-machine-learning), Azure Data Factory (use azure-data-factory).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Databricks Skill

This skill provides expert guidance for Azure Databricks. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Location | Description |
|----------|----------|-------------|
| Troubleshooting | L37-L155 | Diagnosing and fixing Databricks issues: cluster/compute startup, Spark and SQL errors, connectors/Lakeflow ingestion, Model Serving/AI agents, Feature Store, streaming, jobs, and performance debugging. |
| Best Practices | L156-L349 | Best practices for Databricks architecture, compute, governance, streaming, Delta, Lakeflow, AI/ML, RAG, AI Search, performance tuning, cost optimization, and production operations |
| Decision Making | L350-L457 | Guides for choosing Azure Databricks tiers, compute, SQL warehouses, connectors, ML/AI options, and detailed migration paths (Unity Catalog, runtimes, lakehouse, Lakeflow, MLflow, Feature Store). |
| Architecture & Design Patterns | [architecture-patterns.md](architecture-patterns.md) | Architecting Databricks/Lakehouse solutions: patterns for agents, pipelines, governance, networking, storage, HA/DR, performance, streaming, CDC, and model deployment. |
| Limits & Quotas | [limits-quotas.md](limits-quotas.md) | Limits, quotas, and constraints for Databricks compute, AI/ML, Lakeflow pipelines/connectors, Lakebase, dashboards/notebooks, SQL features, and Unity Catalog resources and naming. |
| Security | [security.md](security.md) | Identity, access control, encryption, networking, compliance, and governance for Azure Databricks, Unity Catalog, Lakeflow, Lakebase, Apps, OpenSharing, and partner integrations. |
| Configuration | [configuration.md](configuration.md) | Configuring and managing Azure Databricks: account/workspace settings, networking, security/Unity Catalog, compute/jobs/pipelines, AI/ML/GenAI features, connectors, SQL/runtime options, and cost/usage monitoring. |
| Integrations & Coding Patterns | [integrations.md](integrations.md) | Patterns and APIs for integrating Databricks with agents, AI/ML tooling, external data systems, BI apps, SDKs/CLIs, Lakehouse Federation, and Spark/SQL/PySpark code for reading, writing, and streaming data. |
| Deployment | [deployment.md](deployment.md) | Deploying and productionizing Databricks workspaces, apps, agents, dashboards, Lakeflow pipelines, and ML/GenAI models using CI/CD, IaC, CLIs, and various deployment engines. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Databricks Agent Evaluation issues | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-evaluation/troubleshooting |
| Debug custom AI agents on Databricks Apps and Model Serving | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/debug-agent |
| Monitor Genie Agent activity using audit logs and alerts | https://learn.microsoft.com/en-us/azure/databricks/ai-bi/admin/audit |
| Troubleshoot Azure Databricks compute startup issues | https://learn.microsoft.com/en-us/azure/databricks/compute/troubleshooting/ |
| Diagnose and fix Azure Databricks classic cluster termination errors | https://learn.microsoft.com/en-us/azure/databricks/compute/troubleshooting/cluster-error-codes |
| Debug Spark applications using Databricks Spark UI | https://learn.microsoft.com/en-us/azure/databricks/compute/troubleshooting/debugging-spark-ui |
| Troubleshoot Unity Catalog file events for external locations | https://learn.microsoft.com/en-us/azure/databricks/connect/unity-catalog/cloud-storage/file-events-faq |
| Troubleshoot common Databricks CLI issues | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/troubleshooting |
| Diagnose and fix Databricks Connect Python issues | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/python/troubleshooting |
| Diagnose and fix Databricks Connect Scala issues | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/scala/troubleshooting |
| Troubleshoot common Databricks Terraform provider errors | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/terraform/troubleshoot |
| Resolve common issues with Databricks VS Code extension | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/vscode-ext/faqs |
| Troubleshoot Databricks VS Code extension errors | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/vscode-ext/troubleshooting |
| Resolve ARITHMETIC_OVERFLOW errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/arithmetic-overflow-error-class |
| Handle CAST_INVALID_INPUT errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/cast-invalid-input-error-class |
| Diagnose DC_GA4_RAW_DATA_ERROR in GA4 connector | https://learn.microsoft.com/en-us/azure/databricks/error-messages/dc-ga4-raw-data-error-error-class |
| Understand DC_SFDC_API_ERROR in Databricks connectors | https://learn.microsoft.com/en-us/azure/databricks/error-messages/dc-sfdc-api-error-error-class |
| Diagnose DC_SQLSERVER_ERROR in SQL Server connector | https://learn.microsoft.com/en-us/azure/databricks/error-messages/dc-sqlserver-error-error-class |
| Understand DELTA_ICEBERG_COMPAT_V1_VIOLATION errors | https://learn.microsoft.com/en-us/azure/databricks/error-messages/delta-iceberg-compat-v1-violation-error-class |
| Resolve DIVIDE_BY_ZERO error in Azure Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/error-messages/divide-by-zero-error-class |
| Handle Azure Databricks error conditions programmatically | https://learn.microsoft.com/en-us/azure/databricks/error-messages/error-classes |
| Fix EWKB_PARSE_ERROR geometry parsing issues | https://learn.microsoft.com/en-us/azure/databricks/error-messages/ewkb-parse-error-error-class |
| Fix EWKT_PARSE_ERROR geometry parsing issues | https://learn.microsoft.com/en-us/azure/databricks/error-messages/ewkt-parse-error-error-class |
| Resolve GEOJSON_PARSE_ERROR in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/geojson-parse-error-error-class |
| Address GROUP_BY_AGGREGATE errors in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/error-messages/group-by-aggregate-error-class |
| Handle H3_INVALID_CELL_ID errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/h3-invalid-cell-id-error-class |
| Interpret and resolve H3_INVALID_GRID_DISTANCE_VALUE in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/h3-invalid-grid-distance-value-error-class |
| Handle H3_INVALID_RESOLUTION_VALUE errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/h3-invalid-resolution-value-error-class |
| Resolve H3_NOT_ENABLED errors and tier requirements | https://learn.microsoft.com/en-us/azure/databricks/error-messages/h3-not-enabled-error-class |
| Fix INSUFFICIENT_TABLE_PROPERTY errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/insufficient-table-property-error-class |
| Troubleshoot INVALID_ARRAY_INDEX errors in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/error-messages/invalid-array-index-error-class |
| Troubleshoot INVALID_ARRAY_INDEX_IN_ELEMENT_AT in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/invalid-array-index-in-element-at-error-class |
| Resolve MISSING_AGGREGATION errors in Databricks queries | https://learn.microsoft.com/en-us/azure/databricks/error-messages/missing-aggregation-error-class |
| Diagnose ROW_COLUMN_ACCESS errors for filters and masks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/row-column-access-error-class |
| Interpret Azure Databricks SQLSTATE error codes | https://learn.microsoft.com/en-us/azure/databricks/error-messages/sqlstates |
| Fix TABLE_OR_VIEW_NOT_FOUND errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/table-or-view-not-found-error-class |
| Resolve UNRESOLVED_ROUTINE function resolution errors | https://learn.microsoft.com/en-us/azure/databricks/error-messages/unresolved-routine-error-class |
| Understand UNSUPPORTED_TABLE_OPERATION errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/unsupported-table-operation-error-class |
| Understand UNSUPPORTED_VIEW_OPERATION errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/error-messages/unsupported-view-operation-error-class |
| Troubleshoot WKB_PARSE_ERROR for geometry parsing | https://learn.microsoft.com/en-us/azure/databricks/error-messages/wkb-parse-error-error-class |
| Troubleshoot WKT_PARSE_ERROR for geometry parsing | https://learn.microsoft.com/en-us/azure/databricks/error-messages/wkt-parse-error-error-class |
| Troubleshoot common Genie Agent data and token issues | https://learn.microsoft.com/en-us/azure/databricks/genie/troubleshooting |
| Monitor and troubleshoot Auto Loader ingestion pipelines | https://learn.microsoft.com/en-us/azure/databricks/ingestion/cloud-object-storage/auto-loader/observability |
| Troubleshoot common Aha! connector errors in Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/aha-troubleshoot |
| Resolve common Confluence connector ingestion issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/confluence-faq |
| Troubleshoot authentication and rate limit errors for Confluence | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/confluence-troubleshoot |
| Troubleshoot Dynamics 365 ingestion with Lakeflow Connect | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/d365-troubleshoot |
| Troubleshoot Google Ads connector ingestion issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/google-ads-troubleshoot |
| Troubleshoot Google Analytics raw data ingestion issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/google-analytics-troubleshoot |
| Resolve common Databricks Google Drive connector issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/google-drive-faq |
| Troubleshoot Databricks Google Drive ingestion failures | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/google-drive-troubleshoot |
| Troubleshoot Databricks HubSpot connector issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/hubspot-troubleshoot |
| Resolve common Azure Databricks Jira connector issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/jira-faq |
| Troubleshoot Jira Lakeflow ingestion errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/jira-troubleshoot |
| Troubleshoot Databricks managed Kafka ingestion | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/kafka-troubleshoot |
| Diagnose and fix Databricks Meta Ads ingestion issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/meta-ads-troubleshoot |
| Troubleshoot Databricks Monday.com connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/monday-com-troubleshoot |
| Diagnose and fix MySQL Lakeflow Connect ingestion | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/mysql-troubleshoot |
| Troubleshoot Netskope Logs connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/netskope-logs-troubleshoot |
| Troubleshoot common Outlook connector ingestion errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/outlook-troubleshoot |
| Pendo connector FAQs for Databricks ingestion | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/pendo-faq |
| Troubleshoot Databricks Pendo connector errors and failures | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/pendo-troubleshoot |
| Troubleshoot PostgreSQL Lakeflow Connect ingestion issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/postgresql-troubleshoot |
| Troubleshoot query-based connector cursor and errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/query-based-troubleshoot |
| Troubleshoot Databricks RabbitMQ ingestion errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/rabbitmq-troubleshoot |
| Troubleshoot Databricks Salesforce ingestion issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/salesforce-troubleshoot |
| Diagnose and fix Databricks ServiceNow connector issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/servicenow-troubleshoot |
| Troubleshoot Salesforce Marketing Cloud connector issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/sfmc-troubleshoot |
| Troubleshoot Microsoft SharePoint connector issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/sharepoint-troubleshoot |
| Troubleshoot Databricks Slack logs connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/slack-access-integration-logs-troubleshoot |
| Troubleshoot Databricks Smartsheet connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/smartsheet-troubleshoot |
| Answer common SQL Server Lakeflow Connect connector questions | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/sql-server-faq |
| Resolve SQL Server Lakeflow Connect ingestion problems | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/sql-server-troubleshoot |
| Resolve common Square connector errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/square-troubleshoot |
| Troubleshoot TikTok Ads connector in Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/tiktok-ads-troubleshoot |
| Diagnose and fix UNITY_CATALOG_INITIALIZATION_FAILED in Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/uc-initialization-troubleshoot |
| Diagnose and fix common Veeva Vault connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/veeva-vault-troubleshoot |
| Diagnose and fix Wiz Audit Logs connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/wiz-audit-logs-troubleshoot |
| Troubleshoot Workday HCM connector in Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/workday-hcm-troubleshoot |
| Diagnose and fix Databricks Workday connector issues | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/workday-reports-troubleshoot |
| Diagnose and fix Zendesk Support connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/zendesk-support-troubleshoot |
| Troubleshoot Databricks Zip connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/zip-troubleshoot |
| Troubleshoot Zoho Books connector errors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/zoho-books-troubleshoot |
| Troubleshoot common Zoom Logs connector errors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/zoom-logs-troubleshoot |
| Diagnose Zerobus Ingest API errors and handling | https://learn.microsoft.com/en-us/azure/databricks/ingestion/zerobus-errors |
| Inspect logs for Databricks init script execution | https://learn.microsoft.com/en-us/azure/databricks/init-scripts/logs |
| Test and validate Databricks ODBC driver connections | https://learn.microsoft.com/en-us/azure/databricks/integrations/odbc/testing |
| Diagnose and improve Lakeflow Jobs performance | https://learn.microsoft.com/en-us/azure/databricks/jobs/diagnose-job-performance |
| Troubleshoot and repair Azure Databricks job failures | https://learn.microsoft.com/en-us/azure/databricks/jobs/repair-job-failures |
| Manage and debug Foundation Model Fine-tuning runs | https://learn.microsoft.com/en-us/azure/databricks/large-language-models/foundation-model-training/view-manage-runs |
| Monitor and troubleshoot materialized view refreshes | https://learn.microsoft.com/en-us/azure/databricks/ldp/dbsql/materialized-monitor |
| Monitor and troubleshoot Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/observability |
| Recover Lakeflow pipelines from checkpoint failures | https://learn.microsoft.com/en-us/azure/databricks/ldp/recover-streaming |
| Migrate to AI Runtime and troubleshoot common GPU issues | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/guides |
| Troubleshoot Databricks Feature Store errors and limits | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/troubleshooting-and-limitations |
| Debug common Databricks Model Serving endpoint issues | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/model-serving-debug |
| Diagnose Databricks model serving with Genie Code | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/model-serving-genie-code |
| Debug Databricks Model Serving timeout issues | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/model-serving-timeouts |
| Resolve common OpenSharing data access errors | https://learn.microsoft.com/en-us/azure/databricks/opensharing/troubleshooting |
| Troubleshoot failing Spark jobs and executors in Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/failing-spark-jobs |
| Use Databricks Spark jobs timeline for debugging | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/jobs-timeline |
| Diagnose long-running Spark stages in Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/long-spark-stage |
| Debug slow low-I/O Spark stages in Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/slow-spark-stage-low-io |
| Identify expensive reads in Spark DAG on Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/spark-dag-expensive-read |
| Diagnose gaps between Spark jobs in Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/spark-job-gaps |
| Diagnose and fix Spark memory issues on Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/spark-memory-issues |
| Troubleshoot Azure Databricks Partner Connect issues | https://learn.microsoft.com/en-us/azure/databricks/partner-connect/troubleshoot |
| Retrieve exceptions from terminated StreamingQuery | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/streamingquery/exception |
| Debug streaming queries with explain plans | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/streamingquery/explain |
| Troubleshoot Databricks Git folder sync errors | https://learn.microsoft.com/en-us/azure/databricks/repos/errors-troubleshooting |
| Detect and repair Delta table metadata and file issues | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/delta-fsck |
| Act on Databricks SQL query performance insights | https://learn.microsoft.com/en-us/azure/databricks/sql/user/queries/performance-insights |
| Use Databricks SQL query history for troubleshooting | https://learn.microsoft.com/en-us/azure/databricks/sql/user/queries/query-history |
| Troubleshoot Databricks SQL queries with profiles | https://learn.microsoft.com/en-us/azure/databricks/sql/user/queries/query-profile |
| Inspect and debug Structured Streaming state on Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/read-state |

### Best Practices
| Topic | URL |
|-------|-----|
| Use default Databricks policy families to enforce compute best practices | https://learn.microsoft.com/en-us/azure/databricks/admin/clusters/policy-families |
| Apply identity best practices and federation in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/admin/users-groups/best-practices |
| Apply best practices to Azure Databricks serverless workspaces | https://learn.microsoft.com/en-us/azure/databricks/admin/workspace/serverless-workspaces-best-practices |
| Apply Databricks best practices for MLflow 2 evaluation sets | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-evaluation/evaluation-set |
| Load test Databricks Apps agents for QPS limits | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/load-test-agent-app |
| Measure RAG performance with retrieval and response metrics | https://learn.microsoft.com/en-us/azure/databricks/agents/tutorials/ai-cookbook/evaluate-assess-performance |
| Define RAG application quality with evaluation sets | https://learn.microsoft.com/en-us/azure/databricks/agents/tutorials/ai-cookbook/evaluate-define-quality |
| Evaluate and monitor RAG applications for quality, cost, latency | https://learn.microsoft.com/en-us/azure/databricks/agents/tutorials/ai-cookbook/fundamentals-evaluation-monitoring-rag |
| Design and optimize RAG inference chains on Databricks | https://learn.microsoft.com/en-us/azure/databricks/agents/tutorials/ai-cookbook/fundamentals-inference-chain-rag |
| Build and tune unstructured data pipelines for RAG | https://learn.microsoft.com/en-us/azure/databricks/agents/tutorials/ai-cookbook/quality-data-pipeline-rag |
| Improve RAG application quality via key tuning knobs | https://learn.microsoft.com/en-us/azure/databricks/agents/tutorials/ai-cookbook/quality-overview |
| Optimize RAG chain components for better responses | https://learn.microsoft.com/en-us/azure/databricks/agents/tutorials/ai-cookbook/quality-rag-chain |
| Optimize Databricks AI Search performance and scale | https://learn.microsoft.com/en-us/azure/databricks/ai-search/best-practices |
| Load test Databricks AI Search endpoints for sizing | https://learn.microsoft.com/en-us/azure/databricks/ai-search/endpoint-load-test |
| Apply Databricks AI Search filter expressions effectively | https://learn.microsoft.com/en-us/azure/databricks/ai-search/filtering-guide |
| Apply Databricks AI Search retrieval best practices | https://learn.microsoft.com/en-us/azure/databricks/ai-search/retrieval-quality |
| Evaluate Databricks AI Search retrieval strategies | https://learn.microsoft.com/en-us/azure/databricks/ai-search/retrieval-quality-eval |
| Detect and clean up unused Databricks AI Search endpoints | https://learn.microsoft.com/en-us/azure/databricks/ai-search/unused-endpoints |
| Migrate Databricks library installs from init scripts | https://learn.microsoft.com/en-us/azure/databricks/archive/compute/libraries-init-scripts |
| Apply compute policy best practices in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/compute/policies-best-practices |
| Use DBIO for transactional writes to cloud storage in Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/legacy/dbio-commit |
| Optimize skewed joins in Databricks using skew hints | https://learn.microsoft.com/en-us/azure/databricks/archive/legacy/skew-join |
| Migrate from Databricks Deep Learning Pipelines | https://learn.microsoft.com/en-us/azure/databricks/archive/spark-3.x-migration/deep-learning-pipelines |
| Apply advanced techniques in Databricks metric views | https://learn.microsoft.com/en-us/azure/databricks/business-semantics/metric-views/advanced-techniques |
| Use level-of-detail expressions in metric views | https://learn.microsoft.com/en-us/azure/databricks/business-semantics/metric-views/level-of-detail |
| Apply Azure Databricks administration best practices | https://learn.microsoft.com/en-us/azure/databricks/cheat-sheet/administration |
| Optimize BI performance with Databricks SQL warehouses | https://learn.microsoft.com/en-us/azure/databricks/cheat-sheet/bi-serving |
| Optimize BI performance with Databricks data preparation | https://learn.microsoft.com/en-us/azure/databricks/cheat-sheet/bi-serving-data-prep |
| Configure Databricks SQL warehouses for optimal BI serving | https://learn.microsoft.com/en-us/azure/databricks/cheat-sheet/bi-serving-sql-serving |
| Apply Azure Databricks compute creation best practices | https://learn.microsoft.com/en-us/azure/databricks/cheat-sheet/compute |
| Implement Azure Databricks production job scheduling best practices | https://learn.microsoft.com/en-us/azure/databricks/cheat-sheet/jobs |
| Apply Power BI performance best practices with Databricks | https://learn.microsoft.com/en-us/azure/databricks/cheat-sheet/power-bi |
| Apply classic compute configuration best practices in Databricks | https://learn.microsoft.com/en-us/azure/databricks/compute/cluster-config-best-practices |
| Use flexible node types for reliable Databricks compute | https://learn.microsoft.com/en-us/azure/databricks/compute/flexible-node-types |
| Apply best practices for Databricks pools | https://learn.microsoft.com/en-us/azure/databricks/compute/pool-best-practices |
| Use serverless compute effectively on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/compute/serverless/best-practices |
| Tune Databricks SQL warehouses for BI workloads | https://learn.microsoft.com/en-us/azure/databricks/compute/sql-warehouse/bi-workload-settings |
| Control large interactive queries with Query Watchdog | https://learn.microsoft.com/en-us/azure/databricks/compute/troubleshooting/query-watchdog |
| Apply Azure Databricks data engineering best practices | https://learn.microsoft.com/en-us/azure/databricks/data-engineering/best-practices |
| Implement observability for Databricks jobs and pipelines | https://learn.microsoft.com/en-us/azure/databricks/data-engineering/observability-best-practices |
| Handle schema evolution in Azure Databricks pipelines | https://learn.microsoft.com/en-us/azure/databricks/data-engineering/schema-evolution |
| Best practices for Unity Catalog ABAC policies | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/abac/best-practices |
| Implement common ABAC row filtering and masking patterns | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/abac/common-patterns |
| Optimize performance of ABAC row and column policies | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/abac/performance |
| Understand ABAC policy evaluation behavior | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/abac/policy-evaluation |
| Apply Unity Catalog data governance best practices | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/best-practices |
| Update Databricks jobs after Unity Catalog upgrade | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/jobs-update |
| Manage Unity Catalog object storage lifecycle and recovery | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/object-storage-lifecycle |
| Work with legacy Hive metastore objects in Databricks | https://learn.microsoft.com/en-us/azure/databricks/database-objects/hive-metastore |
| Follow DBFS root storage recommendations in Databricks | https://learn.microsoft.com/en-us/azure/databricks/dbfs/dbfs-root |
| Apply DBFS and Unity Catalog usage best practices | https://learn.microsoft.com/en-us/azure/databricks/dbfs/unity-catalog |
| Apply Delta Lake best practices on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/delta/best-practices |
| Handle Delta Lake limitations and risks on Amazon S3 | https://learn.microsoft.com/en-us/azure/databricks/delta/s3-limitations |
| Use selective overwrite options in Delta Lake | https://learn.microsoft.com/en-us/azure/databricks/delta/selective-overwrite |
| Apply MLOps Stack best practices with bundles | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/bundles/mlops-stacks |
| Apply CI/CD workflow best practices on Databricks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/ci-cd/flows |
| Apply security and performance best practices for Databricks apps | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-apps/best-practices |
| Test Databricks Connect for Python code with pytest | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/python/testing |
| Handle async queries and interruptions in Databricks Connect | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/queries |
| Apply Databricks developer and CI/CD best practices | https://learn.microsoft.com/en-us/azure/databricks/developers/best-practices |
| Explore Unity Catalog volumes and storage files in Databricks | https://learn.microsoft.com/en-us/azure/databricks/discover/files |
| Choose between Databricks volumes and workspace files | https://learn.microsoft.com/en-us/azure/databricks/files/files-recommendations |
| Apply prompt and context best practices in Genie Code | https://learn.microsoft.com/en-us/azure/databricks/genie-code/tips |
| Curate effective Genie Agents with domain-specific guidance | https://learn.microsoft.com/en-us/azure/databricks/genie/best-practices |
| Apply Auto Loader best practices for reliable ingestion | https://learn.microsoft.com/en-us/azure/databricks/ingestion/cloud-object-storage/auto-loader/best-practices |
| Configure Auto Loader automatic type widening | https://learn.microsoft.com/en-us/azure/databricks/ingestion/cloud-object-storage/auto-loader/type-widening |
| Apply common COPY INTO data loading patterns | https://learn.microsoft.com/en-us/azure/databricks/ingestion/cloud-object-storage/copy-into/examples |
| Incrementally clone Parquet and Iceberg tables to Delta | https://learn.microsoft.com/en-us/azure/databricks/ingestion/data-migration/clone-parquet |
| Apply Lakeflow Connect patterns for managed ingestion | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/common-patterns |
| Query system.billing.usage to monitor Lakeflow costs | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/monitor-costs |
| Apply Netskope Logs connector usage recommendations | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/netskope-logs-faq |
| Maintain Databricks Lakeflow managed ingestion pipelines | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/pipeline-maintenance |
| Maintain and operate PostgreSQL ingestion pipelines | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/postgresql-maintenance |
| RabbitMQ connector behavioral FAQs and guidance | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/rabbitmq-faq |
| Filter rows during Lakeflow Connect ingestion | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/row-filtering |
| Optimize incremental ingestion of Salesforce formula fields | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/salesforce-formula-fields |
| SharePoint connector FAQs and behavioral guidance | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/sharepoint-faq |
| Optimize Databricks smart closure for CDC pipelines | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/smart-closure |
| Use Wiz Audit Logs connector effectively and safely | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/wiz-audit-logs-faq |
| Apply Workday Reports connector FAQs and guidance | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/workday-reports-faq |
| Query OpenTelemetry data ingested into Databricks Delta | https://learn.microsoft.com/en-us/azure/databricks/ingestion/opentelemetry/queries |
| Use and configure init scripts on Azure Databricks clusters | https://learn.microsoft.com/en-us/azure/databricks/init-scripts/ |
| Reference external files safely in Databricks init scripts | https://learn.microsoft.com/en-us/azure/databricks/init-scripts/referencing-files |
| Implement recurring and backfill SQL jobs in Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/jobs/how-to/create-recurring-job |
| Drive Databricks For each jobs with control tables | https://learn.microsoft.com/en-us/azure/databricks/jobs/how-to/foreach-sql-lookup-tutorial |
| Apply classic compute best practices for Databricks jobs | https://learn.microsoft.com/en-us/azure/databricks/jobs/run-classic-jobs |
| Reduce Databricks costs with optimization practices | https://learn.microsoft.com/en-us/azure/databricks/lakehouse-architecture/cost-optimization/best-practices |
| Apply data and AI governance best practices on Databricks | https://learn.microsoft.com/en-us/azure/databricks/lakehouse-architecture/data-governance/best-practices |
| Design compute and workspace configuration for Databricks | https://learn.microsoft.com/en-us/azure/databricks/lakehouse-architecture/deployment-guide/compute |
| Design observability and monitoring for Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/lakehouse-architecture/deployment-guide/observability |
| Implement interoperability and usability best practices on Databricks | https://learn.microsoft.com/en-us/azure/databricks/lakehouse-architecture/interoperability-and-usability/best-practices |
| Apply operational excellence practices in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/lakehouse-architecture/operational-excellence/best-practices |
| Optimize performance efficiency on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/lakehouse-architecture/performance-efficiency/best-practices |
| Implement reliability best practices on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/lakehouse-architecture/reliability/best-practices |
| Scale ai_classify for 500+ label taxonomies | https://learn.microsoft.com/en-us/azure/databricks/large-language-models/classify-documents-labels-tutorial |
| Optimize Lakeflow clusters with enhanced and vertical autoscaling | https://learn.microsoft.com/en-us/azure/databricks/ldp/auto-scaling |
| Best practices for designing Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/best-practices |
| Advanced AUTO CDC usage and monitoring in pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/cdc-advanced |
| Use REPLACE WHERE flows for targeted recomputes | https://learn.microsoft.com/en-us/azure/databricks/ldp/dbsql/flows-replace-where |
| Handle compatibility issues with pipeline environment versions | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/environment-version-compatibility |
| Apply data quality expectations in pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/ldp-python-ref-expectations |
| Advanced expectation patterns for Lakeflow data quality | https://learn.microsoft.com/en-us/azure/databricks/ldp/expectation-patterns |
| Apply expectations for data quality in Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/expectations |
| Reduce high initialization times in Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/fix-high-init |
| Infer and evolve JSON schemas with from_json in pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/from-json-schema-evolution |
| Run full refreshes on Lakeflow streaming tables safely | https://learn.microsoft.com/en-us/azure/databricks/ldp/full-refresh-st |
| Optimize stateful streaming with watermarks in pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/stateful-processing |
| Implement CDC ETL pipelines with Lakeflow and Auto Loader | https://learn.microsoft.com/en-us/azure/databricks/ldp/tutorial-pipelines |
| Build geospatial Lakeflow pipelines with native spatial types | https://learn.microsoft.com/en-us/azure/databricks/ldp/tutorial-spatial-pipelines |
| Restart the Python process to refresh Databricks libraries | https://learn.microsoft.com/en-us/azure/databricks/libraries/restart-python-process |
| Apply Hyperopt best practices on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl-hyperparam-tuning/hyperopt-best-practices |
| Implement point-in-time correct feature joins | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/time-series |
| Benchmark Databricks LLM endpoints for performance | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/foundation-model-apis/prov-throughput-run-benchmark |
| Apply Databricks batch model inference patterns | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-inference/ |
| Validate models before Databricks serving deployment | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/model-serving-pre-deployment-validation |
| Monitor Databricks model quality and endpoint health | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/monitor-diagnose-endpoints |
| Optimize Databricks Model Serving endpoints for production | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/production-optimization |
| Plan and execute load testing for Databricks serving endpoints | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/what-is-load-test |
| Tune and autoscale Ray clusters on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ray/scale-ray |
| Apply deep learning best practices on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/dl-best-practices |
| Adapt Apache Spark workloads for Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/migration/spark |
| Apply MLflow 3 best practices for GenAI observability | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/ |
| Align MLflow judges with human feedback | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/align-judges |
| Evaluate and compare MLflow prompt versions for GenAI | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/prompt-version-mgmt/prompt-registry/evaluate-prompts |
| Use manual MLflow tracing for production GenAI apps | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/app-instrumentation/manual-tracing/ |
| Collect and log user feedback on GenAI traces with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/collect-user-feedback/ |
| Analyze GenAI trace data using MLflow Trace SDK | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/observe-with-traces/analyze-traces |
| Implement PII redaction for OTel traces in Databricks | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/redact-pii-otel-traces |
| Apply software engineering practices to Databricks notebooks | https://learn.microsoft.com/en-us/azure/databricks/notebooks/best-practices |
| Run Databricks notebooks safely and efficiently | https://learn.microsoft.com/en-us/azure/databricks/notebooks/run-notebook |
| Apply unit testing patterns in Databricks notebooks | https://learn.microsoft.com/en-us/azure/databricks/notebooks/test-notebooks |
| Optimize OpenSharing egress costs for data providers | https://learn.microsoft.com/en-us/azure/databricks/opensharing/manage-egress |
| Apply performance optimization recommendations on Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/ |
| Use adaptive query execution on Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/aqe |
| Migrate away from deprecated Bloom filter indexes | https://learn.microsoft.com/en-us/azure/databricks/optimizations/bloom-filters |
| Optimize Spark SQL queries with Databricks CBO | https://learn.microsoft.com/en-us/azure/databricks/optimizations/cbo |
| Improve read performance with Databricks disk cache | https://learn.microsoft.com/en-us/azure/databricks/optimizations/disk-cache |
| Improve Delta query performance with dynamic file pruning | https://learn.microsoft.com/en-us/azure/databricks/optimizations/dynamic-file-pruning |
| Choose and configure Databricks Delta isolation levels | https://learn.microsoft.com/en-us/azure/databricks/optimizations/isolation/isolation-levels |
| Use row-level concurrency for Delta tables on Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/isolation/row-level-concurrency |
| Optimize Delta MERGE performance with low shuffle merge | https://learn.microsoft.com/en-us/azure/databricks/optimizations/low-shuffle-merge |
| Use predictive I/O optimizations on Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/predictive-io |
| Optimize Azure Databricks range join performance | https://learn.microsoft.com/en-us/azure/databricks/optimizations/range-join |
| Diagnose Databricks Spark cost and performance in UI | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/ |
| Diagnose high I/O Spark stages using Databricks UI | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/long-spark-stage-io |
| Debug skew and spill in Databricks Spark stages | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/long-spark-stage-page |
| Handle Databricks spot instance losses effectively | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/losing-spot-instances |
| Resolve long Spark stages with a single task | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/one-spark-task |
| Optimize many small Spark jobs on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/small-spark-jobs |
| Mitigate overloaded Spark driver on Databricks | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/spark-driver-overloaded |
| Detect unnecessary data rewriting in Databricks Spark writes | https://learn.microsoft.com/en-us/azure/databricks/optimizations/spark-ui-guide/spark-rewriting-data |
| Best practices for setting up Databricks Partner Connect | https://learn.microsoft.com/en-us/azure/databricks/partner-connect/best-practice |
| Handle to_utc_timestamp semantics in Spark Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/to_utc_timestamp |
| Apply networking recommendations for Lakehouse Federation | https://learn.microsoft.com/en-us/azure/databricks/query-federation/networking |
| Optimize performance of Lakehouse Federation queries | https://learn.microsoft.com/en-us/azure/databricks/query-federation/performance-recommendations |
| Transform complex and nested data types in Databricks | https://learn.microsoft.com/en-us/azure/databricks/semi-structured/complex-types |
| Use higher-order functions on arrays in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/semi-structured/higher-order-functions |
| Compare VARIANT and JSON string storage semantics | https://learn.microsoft.com/en-us/azure/databricks/semi-structured/variant-json-diff |
| Convert Parquet tables to Delta Lake in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/delta-convert-to-delta |
| Optimize Delta Lake table layout with Databricks OPTIMIZE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/delta-optimize |
| Vacuum unused files from Delta and Spark tables | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/delta-vacuum |
| Apply partitioning and liquid clustering best practices in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-partition |
| Use ANALYZE TABLE statistics for Databricks optimization | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-aux-analyze-compute-statistics |
| Use Databricks SQL query hints for performance | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-qry-select-hints |
| Use OFFSET and LIMIT safely for pagination in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-qry-select-offset |
| Benchmark Databricks SQL warehouses with the TPC-DS dataset | https://learn.microsoft.com/en-us/azure/databricks/sql/tpcds-eval |
| Author effective SQL patterns for Databricks alerts | https://learn.microsoft.com/en-us/azure/databricks/sql/user/alerts/query-patterns |
| Optimize Databricks SQL queries with RELY constraints | https://learn.microsoft.com/en-us/azure/databricks/sql/user/queries/query-optimization-constraints |
| Operate multiple Databricks streaming queries per cluster | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/multiple-streams |
| Run Databricks Structured Streaming in production | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/production |
| Optimize and monitor Databricks real-time streaming performance | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/real-time/performance |
| Optimize stateful Structured Streaming on Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/stateful-streaming |
| Optimize stateless Structured Streaming queries on Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/stateless-streaming |
| Monitor Structured Streaming queries on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/stream-monitoring |
| Apply watermarks for stateful streaming on Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/watermarks |
| Optimize Databricks tables using liquid clustering | https://learn.microsoft.com/en-us/azure/databricks/tables/clustering |
| Leverage data skipping on Databricks tables | https://learn.microsoft.com/en-us/azure/databricks/tables/data-skipping |
| Optimize external table partition discovery in Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/tables/external-partition-discovery |
| Optimize VARIANT queries with variant shredding | https://learn.microsoft.com/en-us/azure/databricks/tables/features/variant-shredding |
| Use table history and time travel safely | https://learn.microsoft.com/en-us/azure/databricks/tables/history |
| Optimize Delta and Iceberg table file layout | https://learn.microsoft.com/en-us/azure/databricks/tables/operations/optimize |
| Use VACUUM to remove unused Delta files | https://learn.microsoft.com/en-us/azure/databricks/tables/operations/vacuum |
| Interpret table size versus storage usage | https://learn.microsoft.com/en-us/azure/databricks/tables/size |
| Tune Delta and Iceberg data file sizes | https://learn.microsoft.com/en-us/azure/databricks/tables/tune-file-size |
| Design Delta Lake data models for Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/transform/data-modeling |
| Apply join patterns for batch and streaming | https://learn.microsoft.com/en-us/azure/databricks/transform/join |
| Optimize join performance in Azure Databricks workloads | https://learn.microsoft.com/en-us/azure/databricks/transform/optimize-joins |
| Clean and validate data in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/transform/validate |
| Optimize Unity Catalog batch Python UDF performance | https://learn.microsoft.com/en-us/azure/databricks/udf/python-batch-udf |
| Download internet data into Azure Databricks volumes | https://learn.microsoft.com/en-us/azure/databricks/volumes/download-internet-files |

### Decision Making
| Topic | URL |
|-------|-----|
| Manage and change Azure Databricks subscription tier | https://learn.microsoft.com/en-us/azure/databricks/admin/account-settings/account |
| Plan migration from Standard to Premium Databricks tier | https://learn.microsoft.com/en-us/azure/databricks/admin/account-settings/standard-tier |
| Decide when to enable Mission Critical add-on for Databricks | https://learn.microsoft.com/en-us/azure/databricks/admin/mission-critical |
| Decide when and how to use serverless Databricks workspaces | https://learn.microsoft.com/en-us/azure/databricks/admin/workspace/serverless-workspaces |
| Decide and migrate agents from Model Serving to Apps | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/migrate-agent-to-apps |
| Choose BI tools that integrate with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/ai-bi/tools |
| Optimize Databricks AI Search costs and usage | https://learn.microsoft.com/en-us/azure/databricks/ai-search/cost-management |
| Decide and migrate from dbx to Databricks bundles | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/dbx/dbx-migrate |
| Migrate optimized LLM endpoints to provisioned throughput | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/migrate-provisioned-throughput |
| Decide when to use Databricks Light runtime | https://learn.microsoft.com/en-us/azure/databricks/archive/runtime/light |
| Plan migration of Databricks workloads to Spark 3.x | https://learn.microsoft.com/en-us/azure/databricks/archive/spark-3.x-migration/ |
| Choose BI connection patterns for metric views | https://learn.microsoft.com/en-us/azure/databricks/business-semantics/metric-views/bi-tools |
| Select aggregated vs unaggregated metric view materializations | https://learn.microsoft.com/en-us/azure/databricks/business-semantics/metric-views/choose-materialization-type |
| Choose and manage the default Unity Catalog catalog | https://learn.microsoft.com/en-us/azure/databricks/catalogs/default |
| Choose appropriate Azure Databricks compute types | https://learn.microsoft.com/en-us/azure/databricks/compute/choose-compute |
| Decide when and how to use GPU Databricks compute | https://learn.microsoft.com/en-us/azure/databricks/compute/gpu |
| Plan migration from classic to serverless Databricks compute | https://learn.microsoft.com/en-us/azure/databricks/compute/serverless/migration |
| Choose serverless streaming configurations in Databricks | https://learn.microsoft.com/en-us/azure/databricks/compute/serverless/streaming |
| Use Lakehouse Real-Time for low-latency SQL on Databricks | https://learn.microsoft.com/en-us/azure/databricks/compute/sql-warehouse/real-time |
| Choose and manage Azure Databricks SQL warehouse sizing and scaling | https://learn.microsoft.com/en-us/azure/databricks/compute/sql-warehouse/warehouse-behavior |
| Choose appropriate Azure Databricks SQL warehouse type | https://learn.microsoft.com/en-us/azure/databricks/compute/sql-warehouse/warehouse-types |
| Choose Databricks connection options for external data | https://learn.microsoft.com/en-us/azure/databricks/connect/ |
| Choose data modeling options in Databricks AI/BI dashboards | https://learn.microsoft.com/en-us/azure/databricks/dashboards/manage/data-modeling/ |
| Select batch vs streaming semantics in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/data-engineering/batch-vs-streaming |
| Choose procedural vs declarative data processing in Databricks | https://learn.microsoft.com/en-us/azure/databricks/data-engineering/procedural-vs-declarative |
| Choose tables, views, materialized and streaming tables | https://learn.microsoft.com/en-us/azure/databricks/data-engineering/tables-views |
| Process CDC, snapshots, and SCD in Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/data-engineering/what-is-cdc |
| Choose between ABAC and table-level filters | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/abac/abac-vs-rls-cm |
| Decide between managed and external Unity Catalog assets | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/managed-versus-external |
| Plan and execute Unity Catalog workspace upgrade | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/upgrade/ |
| Prepare and migrate to Unity Catalog–only Databricks workspaces | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/upgrade/uc-only-migration |
| Choose local development tools for Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/ |
| Migrate from legacy to new Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/migrate |
| Migrate from older to new Databricks Connect for Python | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/python/migrate |
| Migrate Scala projects to Databricks Connect 13.3+ | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/scala/migrate |
| Decide between CDKTF and Databricks Terraform provider | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/terraform/cdktf |
| Use Compatibility Mode for external table reads | https://learn.microsoft.com/en-us/azure/databricks/external-access/compatibility-mode |
| Manage Genie budgets and cost controls via Unity AI Gateway | https://learn.microsoft.com/en-us/azure/databricks/genie/budgets |
| Choose between Azure Databricks free options | https://learn.microsoft.com/en-us/azure/databricks/getting-started/free-trial-vs-free-edition |
| Choose Auto Loader file detection mode in Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/cloud-object-storage/auto-loader/file-detection-modes |
| Choose and manage Lakeflow community connectors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/community-connectors |
| Plan migration of existing data to Delta Lake on Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/data-migration/ |
| Understand Aha! connector plans and table coverage | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/aha-faq |
| Plan and configure MySQL ingestion with Lakeflow Connect | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/mysql |
| Understand Slack logs connector requirements and support | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/slack-access-integration-logs-faq |
| Understand Zip connector capabilities and FAQs | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/zip-faq |
| Understand Zoom Logs connector requirements and capabilities | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/zoom-logs-faq |
| Choose and start with Databricks ODBC and JDBC drivers | https://learn.microsoft.com/en-us/azure/databricks/integrations/jdbc-odbc-bi |
| Migrate from Simba Spark ODBC to Databricks ODBC | https://learn.microsoft.com/en-us/azure/databricks/integrations/odbc/migration |
| Migrate from Spark Submit tasks to JAR and notebook tasks | https://learn.microsoft.com/en-us/azure/databricks/jobs/tasks/spark-submit |
| Choose the right development language on Databricks | https://learn.microsoft.com/en-us/azure/databricks/languages/overview |
| Plan migration from deprecated Foundation Model Fine-tuning | https://learn.microsoft.com/en-us/azure/databricks/large-language-models/foundation-model-training/ |
| Clone Hive metastore pipelines to Unity Catalog via REST API | https://learn.microsoft.com/en-us/azure/databricks/ldp/clone-hms-to-uc |
| Use materialized views in Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/concepts/materialized-views |
| Compare Lakeflow pipelines with Spark Declarative Pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/concepts/spark-declarative-pipelines |
| Choose between standalone and Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/concepts/standalone-pipelines |
| Decide when to use Lakeflow streaming tables | https://learn.microsoft.com/en-us/azure/databricks/ldp/concepts/streaming-tables |
| Map Delta Live Tables features to Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/concepts/where-is-dlt |
| Choose between standalone tables and Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/dbsql/dbsql-for-ldp |
| Choose SQL or Python for Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/sql-vs-python |
| Use incremental refresh for materialized views vs streaming tables | https://learn.microsoft.com/en-us/azure/databricks/ldp/incremental-refresh |
| Migrate Databricks LIVE schema legacy pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/live-schema |
| Choose triggered vs continuous mode for Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/pipeline-mode |
| Optimize Databricks Feature Store cost and usage | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/cost-management |
| Migrate legacy online tables to Databricks Feature Store | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/migrate-from-online-tables |
| Select and use Databricks Online Feature Stores | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/online-feature-store |
| Upgrade workspace feature tables to Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/uc/upgrade-feature-table-to-uc |
| Plan capacity using model units for throughput | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/foundation-model-apis/model-units |
| Migrate Databricks ML workflows to Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/manage-model-lifecycle/migrate-to-uc |
| Upgrade ML workflows to Unity Catalog models | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/manage-model-lifecycle/upgrade-workflows |
| Migrate from legacy MLflow Model Serving to Databricks Model Serving | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/migrate-model-serving |
| Choose between Spark and Ray on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ray/spark-ray-overview |
| Plan for Databricks generative model lifecycle | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/retired-models-policy |
| Decide when to use distributed training on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/distributed-training/ |
| Choose and train deep-learning recommenders on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-recommender-models |
| Plan migration of data applications to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/migration/ |
| Assess and migrate ETL pipelines to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/migration/etl |
| Plan migration from Parquet data lake to Delta Lake | https://learn.microsoft.com/en-us/azure/databricks/migration/parquet-to-delta-lake |
| Plan migration from data warehouse to Databricks lakehouse | https://learn.microsoft.com/en-us/azure/databricks/migration/warehouse-to-lakehouse |
| Migrate from MLflow 2 Agent Evaluation to MLflow 3 | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/agent-eval-migration |
| Quick reference for migrating to MLflow 3 | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/agent-eval-migration-reference |
| Choose between open source and managed MLflow on Databricks | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/overview/oss-managed-diff |
| Choose Lakebase backup and restore methods | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/backup-methods |
| Migrate Databricks Asset Bundles to Autoscaling Lakebase | https://learn.microsoft.com/en-us/azure/databricks/oltp/update-to-autoscaling-dabs |
| Plan and understand Lakebase upgrade to Autoscaling | https://learn.microsoft.com/en-us/azure/databricks/oltp/upgrade-to-autoscaling |
| Choose pandas options and patterns on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pandas/ |
| Choose Microsoft Fabric integration for Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/fabric |
| Select Databricks options for external query federation | https://learn.microsoft.com/en-us/azure/databricks/query-federation/ |
| Choose and configure Databricks-to-Databricks federation | https://learn.microsoft.com/en-us/azure/databricks/query-federation/databricks |
| Migrate Databricks HTTP connections to serverless routing | https://learn.microsoft.com/en-us/azure/databricks/query-federation/http-migration |
| Migrate legacy Databricks query federation to Lakehouse Federation | https://learn.microsoft.com/en-us/azure/databricks/query-federation/migrate |
| Plan and execute Databricks Runtime 11.x migration | https://learn.microsoft.com/en-us/azure/databricks/release-notes/runtime/11.x-migration |
| Migrate workloads to Databricks Runtime 12.x safely | https://learn.microsoft.com/en-us/azure/databricks/release-notes/runtime/12.x-migration |
| Plan and execute Databricks Runtime 13.x migration | https://learn.microsoft.com/en-us/azure/databricks/release-notes/runtime/13.x-migration |
| Migrate workloads to Databricks Runtime 14.x safely | https://learn.microsoft.com/en-us/azure/databricks/release-notes/runtime/14.x-migration |
| Assess Databricks Runtime support lifecycle and upgrades | https://learn.microsoft.com/en-us/azure/databricks/release-notes/runtime/databricks-runtime-ver |
| Choose Azure Databricks serverless SKUs and DBU rates | https://learn.microsoft.com/en-us/azure/databricks/resources/pricing |
| Plan and manage Databricks serverless networking costs | https://learn.microsoft.com/en-us/azure/databricks/security/network/serverless-network-security/cost-management |
| Choose and use Azure Databricks workspace export options | https://learn.microsoft.com/en-us/azure/databricks/security/privacy/export-workspace-data |
| Choose between Spark Connect and Spark Classic | https://learn.microsoft.com/en-us/azure/databricks/spark/connect-vs-classic |
| Choose between SparkR and sparklyr on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/sparkr/sparkr-vs-sparklyr |
| Choose and size SQL warehouses for alerts | https://learn.microsoft.com/en-us/azure/databricks/sql/user/alerts/compute |
| Choose Structured Streaming output modes on Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/output-mode |
| Decide when to use real-time mode in Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/real-time/concepts |
