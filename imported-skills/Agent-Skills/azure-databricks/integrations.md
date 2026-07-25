# Azure Databricks — Integrations & Coding Patterns

> This is a reference file for the main [SKILL.md](SKILL.md). This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Databricks Supervisor API to orchestrate agents | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-bricks/supervisor-api |
| Connect Databricks agents to tools and MCP servers | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/agent-tool |
| Author Python AI agents and deploy via Model Serving | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/author-agent-model-serving |
| Enable Python code execution tools for agents | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/code-interpreter-tools |
| Create Databricks AI tools from Unity Catalog functions | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/create-custom-tool |
| Build multi-agent systems with Genie and LangGraph | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/multi-agent-genie |
| Build non-conversational agents with MLflow | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/non-conversational-agents |
| Query Databricks-deployed AI agents via APIs | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/query-agent |
| Build agent tools for structured data on Databricks | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/structured-retrieval-tools |
| Integrate Databricks AI agents with Microsoft Teams | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/teams-agent |
| Integrate Unity Catalog tools with LangChain and others | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/unity-catalog-tool-integration |
| Connect Databricks agents to unstructured data | https://learn.microsoft.com/en-us/azure/databricks/agents/agent-framework/unstructured-retrieval-tools |
| Connect external AI assistants to Databricks MCPs | https://learn.microsoft.com/en-us/azure/databricks/agents/mcp/connect-clients |
| Integrate Genie One via MCP server for agents | https://learn.microsoft.com/en-us/azure/databricks/agents/mcp/genie-mcp |
| Connect Databricks agents to MCP servers | https://learn.microsoft.com/en-us/azure/databricks/agents/mcp/use-mcp-in-agents |
| Query LLMs and agents via Databricks interfaces | https://learn.microsoft.com/en-us/azure/databricks/agents/query-llms |
| Manage Databricks AI/BI assets via REST APIs | https://learn.microsoft.com/en-us/azure/databricks/ai-bi/admin/use-apis |
| Integrate coding agents with Unity AI Gateway model providers | https://learn.microsoft.com/en-us/azure/databricks/ai-gateway/coding-agent-integration-model-provider-services |
| Integrate coding agents with Unity AI model services | https://learn.microsoft.com/en-us/azure/databricks/ai-gateway/coding-agent-integration-model-services |
| Query model provider services through Unity AI Gateway | https://learn.microsoft.com/en-us/azure/databricks/ai-gateway/query-model-provider-services |
| Query Unity Catalog model services via APIs | https://learn.microsoft.com/en-us/azure/databricks/ai-gateway/query-model-services |
| Use custom Python embedding models with Databricks AI Search | https://learn.microsoft.com/en-us/azure/databricks/ai-search/custom-embedding-model |
| Register and serve OSS embedding models for AI Search | https://learn.microsoft.com/en-us/azure/databricks/ai-search/embedding-with-oss-models |
| Use Databricks AI Search Python SDK example notebooks | https://learn.microsoft.com/en-us/azure/databricks/ai-search/example-notebooks |
| Integrate Databricks AI Search with OpenAI embeddings | https://learn.microsoft.com/en-us/azure/databricks/ai-search/vector-search-external-embedding-model-example |
| Use GTE foundation embeddings with Databricks AI Search | https://learn.microsoft.com/en-us/azure/databricks/ai-search/vector-search-foundation-embedding-model-gte-example |
| Implement Databricks AI Search with the Python SDK | https://learn.microsoft.com/en-us/azure/databricks/ai-search/vector-search-python-sdk-example |
| Set up legacy ABS-AQS streaming connector for Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/azure/aqs |
| Read and write data between Databricks and Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/databricks/archive/azure/cosmosdb |
| Stream data from Databricks to Azure Synapse with Structured Streaming | https://learn.microsoft.com/en-us/azure/databricks/archive/azure/stream-synapse |
| Configure legacy PolyBase integration between Databricks and Synapse | https://learn.microsoft.com/en-us/azure/databricks/archive/azure/synapse-polybase |
| Use Azure Databricks connector for Amazon Redshift | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/amazon-redshift |
| Use Databricks connector for Amazon S3 Select | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/amazon-s3-select |
| Connect Azure Databricks to Google BigQuery | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/bigquery |
| Connect Cassandra to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/cassandra |
| Integrate Couchbase with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/couchbase |
| Use Databricks JDBC connector between workspaces | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/databricks |
| Read and write data to Elasticsearch from Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/elasticsearch |
| Configure JDBC connections from Azure Databricks to external databases | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/jdbc |
| Query MariaDB from Azure Databricks using JDBC | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/mariadb |
| Read and write data to MongoDB Atlas from Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/mongodb |
| Query MySQL from Azure Databricks using JDBC | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/mysql |
| Connect Azure Databricks to Neo4j using neo4j-spark-connector | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/neo4j |
| Query PostgreSQL from Azure Databricks using JDBC | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/postgresql |
| Integrate Azure Databricks with Snowflake connector | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/snowflake |
| Use spark-xml library with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/spark-xml-library |
| Use the Apache Spark connector for Azure SQL Database and SQL Server in Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/sql-databases-azure |
| Connect Azure Databricks to SQL Server using JDBC | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/sql-server |
| Enable SQL Server CDC for Databricks ingestion | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/sql-server-cdc |
| Enable SQL Server change tracking for Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/sql-server-ct |
| Set up SQL Server DDL capture for Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/sql-server-ddl-legacy |
| Use Azure Databricks connector to query Azure Synapse | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/synapse-analytics |
| Connect Azure Databricks to Azure Synapse dedicated SQL pool | https://learn.microsoft.com/en-us/azure/databricks/archive/connectors/synapse-analytics-dedicated-pool |
| Use legacy Databricks clusters CLI commands | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/cli/clusters-cli |
| Run and manage Databricks jobs with legacy CLI | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/cli/jobs-cli |
| Work with Databricks repos via the legacy CLI | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/cli/repos-cli |
| Manage Databricks job runs with the legacy CLI | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/cli/runs-cli |
| Manage Databricks workspace objects with legacy CLI | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/cli/workspace-cli |
| Sync local files to Databricks workspaces using dbx | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/dbx/dbx-sync |
| Develop Databricks code with dbx in Visual Studio Code | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/dbx/ide-how-to |
| Configure Git folders with the Databricks VS Code extension | https://learn.microsoft.com/en-us/azure/databricks/archive/dev-tools/vscode-repos |
| Connect Azure Databricks to Excel via ODBC driver | https://learn.microsoft.com/en-us/azure/databricks/archive/integrations/excel |
| Read Databricks Unity Catalog tables from Iceberg clients | https://learn.microsoft.com/en-us/azure/databricks/archive/legacy/external-access-iceberg |
| Import external Hive tables stored in cloud storage into Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/legacy/hive-tables |
| Use Koalas (pandas API on Spark) in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/legacy/koalas |
| Use ai_generate_text in Databricks SQL for reviews | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/ai-generate-text-example |
| Enable Databricks inference tables via REST API | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/enable-model-serving-inference-tables |
| Convert Spark Parquet data to Petastorm datasets | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/petastorm |
| Run distributed training with Horovod on Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/train-model/horovod |
| Launch HorovodRunner distributed jobs on Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/train-model/horovod-runner |
| HorovodRunner CNN training examples on Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/train-model/horovod-runner-examples |
| Use horovod.spark for distributed deep learning | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/train-model/horovod-spark |
| Run Hugging Face NLP inference on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/train-model/model-inference-nlp |
| Use spark-tensorflow-distributor for distributed TensorFlow | https://learn.microsoft.com/en-us/azure/databricks/archive/machine-learning/train-model/spark-tf-distributor |
| Track ML runs with MLflow in Java and Scala | https://learn.microsoft.com/en-us/azure/databricks/archive/mlflow/quick-start-java-scala |
| Track ML experiments with MLflow in R on Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/mlflow/quick-start-r |
| Export and import ML models with MLeap on Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/model-export/mleap-model-export |
| Track PySpark training and save models as MLeap | https://learn.microsoft.com/en-us/azure/databricks/archive/model-export/tracking-ex-pyspark |
| Connect SQL Workbench/J to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/archive/partners/workbenchj |
| Access Amazon S3 from Azure Databricks using DBFS and APIs | https://learn.microsoft.com/en-us/azure/databricks/archive/storage/amazon-s3 |
| Connect Azure Databricks to Azure Data Lake Storage | https://learn.microsoft.com/en-us/azure/databricks/archive/storage/tutorial-azure-storage |
| Model Databricks metric views for consistent KPIs | https://learn.microsoft.com/en-us/azure/databricks/business-semantics/metric-views/basic-modeling |
| Query Unity Catalog metric views with MEASURE from Databricks tools | https://learn.microsoft.com/en-us/azure/databricks/business-semantics/metric-views/query |
| Build a sales analytics metric view with joins | https://learn.microsoft.com/en-us/azure/databricks/business-semantics/metric-views/tpch-example |
| Use parameters in Databricks metric views | https://learn.microsoft.com/en-us/azure/databricks/business-semantics/metric-views/use-parameters |
| Create and consume output tables in Databricks Clean Rooms | https://learn.microsoft.com/en-us/azure/databricks/clean-rooms/output-tables |
| Use system table queries to monitor SQL warehouses | https://learn.microsoft.com/en-us/azure/databricks/compute/sql-warehouse/monitor/queries |
| Configure JDBC Unity Catalog connections in Databricks | https://learn.microsoft.com/en-us/azure/databricks/connect/jdbc-connection |
| Use Spark data sources with Databricks external systems | https://learn.microsoft.com/en-us/azure/databricks/connect/spark-data-sources |
| Connect Azure Databricks Structured Streaming to Kafka | https://learn.microsoft.com/en-us/azure/databricks/connect/streaming/kafka/ |
| Subscribe to Google Pub/Sub with Databricks | https://learn.microsoft.com/en-us/azure/databricks/connect/streaming/pub-sub |
| Stream data from Apache Pulsar into Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/connect/streaming/pulsar |
| Use Unity Catalog service credentials to call cloud APIs | https://learn.microsoft.com/en-us/azure/databricks/connect/unity-catalog/cloud-services/use-service-credentials |
| Connect Unity Catalog to ADLS Gen2 external locations | https://learn.microsoft.com/en-us/azure/databricks/connect/unity-catalog/cloud-storage/external-locations-adls |
| Create OneLake external locations with Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/connect/unity-catalog/cloud-storage/external-locations-onelake |
| Configure Cloudflare R2 external locations in Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/connect/unity-catalog/cloud-storage/external-locations-r2 |
| Connect Azure Databricks Unity Catalog to AWS S3 | https://learn.microsoft.com/en-us/azure/databricks/connect/unity-catalog/cloud-storage/s3/s3-external-location-manual |
| Use Genie Code Agent to author AI/BI dashboards | https://learn.microsoft.com/en-us/azure/databricks/dashboards/manage/dashboard-agent |
| Migrate Tableau and Power BI files to Databricks dashboards | https://learn.microsoft.com/en-us/azure/databricks/dashboards/manage/import-bi |
| Embed Databricks dashboards via iframe with access control | https://learn.microsoft.com/en-us/azure/databricks/dashboards/share/embedding/basic |
| Use Databricks dashboard REST APIs for management | https://learn.microsoft.com/en-us/azure/databricks/dashboards/tutorials/dashboard-crud-api |
| Manage AI/BI dashboards via Workspace and Lakeview APIs | https://learn.microsoft.com/en-us/azure/databricks/dashboards/tutorials/workspace-dashboard-api |
| Share ABAC-protected tables via OpenSharing | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/abac/opensharing |
| Create data profiles using Databricks quality_monitors API | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/data-quality-monitoring/data-profiling/create-monitor-api |
| Add external lineage metadata to Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/data-governance/unity-catalog/external-lineage |
| Upsert into Delta Lake tables using MERGE | https://learn.microsoft.com/en-us/azure/databricks/delta/merge |
| Create user-defined operators in Lakeflow Designer | https://learn.microsoft.com/en-us/azure/databricks/designer/user-operators |
| Run Databricks CLI from Azure Cloud Shell | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/databricks-cli-from-azure-cloud-shell |
| Download Databricks billable usage logs with CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/account-billable-usage-commands |
| Manage Databricks account resources with CLI account commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/account-commands |
| Use Databricks CLI account networks commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/account-networks-commands |
| Manage OAuth published apps via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/account-o-auth-published-apps-commands |
| Configure published app integrations with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/account-published-app-integration-commands |
| Call Databricks REST APIs using CLI api command | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/api-commands |
| Manage Databricks apps with CLI commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/apps-commands |
| Use Databricks CLI clean-rooms command group | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/clean-rooms-commands |
| Create and manage external data connections via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/connections-commands |
| Manage consumer fulfillments with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/consumer-fulfillments-commands |
| Manage consumer installations via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/consumer-installations-commands |
| Use Databricks CLI credentials commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/credentials-commands |
| Get current user via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/current-user-commands |
| Manage data classification with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/data-classification-commands |
| Manage data quality via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/data-quality-commands |
| Use deprecated data-sources CLI commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/data-sources-commands |
| Manage Databricks databases with CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/database-commands |
| Assign tags to Unity Catalog entities via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/entity-tag-assignments-commands |
| Manage Databricks environments using CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/environments-commands |
| Configure external lineage via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/external-lineage-commands |
| Manage external locations in Unity Catalog CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/external-locations-commands |
| Register external metadata with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/external-metadata-commands |
| Manage feature store via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/feature-engineering-commands |
| Perform file operations with Databricks fs CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/fs-commands |
| Configure Git credentials using Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/git-credentials-commands |
| Manage global init scripts via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/global-init-scripts-commands |
| Manage instance pools with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/instance-pools-commands |
| Create and manage jobs via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/jobs-commands |
| Manage Knowledge Assistants with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/knowledge-assistants-commands |
| Work with Databricks Labs apps via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/labs-commands |
| Manage Lakeview dashboards using Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/lakeview-commands |
| Use Lakeview embedded dashboards via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/lakeview-embedded-commands |
| Install and manage libraries with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/libraries-commands |
| Use Databricks CLI metastores command group | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/metastores-commands |
| Manage workspace model registry via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/model-registry-commands |
| Manage model versions in Unity Catalog CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/model-versions-commands |
| Configure notification destinations via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/notification-destinations-commands |
| Create and manage online tables via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/online-tables-commands |
| Use Azure Databricks CLI pipelines command group | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/pipelines-commands |
| Use Databricks CLI policy-families commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/policy-families-commands |
| Manage marketplace exchange filters with CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/provider-exchange-filters-commands |
| Manage Databricks marketplace exchanges via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/provider-exchanges-commands |
| Manage marketplace provider files using CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/provider-files-commands |
| Manage Databricks marketplace listings via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/provider-listings-commands |
| Handle marketplace personalization requests with CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/provider-personalization-requests-commands |
| Manage provider analytics dashboards via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/provider-provider-analytics-dashboards-commands |
| Manage marketplace providers using Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/provider-providers-commands |
| Use Databricks CLI providers command group | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/providers-commands |
| Use deprecated quality-monitor-v2 CLI commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/quality-monitor-v2-commands |
| Manage quality monitors with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/quality-monitors-commands |
| Manage Databricks SQL queries via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/queries-commands |
| Use deprecated queries-legacy CLI commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/queries-legacy-commands |
| Access query-history using Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/query-history-commands |
| Use Databricks CLI recipient-activation commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/recipient-activation-commands |
| Manage recipient federation policies with Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/recipient-federation-policies-commands |
| Manage share recipients using Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/recipients-commands |
| Manage Unity Catalog registered models via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/registered-models-commands |
| Manage Databricks repos (Git folders) via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/repos-commands |
| Manage Unity Catalog resource quotas via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/resource-quotas-commands |
| Handle Unity Catalog access requests with CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/rfa-commands |
| Use Databricks CLI sandbox command group | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/sandbox-commands |
| Manage Unity Catalog schemas via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/schemas-commands |
| Manage Databricks secrets and scopes via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/secrets-commands |
| Manage service principal secrets via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/service-principal-secrets-proxy-commands |
| Manage Databricks service principals via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/service-principals-commands |
| Use service-principals-v2 identities with CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/service-principals-v2-commands |
| Manage model serving endpoints via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/serving-endpoints-commands |
| Configure workspace settings using Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/settings-commands |
| Manage Unity Catalog shares via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/shares-commands |
| Use Databricks CLI ssh commands for tunnels | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/ssh-commands |
| Manage Unity Catalog storage credentials via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/storage-credentials-commands |
| Sync local files to Databricks workspace via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/sync-commands |
| Manage system schemas via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/system-schemas-commands |
| Manage table constraints using Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/table-constraints-commands |
| Manage Unity Catalog tables via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/tables-commands |
| Manage governed tag policies via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/tag-policies-commands |
| Generate temporary path credentials via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/temporary-path-credentials-commands |
| Generate temporary table credentials via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/temporary-table-credentials-commands |
| Use Databricks CLI token-management admin commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/token-management-commands |
| Manage Databricks tokens with CLI commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/tokens-commands |
| Manage Databricks users via CLI commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/users-commands |
| Use Databricks CLI users-v2 management commands | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/users-v2-commands |
| Retrieve Databricks CLI version information | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/version-command |
| Manage Unity Catalog volumes via Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/volumes-commands |
| Administer SQL warehouses using Databricks CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/warehouses-commands |
| Configure Unity Catalog workspace bindings via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/workspace-bindings-commands |
| Manage Databricks workspace files with CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/workspace-commands |
| Update Databricks workspace settings with CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/workspace-conf-commands |
| Manage Databricks workspace tag assignments via CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/cli/reference/workspace-entity-tag-assignments-commands |
| Add and configure Genie Agent resources in apps | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-apps/genie |
| Integrate Databricks Apps with platform resources | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-apps/resources |
| Use Databricks Connect to integrate IDEs with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/ |
| Use Databricks Connect within Databricks notebooks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/notebooks |
| Use Databricks Utilities with Databricks Connect for Python | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/python/databricks-utilities |
| Use Databricks Connect for Python code patterns | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/python/examples |
| Install and configure Databricks Connect for Python | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/python/install |
| Run PyCharm code on classic Databricks compute | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/python/tutorial-cluster |
| Run Python code on serverless compute with Databricks Connect | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/python/tutorial-serverless |
| Use Databricks Utilities via Databricks Connect for Scala | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/scala/databricks-utilities |
| Use Databricks Connect for Scala code examples | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-connect/scala/examples |
| Run Databricks SQL queries using the SQL CLI | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-sql-cli |
| Use Databricks dbutils APIs in notebooks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/databricks-utils |
| Configure JetBrains DataGrip to connect to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/datagrip |
| Configure DBeaver to work with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/dbeaver |
| Run SQL from Go using Databricks SQL Driver | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/go-sql-driver |
| Use Databricks SQL Driver for Node.js securely | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/nodejs-sql-driver |
| Use pyodbc to connect Python apps to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/pyodbc |
| Run SQL on Databricks with Python SQL Connector | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/python-sql-connector |
| Use the English SDK to generate Spark code | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/sdk-english |
| Automate Azure Databricks with Go SDK | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/sdk-go |
| Automate Azure Databricks with Java SDK | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/sdk-java |
| Use Databricks JavaScript SDKs for automation | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/sdk-javascript |
| Automate Azure Databricks with Python SDK | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/sdk-python |
| Automate Azure Databricks with R SDK | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/sdk-r |
| Integrate SQLAlchemy with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/sqlalchemy |
| Use the Databricks SQLTools driver in VS Code | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/sqltools-driver |
| Automate Unity Catalog deployment with Databricks Terraform | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/terraform/automate-uc |
| Provision Databricks clusters, notebooks, and jobs with Terraform | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/terraform/cluster-notebook-job |
| Manage Azure Databricks workspace resources using Terraform | https://learn.microsoft.com/en-us/azure/databricks/dev-tools/terraform/workspace-management |
| Access Unity Catalog Iceberg tables from Apache Iceberg clients | https://learn.microsoft.com/en-us/azure/databricks/external-access/iceberg |
| Use Unity REST API from external Delta clients | https://learn.microsoft.com/en-us/azure/databricks/external-access/unity-rest |
| Unzip and read compressed files in Databricks | https://learn.microsoft.com/en-us/azure/databricks/files/unzip-files |
| Integrate Genie Code with GitHub via MCP | https://learn.microsoft.com/en-us/azure/databricks/genie-code/github-mcp |
| Connect Genie Code to MCP servers and SaaS tools | https://learn.microsoft.com/en-us/azure/databricks/genie-code/mcp |
| Integrate Genie Agents via Conversation and Management APIs | https://learn.microsoft.com/en-us/azure/databricks/genie/conversation-api |
| Use common Auto Loader data loading patterns | https://learn.microsoft.com/en-us/azure/databricks/ingestion/cloud-object-storage/auto-loader/patterns |
| Load Unity Catalog tables using COPY INTO from ADLS | https://learn.microsoft.com/en-us/azure/databricks/ingestion/cloud-object-storage/copy-into/unity-catalog |
| Convert Parquet and Iceberg tables to Delta Lake | https://learn.microsoft.com/en-us/azure/databricks/ingestion/data-migration/convert-to-delta |
| Access file metadata via _metadata in Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/file-metadata-column |
| Ingest Google Drive files with Databricks connectors | https://learn.microsoft.com/en-us/azure/databricks/ingestion/google-drive |
| Create Databricks Lakeflow ingestion pipelines from MySQL | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/mysql-pipeline |
| Reference NetSuite connector details for Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/netsuite-reference |
| Build managed Pendo ingestion pipelines with Lakeflow Connect | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/pendo-pipeline |
| Ingest PostgreSQL data into Databricks with Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/postgresql-pipeline |
| Reference Salesforce connector behavior in Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/salesforce-reference |
| Ingest SQL Server data into Databricks with Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/sql-server-pipeline |
| Configure TikTok Ads authentication for Lakeflow | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/tiktok-ads-source-setup |
| Use Veeva Vault connector technical reference | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/veeva-vault-reference |
| Configure Workday HCM authentication for Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/workday-hcm-setup |
| Configure Zendesk Support OAuth for Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/lakeflow-connect/zendesk-support-source-setup |
| Ingest OpenTelemetry data into Databricks via Zerobus | https://learn.microsoft.com/en-us/azure/databricks/ingestion/opentelemetry/ |
| Ingest SFTP files using Lakeflow Auto Loader | https://learn.microsoft.com/en-us/azure/databricks/ingestion/sftp |
| Ingest SharePoint files into Delta tables with Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/sharepoint |
| Ingest semi-structured data as VARIANT in Databricks | https://learn.microsoft.com/en-us/azure/databricks/ingestion/variant |
| Use Arrow Flight with Zerobus Ingest for batch ingestion | https://learn.microsoft.com/en-us/azure/databricks/ingestion/zerobus-arrow-flight |
| Ingest data with Zerobus Ingest in Lakeflow Connect | https://learn.microsoft.com/en-us/azure/databricks/ingestion/zerobus-ingest |
| Use Azure Databricks Excel Add-in for Lakehouse data | https://learn.microsoft.com/en-us/azure/databricks/integrations/excel |
| Write Excel data back to Databricks Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/integrations/excel-write-back |
| Use Databricks Connector to access data from Google Sheets | https://learn.microsoft.com/en-us/azure/databricks/integrations/google-sheets/ |
| Set up Databricks Connector for Google Sheets | https://learn.microsoft.com/en-us/azure/databricks/integrations/google-sheets/connect |
| Use Databricks Connector to query data in Google Sheets | https://learn.microsoft.com/en-us/azure/databricks/integrations/google-sheets/query-data |
| Connect tools using the Databricks JDBC Driver | https://learn.microsoft.com/en-us/azure/databricks/integrations/jdbc-oss/ |
| Use JDBC metadata for Databricks metric views | https://learn.microsoft.com/en-us/azure/databricks/integrations/jdbc-oss/metadata |
| Java API reference for the Databricks JDBC driver | https://learn.microsoft.com/en-us/azure/databricks/integrations/jdbc-oss/reference |
| Manage Unity Catalog volume files via Databricks JDBC | https://learn.microsoft.com/en-us/azure/databricks/integrations/jdbc-oss/volumes |
| Connect with legacy Simba Databricks JDBC driver | https://learn.microsoft.com/en-us/azure/databricks/integrations/jdbc/ |
| Manage Unity Catalog volume files via JDBC Driver | https://learn.microsoft.com/en-us/azure/databricks/integrations/jdbc/volumes |
| Connect Lovable no-code apps to Databricks via OAuth | https://learn.microsoft.com/en-us/azure/databricks/integrations/lovable |
| Integrate Databricks Genie MCP with Microsoft Foundry | https://learn.microsoft.com/en-us/azure/databricks/integrations/microsoft-foundry |
| Integrate Databricks Genie with Microsoft 365 Copilot | https://learn.microsoft.com/en-us/azure/databricks/integrations/msft-m365-copilot |
| Connect Azure Databricks to Microsoft Power Platform | https://learn.microsoft.com/en-us/azure/databricks/integrations/msft-power-platform/ |
| Build Copilot Studio agents with Azure Databricks data | https://learn.microsoft.com/en-us/azure/databricks/integrations/msft-power-platform/copilot-studio |
| Create Azure Databricks connections in Microsoft Power Platform | https://learn.microsoft.com/en-us/azure/databricks/integrations/msft-power-platform/setup |
| Use Databricks data in Power Apps and Power Automate | https://learn.microsoft.com/en-us/azure/databricks/integrations/msft-power-platform/usage |
| Set up Databricks Genie app in Microsoft Teams | https://learn.microsoft.com/en-us/azure/databricks/integrations/msft-teams |
| Connect Python and R clients to Databricks via ODBC | https://learn.microsoft.com/en-us/azure/databricks/integrations/odbc/connect-databricks-excel-python-r |
| Manage Unity Catalog volume files via Databricks ODBC | https://learn.microsoft.com/en-us/azure/databricks/integrations/odbc/volumes |
| Connect Replit-hosted apps to Azure Databricks with OAuth | https://learn.microsoft.com/en-us/azure/databricks/integrations/replit |
| Configure Git-backed Azure Databricks Lakeflow Jobs | https://learn.microsoft.com/en-us/azure/databricks/jobs/git |
| Implement watermark-based incremental For each jobs | https://learn.microsoft.com/en-us/azure/databricks/jobs/how-to/foreach-watermark-tutorial |
| Orchestrate Azure Databricks jobs with Apache Airflow | https://learn.microsoft.com/en-us/azure/databricks/jobs/how-to/use-airflow-with-jobs |
| Run dbt Core transformations in Lakeflow Jobs | https://learn.microsoft.com/en-us/azure/databricks/jobs/how-to/use-dbt-in-workflows |
| Create and run Scala or Java JAR tasks on Databricks | https://learn.microsoft.com/en-us/azure/databricks/jobs/how-to/use-jars-in-workflows |
| Package and run Python wheels in Lakeflow Jobs | https://learn.microsoft.com/en-us/azure/databricks/jobs/how-to/use-python-wheels-in-workflows |
| Access job and task parameters from Databricks code | https://learn.microsoft.com/en-us/azure/databricks/jobs/parameter-use |
| Use dbutils task values to pass data between tasks | https://learn.microsoft.com/en-us/azure/databricks/jobs/task-values |
| Run dbt Core projects with Lakeflow Jobs | https://learn.microsoft.com/en-us/azure/databricks/jobs/tasks/dbt |
| Orchestrate dbt platform jobs from Databricks | https://learn.microsoft.com/en-us/azure/databricks/jobs/tasks/dbt-platform |
| Configure pipeline tasks within Lakeflow Jobs workflows | https://learn.microsoft.com/en-us/azure/databricks/jobs/tasks/pipeline |
| Implement AUTO CDC APIs for change data capture | https://learn.microsoft.com/en-us/azure/databricks/ldp/cdc |
| Configure Lakeflow sinks to external systems | https://learn.microsoft.com/en-us/azure/databricks/ldp/concepts/sinks |
| Use Python notebooks with standalone pipelines on serverless compute | https://learn.microsoft.com/en-us/azure/databricks/ldp/dbsql/using-python |
| Define Lakeflow datasets with Python decorators | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/definition-function |
| Use append_flow decorator for streaming tables | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/ldp-python-ref-append-flow |
| Process CDC feeds with create_auto_cdc_flow | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/ldp-python-ref-apply-changes |
| Process snapshot CDC with create_auto_cdc_from_snapshot_flow | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/ldp-python-ref-apply-changes-from-snapshot |
| Use foreach_batch_sink for custom streaming logic | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/ldp-python-ref-foreach-batch-sink |
| Create sinks to Kafka, Event Hubs, or Delta | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/ldp-python-ref-sink |
| Implement update_flow sinks for stateful streaming | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/ldp-python-ref-update-flow |
| Develop Lakeflow pipeline code using Python | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/python-dev |
| Develop Lakeflow pipelines using SQL syntax | https://learn.microsoft.com/en-us/azure/databricks/ldp/developer/sql-dev |
| Implement pipeline event hooks for custom monitoring | https://learn.microsoft.com/en-us/azure/databricks/ldp/event-hooks |
| Use Azure Event Hubs via Kafka endpoint in pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/event-hubs |
| Use ForEachBatch sink for custom streaming outputs | https://learn.microsoft.com/en-us/azure/databricks/ldp/for-each-batch |
| Import Python modules into Lakeflow pipelines | https://learn.microsoft.com/en-us/azure/databricks/ldp/import-workspace-files |
| Configure Lakeflow sinks for Delta, Kafka, and custom targets | https://learn.microsoft.com/en-us/azure/databricks/ldp/ldp-sinks |
| Load data into Lakeflow pipelines from multiple sources | https://learn.microsoft.com/en-us/azure/databricks/ldp/load |
| Define transformations in Lakeflow pipelines with Spark and ML | https://learn.microsoft.com/en-us/azure/databricks/ldp/transform |
| Manage AI Runtime jobs using the air CLI | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/cli/ |
| Reference air CLI commands for AI Runtime workloads | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/cli/command-reference |
| AI Runtime CLI multi-GPU workload examples | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/cli/examples/ |
| Fine-tune Llama-3.1-8B with FSDP on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/cli/examples/multinode-llm-sft |
| Batch LLM inference with Ray Data and vLLM on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/cli/examples/ray-batch-inference |
| Run Ray Train distributed fine-tuning on AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/cli/examples/ray-train-distributed |
| Connect notebooks and IDEs to Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/connecting |
| Use serverless_gpu API for multi-GPU training on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/distributed-training |
| Run classic ML with GPU on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/gpu-classic-ml |
| Use DDP for multi-GPU training on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/gpu-ddp |
| Distributed DeepSpeed training on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/gpu-deepspeed |
| Scale multi-GPU distributed training on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/gpu-distributed-training |
| Train large models with FSDP on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/gpu-fsdp |
| Build deep learning recommenders on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/gpu-recommendation |
| Get started with H100 serverless GPUs on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-api-h100-starter |
| Train CNN image classifier on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-cnn-mnist |
| Fine-tune Qwen2-0.5B with LoRA on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-distributed-finetune-qwen2-0.5b |
| Fine-tune OpenAI gpt-oss-20b with Databricks distributed training | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-distributed-gpt-oss-20b |
| Train Transformers with PyTorch FSDP on Databricks serverless GPU | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-distributed-pytorch-fsdp |
| Distributed fine-tuning GPT-OSS 120B on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-gpt-oss-120b-ddp-fsdp |
| Train two-tower recommenders on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-recommender-system-lightning |
| Train RetinaNet object detection on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-retinanet-image-detection-model-training |
| Forecast time series with GluonTS on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-time-series-gluonts-101 |
| Train XGBoost regression on a single Databricks GPU | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-xgboost |
| Train and serve YOLO11n object detection on Databricks AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/examples/tutorials/sgc-yolo11n-detect-coco128 |
| Track experiments and monitor GPUs on AI Runtime | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ai-runtime/tracking-observability |
| Use Hyperopt with HorovodRunner for distributed tuning on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl-hyperparam-tuning/hyperopt-distributed-ml |
| Select best model type with Hyperopt and MLflow on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl-hyperparam-tuning/hyperopt-model-selection |
| Parallelize Hyperopt hyperparameter tuning with MLflow on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl-hyperparam-tuning/hyperopt-spark-mlflow-integration |
| Integrate Optuna hyperparameter tuning with MLflow on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl-hyperparam-tuning/optuna |
| Reference for Databricks AutoML Python API methods | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl/automl-api-reference |
| Train classification models with Databricks AutoML Python API | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl/classification-train-api |
| Integrate Databricks AutoML with Feature Store tables | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl/feature-store-integration |
| Train time-series forecasting models with Databricks AutoML API | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl/forecasting-train-api |
| Train regression models with Databricks AutoML Python API | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/automl/regression-train-api |
| Configure automatic feature lookup in Databricks Model Serving | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/automatic-feature-lookup |
| Use Databricks Feature Views API for feature pipelines | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/declarative-api-reference |
| Implement on-demand feature computation at inference | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/on-demand-features |
| Use Databricks features in real-time online workflows | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/online-workflows |
| Publish Databricks feature tables to external online stores | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/publish-features |
| Use the Databricks Feature Engineering Python client | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/python-api |
| Integrate third-party online stores with Feature Store | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/third-party-online-stores |
| Train models using Databricks feature tables | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/train-models-with-feature-store |
| Train models using Databricks Feature Views | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/feature-store/train-with-declarative-features |
| Create external model endpoints for OpenAI on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/foundation-models/external-models-tutorial |
| Use Unity Catalog foundation models in Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/foundation-models/pretrained-models |
| Load training data with Mosaic Streaming on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/load-data/streaming |
| Save and load TFRecord data with Spark and TensorFlow on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/load-data/tfrecords-save-load |
| Copy Databricks model versions to Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/manage-model-lifecycle/migrate-models |
| Create and call Databricks foundation model endpoints | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/create-foundation-model-endpoints |
| Deploy custom Python code with Databricks Model Serving | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/deploy-custom-python-code |
| Call provider-native OpenAI, Anthropic, Gemini APIs | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/provider-native-apis |
| Use Anthropic Messages API on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-anthropic-messages |
| Query chat and general models via Unity AI Gateway | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-chat-models |
| Query embedding models through Unity AI Gateway | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-embedding-models |
| Use Google Gemini API through Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-gemini-api |
| Use Databricks Open Responses API across providers | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-open-responses-models |
| Use OpenAI Responses API via Databricks endpoints | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-openai-responses |
| Query reasoning models via Databricks APIs | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-reason-models |
| Query route-optimized Databricks model and feature endpoints | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-route-optimization |
| Query vision foundation models on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/query-vision-models |
| Format and send scoring requests to Databricks custom model endpoints | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/score-custom-model-endpoints |
| Send requests to Databricks foundation model endpoints | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/score-foundation-models |
| Enable web search grounding for Databricks models | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/model-serving/web-search |
| Featurization for transfer learning with pandas UDFs | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/preprocess-data/transfer-learning-tensorflow |
| Integrate Ray and Spark in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ray/connect-spark-ray |
| Integrate MLflow tracking with Ray on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/ray/ray-mlflow |
| Implement distributed image inference on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/reference-solutions/images-etl-inference |
| Use DeepSpeed distributor for large PyTorch models on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/distributed-training/deepspeed |
| Train Spark ML models with pyspark.ml.connect on Databricks Connect | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/distributed-training/distributed-ml-for-spark-connect |
| Run distributed PyTorch training with TorchDistributor on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/distributed-training/spark-pytorch-distributor |
| Fine-tune Hugging Face models on Databricks GPU | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/huggingface/fine-tune-model |
| Prepare datasets for fine-tuning Hugging Face models on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/huggingface/load-data |
| Use deprecated sparkdl.xgboost for distributed XGBoost | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/sparkdl-xgboost |
| Use TensorBoard for ML debugging on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/tensorboard |
| Train XGBoost models on Azure Databricks with Python and Scala | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/xgboost |
| Integrate XGBoost with Spark ML pipelines in Scala | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/xgboost-scala |
| Use xgboost.spark for distributed XGBoost on Databricks | https://learn.microsoft.com/en-us/azure/databricks/machine-learning/train-model/xgboost-spark |
| Log MLflow model dependencies for Databricks deployment | https://learn.microsoft.com/en-us/azure/databricks/mlflow/log-model-dependencies |
| Integrate Workspace Model Registry webhooks | https://learn.microsoft.com/en-us/azure/databricks/mlflow/model-registry-webhooks |
| Log, load, and register MLflow models in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/mlflow/models |
| Implement MLflow GenAI code-based scorer patterns | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/code-based-scorer-examples |
| Use mlflow.genai.evaluate as evaluation harness | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/eval-harness |
| Use MLflow built-in LLM judges | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/judges/ |
| Create guidelines-based LLM judges in MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/judges/guidelines |
| Apply relevance judges for RAG systems | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/judges/is_context_relevant |
| Use RetrievalSufficiency judge for context coverage | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/judges/is_context_sufficient |
| Assess GenAI correctness with MLflow judge | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/judges/is_correct |
| Check RAG groundedness with MLflow judge | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/judges/is_grounded |
| Evaluate GenAI safety with MLflow judge | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/judges/is_safe |
| API reference for MLflow scorer lifecycle methods | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/concepts/production-quality-monitoring |
| Simulate conversations to test conversational agents | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/conversation-simulation |
| Implement custom LLM judges with make_judge | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/custom-judge/ |
| Tutorial: Build custom judges with make_judge | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/custom-judge/create-custom-judge |
| Develop and iterate MLflow GenAI code-based scorers | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/custom-scorer-dev-workflow |
| Create custom code-based scorers in MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/custom-scorers |
| MLflow evaluation data and predict_fn patterns | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/eval-examples |
| Evaluate GenAI apps with mlflow.genai.evaluate | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/evaluate-app |
| Evaluate multi-turn conversations in MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/eval-monitor/evaluate-conversations |
| Integrate MLflow Tracing with GenAI apps in local IDEs | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/getting-started/tracing/tracing-ide |
| Integrate MLflow Tracing in Databricks GenAI notebooks | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/getting-started/tracing/tracing-notebook |
| Create and manage prompts with MLflow SDK | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/prompt-version-mgmt/prompt-registry/create-and-edit-prompts |
| Apply Prompt Registry operations with examples | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/prompt-version-mgmt/prompt-registry/examples |
| Track prompt and app versions with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/prompt-version-mgmt/prompt-registry/track-prompts-app-versions |
| Choose automatic vs manual MLflow tracing for GenAI apps | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/app-instrumentation/ |
| Enable automatic MLflow genAI tracing in Databricks | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/app-instrumentation/automatic |
| Add MLflow tracing via Python function decorators | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/app-instrumentation/manual-tracing/function-decorator |
| Use MLflow low-level client APIs for tracing | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/app-instrumentation/manual-tracing/low-level-api |
| Use mlflow.start_span context managers for fine-grained tracing | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/app-instrumentation/manual-tracing/span-tracing |
| Instrument Node.js apps with MLflow Tracing SDK | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/app-instrumentation/typescript-sdk |
| Integrate MLflow Tracing with GenAI frameworks | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/ |
| Enable MLflow tracing for AG2 multi-agent workflows | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/ag2 |
| Integrate MLflow tracing with Agno agents | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/agno |
| Enable MLflow tracing for Anthropic models | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/anthropic |
| Trace AutoGen multi-agent runs with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/autogen |
| Trace Amazon Bedrock LLM usage with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/bedrock |
| Integrate Claude Code tracing with MLflow on Databricks | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/claude-code |
| Integrate MLflow tracing with CrewAI multi-agent flows | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/crewai |
| Trace Databricks Foundation Models via MLflow OpenAI autolog | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/databricks-foundation-models |
| Trace DeepSeek via OpenAI-compatible MLflow autolog | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/deepseek |
| Enable MLflow tracing for DSPy workflows | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/dspy |
| Enable MLflow tracing for Google Gemini calls | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/gemini |
| Configure MLflow tracing for Groq SDK usage | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/groq |
| Trace Haystack pipelines and components with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/haystack |
| Trace Instructor-based structured LLM outputs with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/instructor |
| Trace LangChain chains using MLflow autolog | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/langchain |
| Capture LangGraph executions with MLflow tracing | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/langgraph |
| Enable MLflow tracing for LiteLLM gateway calls | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/litellm |
| Trace LlamaIndex engines and workflows in MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/llama_index |
| Configure MLflow tracing for Mistral AI SDK | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/mistral |
| Trace local Ollama OpenAI-compatible endpoints with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/ollama |
| Export MLflow traces to OpenTelemetry-compatible backends | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/open-telemetry |
| Enable MLflow tracing for OpenAI model calls | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/openai |
| Trace OpenAI Agents SDK multi-agent workflows | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/openai-agent |
| Autolog PydanticAI agents and tools with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/pydantic-ai |
| Trace Semantic Kernel prompts and plugins in MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/semantic-kernel |
| Trace Smolagents workflows with MLflow autolog | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/smolagents |
| Trace Strands Agents SDK runs using MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/strands |
| Trace deprecated OpenAI Swarm agents with MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/swarm |
| Enable MLflow tracing for txtai semantic workflows | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/integrations/txtai |
| Use the MLflow MCP server for trace access | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/mlflow-mcp |
| Access MLflow trace metadata and spans via SDK | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/observe-with-traces/access-trace-data |
| Query Unity Catalog OpenTelemetry traces with Databricks | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/observe-with-traces/query-dbsql |
| Example queries using mlflow.search_traces() | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/observe-with-traces/search-traces-examples |
| Export Langfuse OpenTelemetry traces to Databricks MLflow | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tracing/third-party/langfuse |
| Create custom MLflow scorers for RAG evaluation | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tutorials/examples/custom-scorers |
| Optimize chained prompts with MLflow multi-prompt workflows | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tutorials/examples/multi-prompt-optimization |
| Implement MLflow prompt optimization with GEPA and GPT-OSS | https://learn.microsoft.com/en-us/azure/databricks/mlflow3/genai/tutorials/examples/prompt-optimization-quickstart |
| Connect and query Lakebase from SQL clients | https://learn.microsoft.com/en-us/azure/databricks/oltp/instances/query/connect |
| Query Lakebase instances from Databricks notebooks | https://learn.microsoft.com/en-us/azure/databricks/oltp/instances/query/notebook |
| Register Lakebase databases with Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/oltp/instances/register-uc |
| Use Lakebase Autoscaling APIs, CLI, and SDKs | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/api-usage |
| Get started with Terraform for Lakebase projects | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/automate-with-terraform |
| Use Databricks CLI to manage Lakebase projects | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/cli |
| Call Lakebase Data API for Postgres access | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/data-api |
| Connect external apps to Lakebase via SDK and OAuth | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/external-apps-connect |
| Call Lakebase REST API for external app access | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/external-apps-manual-api |
| Connect external monitoring tools to Lakebase | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/external-monitoring-tools |
| Use framework-specific code to connect to Lakebase | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/framework-examples |
| Integrate Lakebase Postgres with Databricks Lakehouse | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/lakehouse-integrations |
| Capture Lakebase Postgres changes into Delta tables | https://learn.microsoft.com/en-us/azure/databricks/oltp/projects/quickstart-lakebase-cdf |
| Read Databricks-to-Databricks OpenSharing data | https://learn.microsoft.com/en-us/azure/databricks/opensharing/read-data-databricks |
| Read OpenSharing data using bearer token credentials | https://learn.microsoft.com/en-us/azure/databricks/opensharing/read-data-open |
| Access Databricks OpenSharing data as a recipient | https://learn.microsoft.com/en-us/azure/databricks/opensharing/recipient |
| Integrate SAP BDC with Azure Databricks via OpenSharing | https://learn.microsoft.com/en-us/azure/databricks/opensharing/sap-bdc/ |
| Create and manage SAP BDC connections for OpenSharing | https://learn.microsoft.com/en-us/azure/databricks/opensharing/sap-bdc/create-connection |
| Grant SAP BDC recipients access to OpenSharing shares | https://learn.microsoft.com/en-us/azure/databricks/opensharing/sap-bdc/share-to-sap |
| Access OpenSharing data via Iceberg REST Catalog clients | https://learn.microsoft.com/en-us/azure/databricks/opensharing/sharing-over-oidc-iceberg |
| Use M2M OIDC federation Python clients for OpenSharing | https://learn.microsoft.com/en-us/azure/databricks/opensharing/sharing-over-oidc-m2m |
| Use U2M OIDC federation to access OpenSharing data | https://learn.microsoft.com/en-us/azure/databricks/opensharing/sharing-over-oidc-u2m |
| Convert between PySpark and pandas DataFrames with Arrow | https://learn.microsoft.com/en-us/azure/databricks/pandas/pyspark-pandas-conversion |
| Connect Databricks to ingestion partners via Partner Connect | https://learn.microsoft.com/en-us/azure/databricks/partner-connect/ingestion |
| Connect Databricks to ML partners via Partner Connect | https://learn.microsoft.com/en-us/azure/databricks/partner-connect/ml |
| Connect Databricks to data prep partners via Partner Connect | https://learn.microsoft.com/en-us/azure/databricks/partner-connect/prep |
| Walkthrough: Connect Fivetran to Databricks via Partner Connect | https://learn.microsoft.com/en-us/azure/databricks/partner-connect/walkthrough-fivetran |
| Access Unity Catalog data from Microsoft Fabric via OneLake | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/fabric-mirror |
| Publish Unity Catalog to Microsoft Fabric mirrored tables | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/fabric-publish |
| Connect Databricks SQL warehouses to Hex | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/hex |
| Configure Looker integration with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/looker |
| Connect Looker Studio to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/looker-studio |
| Connect MicroStrategy Workstation to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/microstrategy |
| Connect Mode analytics to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/mode |
| Connect Power BI Desktop to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/power-bi-desktop |
| Publish Azure Databricks data to Power BI service | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/power-bi-service |
| Configure Unity Catalog connection for Power BI orchestration | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/power-bi-uc-connect |
| Integrate Preset BI with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/preset |
| Connect Qlik Sense to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/qlik-sense |
| Connect Sigma BI to Databricks SQL warehouses | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/sigma |
| Connect Tableau Desktop and Cloud to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/tableau |
| Connect ThoughtSpot to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/bi/thoughtspot |
| Connect Anomalo data quality to Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/data-governance/anomalo |
| Connect erwin Data Modeler to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/data-governance/erwin |
| Integrate Lightup data quality with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/data-governance/lightup |
| Connect Monte Carlo observability to Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/data-governance/monte-carlo |
| Connect Precisely Data Integrity Suite to Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/data-governance/precisely |
| Connect Privacera security platform to Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/data-security/privacera |
| Integrate Azure Databricks with Fivetran for data ingestion | https://learn.microsoft.com/en-us/azure/databricks/partners/ingestion/fivetran |
| Integrate Hevo Data pipelines with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/ingestion/hevo |
| Connect Informatica Cloud Data Integration to Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/ingestion/informatica-cloud-data-integration |
| Integrate Qlik Replicate with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/ingestion/qlik |
| Connect Rivery to Databricks SQL warehouses | https://learn.microsoft.com/en-us/azure/databricks/partners/ingestion/rivery |
| Integrate RudderStack with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/ingestion/rudderstack |
| Connect Snowplow behavioral data to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/ingestion/snowplow |
| Integrate StreamSets pipelines with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/ingestion/streamsets |
| Integrate Azure Databricks clusters with Dataiku | https://learn.microsoft.com/en-us/azure/databricks/partners/ml/dataiku |
| Set up John Snow Labs on Databricks clusters | https://learn.microsoft.com/en-us/azure/databricks/partners/ml/john-snow-labs |
| Integrate Azure Databricks ML clusters with Labelbox | https://learn.microsoft.com/en-us/azure/databricks/partners/ml/labelbox |
| Use SuperAnnotate Python SDK with Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/ml/superannotate |
| Connect dbt Cloud to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/prep/dbt-cloud |
| Integrate Matillion Data Productivity Cloud with Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/prep/matillion |
| Connect Prophecy low-code platform to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/prep/prophecy |
| Connect Census reverse ETL to Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/reverse-etl/census |
| Connect Hightouch reverse ETL to Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/reverse-etl/hightouch |
| Connect AtScale semantic layer to Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/semantic-layer/atscale |
| Integrate Stardog semantic layer with Databricks | https://learn.microsoft.com/en-us/azure/databricks/partners/semantic-layer/stardog |
| Implement PySpark custom data sources on Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/datasources |
| Use PySpark Catalog API on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog |
| Cache tables with PySpark Catalog.cacheTable | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/cachetable |
| Clear cached tables with PySpark Catalog.clearCache | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/clearcache |
| Create tables using PySpark Catalog.createTable | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/createtable |
| Get current catalog with PySpark Catalog.currentCatalog | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/currentcatalog |
| Get current database with PySpark Catalog.currentDatabase | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/currentdatabase |
| Check database existence with PySpark Catalog.databaseExists | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/databaseexists |
| Drop global temp views with PySpark Catalog.dropGlobalTempView | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/dropglobaltempview |
| Drop temp views with PySpark Catalog.dropTempView | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/droptempview |
| Check function existence with PySpark Catalog.functionExists | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/functionexists |
| Get databases with PySpark Catalog.getDatabase | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/getdatabase |
| Get functions with PySpark Catalog.getFunction | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/getfunction |
| Get tables and views with PySpark Catalog.getTable | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/gettable |
| List catalogs with PySpark Catalog.listCatalogs | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/listcatalogs |
| List table columns with PySpark Catalog.listColumns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/listcolumns |
| List databases with PySpark Catalog.listDatabases | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/listdatabases |
| List functions with PySpark Catalog.listFunctions | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/listfunctions |
| List tables and views with PySpark Catalog.listTables | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/listtables |
| Recover table partitions with PySpark Catalog.recoverPartitions | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/recoverpartitions |
| Refresh cached data by path with PySpark Catalog.refreshByPath | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/refreshbypath |
| Refresh cached tables with PySpark Catalog.refreshTable | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/refreshtable |
| Set current catalog with PySpark Catalog.setCurrentCatalog | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/setcurrentcatalog |
| Set current database with PySpark Catalog.setCurrentDatabase | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/setcurrentdatabase |
| Check table existence with PySpark Catalog.tableExists | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/tableexists |
| Uncache tables with PySpark Catalog.uncacheTable | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/catalog/uncachetable |
| Use PySpark Column class in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column |
| Alias PySpark DataFrame columns in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/alias |
| Sort PySpark columns ascending in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/asc |
| Sort ascending with nulls first in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/asc_nulls_first |
| Sort ascending with nulls last in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/asc_nulls_last |
| Cast PySpark columns using astype in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/astype |
| Filter PySpark columns between bounds in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/between |
| Use bitwise AND on PySpark columns in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/bitwiseand |
| Use bitwise OR on PySpark columns in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/bitwiseor |
| Use bitwise XOR on PySpark columns in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/bitwisexor |
| Cast PySpark columns to new data types in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/cast |
| Check substring containment in PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/contains |
| Sort PySpark columns descending in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/desc |
| Sort descending with nulls first in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/desc_nulls_first |
| Sort descending with nulls last in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/desc_nulls_last |
| Remove struct fields from PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/dropfields |
| Check string suffix in PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/endswith |
| Use null-safe equality on PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/eqnullsafe |
| Access struct fields from PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/getfield |
| Access array or map items from PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/getitem |
| Use case-insensitive LIKE on PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/ilike |
| Check membership of values in PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/isin |
| Detect NaN values in PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/isnan |
| Check non-null values in PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/isnotnull |
| Check null values in PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/isnull |
| Use SQL LIKE pattern matching in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/like |
| Alias PySpark columns using name in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/name |
| Specify default values with Column.otherwise | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/otherwise |
| Apply window specifications to PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/over |
| Use regex RLIKE pattern matching in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/rlike |
| Check string prefixes in PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/startswith |
| Extract substrings from PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/substr |
| Safely cast PySpark columns with try_cast | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/try_cast |
| Use conditional expressions with Column.when | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/when |
| Add or replace struct fields in PySpark columns | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/column/withfield |
| Use PySpark DataFrame class in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframe |
| Aggregate entire PySpark DataFrames in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframe/agg |
| Assign aliases to PySpark DataFrames in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframe/alias |
| Compute approximate quantiles on PySpark DataFrames | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframe/approxquantile |
| Use DataFrames as table arguments in Databricks TVFs | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframe/astable |
| Use DataFrame.persist storage levels in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframe/persist |
| Load Excel files into PySpark DataFrames in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/excel |
| Specify input data source formats with DataFrameReader | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/format |
| Read JDBC tables into DataFrames on Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/jdbc |
| Load JSON and JSON Lines into PySpark DataFrames | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/json |
| Load data sources into DataFrames with DataFrameReader.load | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/load |
| Load ORC files into PySpark DataFrames | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/orc |
| Load Parquet files into PySpark DataFrames | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/parquet |
| Read Databricks tables as DataFrames with DataFrameReader.table | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/table |
| Load UTF-8 text files into PySpark DataFrames | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/text |
| Load XML files into PySpark DataFrames on Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframereader/xml |
| Write DataFrames to external storage with DataFrameWriter | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter |
| Write DataFrames as CSV files in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/csv |
| Write DataFrames as Excel files in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/excel |
| Specify output data source formats with DataFrameWriter.format | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/format |
| Insert DataFrame rows into existing tables with insertInto | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/insertinto |
| Write DataFrames to JDBC tables from Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/jdbc |
| Write DataFrames as JSON/JSON Lines files | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/json |
| Write DataFrames as ORC files in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/orc |
| Write DataFrames as Parquet files in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/parquet |
| Save DataFrames to configured data sources with DataFrameWriter.save | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/save |
| Save DataFrames as Databricks tables with saveAsTable | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/saveastable |
| Write DataFrames as UTF-8 text files | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/text |
| Write DataFrames as XML files in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriter/xml |
| Write DataFrames with the v2 writer API in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriterv2 |
| Append DataFrame rows to tables with DataFrameWriterV2.append | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriterv2/append |
| Cluster data columns for query performance | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriterv2/clusterby |
| Set write options for PySpark data sources | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriterv2/option |
| Configure multiple write options in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriterv2/options |
| Partition output tables with DataFrameWriterV2 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriterv2/partitionedby |
| Add table properties with DataFrameWriterV2 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriterv2/tableproperty |
| Specify output data source provider in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/dataframewriterv2/using |
| Implement custom PySpark data sources | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasource |
| Define custom data source format name | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasource/name |
| Create DataSourceReader for custom reads | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasource/reader |
| Provide schema for custom data sources | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasource/schema |
| Implement simple streaming reader for data source | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasource/simplestreamreader |
| Create streaming reader for custom data source | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasource/streamreader |
| Create streaming writer for custom sinks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasource/streamwriter |
| Create batch writer for custom data source | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasource/writer |
| Implement Arrow-based data source writer | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcearrowwriter |
| Write Arrow RecordBatches to custom sink | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcearrowwriter/write |
| Implement DataSourceReader for custom inputs | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcereader |
| Partition custom data source reads | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcereader/partitions |
| Implement filter pushdown in DataSourceReader | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcereader/pushfilters |
| Read partition data in custom DataSourceReader | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcereader/read |
| Register custom data sources in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourceregistration |
| Register Python user-defined data source | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourceregistration/register |
| Implement Arrow-based streaming data writer | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamarrowwriter |
| Write Arrow batches to streaming sink | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamarrowwriter/write |
| Implement streaming reader for custom source | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader |
| Handle commit offsets in streaming reader | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader/commit |
| Configure default read limits for streaming | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader/getdefaultreadlimit |
| Define initial offset for streaming source | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader/initialoffset |
| Compute latest offset with read limits | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader/latestoffset |
| Partition streaming reads into input splits | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader/partitions |
| Read partition data in streaming reader | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader/read |
| Report latest offset for streaming status | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader/reportlatestoffset |
| Stop streaming reader and release resources | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamreader/stop |
| Implement streaming data sink writer | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamwriter |
| Abort streaming microbatch on failures | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamwriter/abort |
| Commit streaming microbatch with messages | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamwriter/commit |
| Write streaming data and return commit info | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcestreamwriter/write |
| Implement batch writer for custom sink | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcewriter |
| Abort batch write job on task failures | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcewriter/abort |
| Commit batch write job with messages | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcewriter/commit |
| Implement custom PySpark DataSourceWriter.write logic | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datasourcewriter/write |
| Use DataStreamReader to load streaming data | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader |
| Read CDC changes with DataStreamReader.changes | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/changes |
| Stream CSV files with DataStreamReader.csv | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/csv |
| Stream Excel files with DataStreamReader.excel | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/excel |
| Specify streaming input formats with DataStreamReader | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/format |
| Stream JSON data with DataStreamReader.json | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/json |
| Load streaming sources with DataStreamReader.load | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/load |
| Name streaming sources for checkpoint evolution | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/name |
| Configure streaming input options with DataStreamReader.option | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/option |
| Set multiple streaming options with DataStreamReader.options | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/options |
| Stream ORC files with DataStreamReader.orc | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/orc |
| Stream Parquet files with DataStreamReader.parquet | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/parquet |
| Define streaming input schemas with DataStreamReader.schema | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/schema |
| Create streaming DataFrames from tables | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/table |
| Stream text files with DataStreamReader.text | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/text |
| Stream XML files with DataStreamReader.xml | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamreader/xml |
| Write streaming DataFrames with DataStreamWriter | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter |
| Cluster streaming output with DataStreamWriter.clusterBy | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/clusterby |
| Process streaming rows with DataStreamWriter.foreach | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/foreach |
| Use foreachBatch for micro-batch streaming output | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/foreachbatch |
| Specify streaming sink formats with DataStreamWriter.format | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/format |
| Configure streaming sink options with DataStreamWriter.option | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/option |
| Set multiple streaming sink options with DataStreamWriter.options | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/options |
| Configure streaming output modes with DataStreamWriter.outputMode | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/outputmode |
| Partition streaming output with DataStreamWriter.partitionBy | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/partitionby |
| Name streaming queries with DataStreamWriter.queryName | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/queryname |
| Start streaming queries with DataStreamWriter.start | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/start |
| Write streaming results to tables with table() | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/table |
| Stream DataFrame output to tables with toTable | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/datastreamwriter/totable |
| Work with Geography values in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/geography |
| Create Geography objects from WKB | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/geography/fromwkb |
| Get WKB bytes from Geography objects | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/geography/getbytes |
| Retrieve SRID from Geography values | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/geography/getsrid |
| Work with Geometry values in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/geometry |
| Create Geometry objects from WKB | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/geometry/fromwkb |
| Get WKB bytes from Geometry objects | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/geometry/getbytes |
| Retrieve SRID from Geometry values | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/geometry/getsrid |
| Perform grouped aggregations with GroupedData | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata |
| Use GroupedData.agg for PySpark aggregations in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata/agg |
| Compute grouped averages with GroupedData.avg in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata/avg |
| Count records per group with GroupedData.count | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata/count |
| Find grouped maximums with GroupedData.max in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata/max |
| Compute grouped means with GroupedData.mean in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata/mean |
| Find grouped minimums with GroupedData.min in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata/min |
| Pivot DataFrame columns with GroupedData.pivot in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata/pivot |
| Compute grouped sums with GroupedData.sum in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/groupeddata/sum |
| Implement custom InputPartition for PySpark data sources | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/inputpartition |
| Capture DataFrame metrics with Observation in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/observation |
| Retrieve observed metrics with Observation.get in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/observation/get |
| Generate plots from DataFrames with PySparkPlotAccessor | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor |
| Draw stacked area plots with PySparkPlotAccessor.area | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/area |
| Create vertical bar charts with PySparkPlotAccessor.bar | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/bar |
| Create horizontal bar charts with PySparkPlotAccessor.barh | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/barh |
| Build box-and-whisker plots with PySparkPlotAccessor.box | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/box |
| Plot histograms of DataFrame columns with PySparkPlotAccessor.hist | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/hist |
| Generate KDE plots with PySparkPlotAccessor.kde | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/kde |
| Plot DataFrames as line charts with PySparkPlotAccessor.line | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/line |
| Create pie charts from DataFrames with PySparkPlotAccessor.pie | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/pie |
| Create scatter plots with PySparkPlotAccessor.scatter | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/plotaccessor/scatter |
| Work with Row objects in Databricks PySpark DataFrames | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/row |
| Convert Row objects to dictionaries with Row.asDict | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/row/asdict |
| Implement SimpleDataSourceStreamReader for lightweight streaming in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/simpledatasourcestreamreader |
| Commit processed offsets with SimpleDataSourceStreamReader.commit | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/simpledatasourcestreamreader/commit |
| Determine initial offsets with SimpleDataSourceStreamReader.initialOffset | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/simpledatasourcestreamreader/initialoffset |
| Read streaming batches with SimpleDataSourceStreamReader.read | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/simpledatasourcestreamreader/read |
| Re-read streaming data ranges with SimpleDataSourceStreamReader.readBetweenOffsets | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/simpledatasourcestreamreader/readbetweenoffsets |
| Use SparkSession as the entry point for Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession |
| Access the active SparkSession with SparkSession.active | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/active |
| Attach local artifacts to Spark sessions with SparkSession.addArtifacts | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/addartifacts |
| Tag and cancel related Spark operations with SparkSession.addTag | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/addtag |
| Manage catalogs, databases, and tables with SparkSession.catalog | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/catalog |
| Clear registered progress handlers with SparkSession.clearProgressHandlers | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/clearprogresshandlers |
| Create PySpark DataFrames from multiple data sources | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/createdataframe |
| Register custom data sources in SparkSession | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/datasource |
| Read data into DataFrames with DataFrameReader | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/read |
| Read streaming data with DataStreamReader | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/readstream |
| Execute SQL queries via SparkSession.sql in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/sql |
| Load Spark SQL tables as DataFrames | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/table |
| Call table-valued functions via SparkSession.tvf | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/tvf |
| Register and use UDFs with SparkSession.udf | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/udf |
| Register and use UDTFs with SparkSession.udtf | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/classes/sparksession/udtf |
| Use ai_classify PySpark function on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/ai_classify |
| Use ai_extract PySpark function on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/ai_extract |
| Use ai_parse_document PySpark function on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/ai_parse_document |
| Use ai_query to call Databricks model endpoints | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/ai_query |
| Create PyArrow-native UDTFs with arrow_udtf | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/arrow_udtf |
| Use from_utc_timestamp for timezone conversion in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/from_utc_timestamp |
| Parse XML strings to rows with from_xml in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/from_xml |
| Access array elements by index with get in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/get |
| Extract JSON objects with get_json_object in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/get_json_object |
| Read individual bits with getbit in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/getbit |
| Compute greatest column value with greatest in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/greatest |
| Identify aggregated columns with grouping in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/grouping |
| Compute grouping levels with grouping_id in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/grouping_id |
| Get H3 cell boundary as GeoJSON in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_boundaryasgeojson |
| Get H3 cell boundary as WKB in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_boundaryaswkb |
| Get H3 cell boundary as WKT in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_boundaryaswkt |
| Get H3 cell center as GeoJSON in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_centerasgeojson |
| Get H3 cell center as WKB in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_centeraswkb |
| Get H3 cell center as WKT in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_centeraswkt |
| Compact H3 cell ID sets with h3_compact in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_compact |
| Cover geography with H3 cells using h3_coverash3 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_coverash3 |
| Cover geography with H3 strings using h3_coverash3string | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_coverash3string |
| Compute grid distance between H3 cells with h3_distance | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_distance |
| Convert H3 IDs to hex strings with h3_h3tostring | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_h3tostring |
| Generate H3 hexagonal rings with h3_hexring in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_hexring |
| Check H3 parent-child relationships with h3_ischildof | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_ischildof |
| Detect H3 pentagon cells with h3_ispentagon | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_ispentagon |
| Validate H3 cell IDs with h3_isvalid in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_isvalid |
| Find H3 neighbors within distance k using h3_kring | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_kring |
| Get H3 neighbors and distances with h3_kringdistances | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_kringdistances |
| Convert longitude and latitude to H3 IDs with h3_longlatash3 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_longlatash3 |
| Convert longitude and latitude to H3 strings with h3_longlatash3string | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_longlatash3string |
| Get maximum child H3 cell with h3_maxchild in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_maxchild |
| Get minimum child H3 cell with h3_minchild in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_minchild |
| Convert point geometries to H3 IDs with h3_pointash3 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_pointash3 |
| Convert point geometries to H3 strings with h3_pointash3string | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_pointash3string |
| Fill polygons with H3 IDs using h3_polyfillash3 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_polyfillash3 |
| Fill polygons with H3 strings using h3_polyfillash3string | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_polyfillash3string |
| Get H3 cell resolution with h3_resolution in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_resolution |
| Convert H3 strings to big integers with h3_stringtoh3 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_stringtoh3 |
| Tessellate geography into H3 chips with h3_tessellateaswkb | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_tessellateaswkb |
| Get H3 children at resolution with h3_tochildren in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_tochildren |
| Get H3 parent at resolution with h3_toparent in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_toparent |
| Try covering geography with H3 IDs using h3_try_coverash3 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_try_coverash3 |
| Try covering geography with H3 strings using h3_try_coverash3string | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/h3_try_coverash3string |
| Use st_collect spatial function in Azure Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_collect |
| Parse EWKT geography with st_geogfromewkt | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_geogfromewkt |
| Parse GeoJSON geography with st_geogfromgeojson | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_geogfromgeojson |
| Parse WKT geography with st_geogfromtext | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_geogfromtext |
| Parse WKB geography with st_geogfromwkb | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_geogfromwkb |
| Parse WKT geography with st_geogfromwkt | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_geogfromwkt |
| Use st_m PySpark function for point M coordinate | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_m |
| Create bounding boxes with st_makeenvelope in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_makeenvelope |
| Build linestrings from geometries using st_makeline | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_makeline |
| Construct point geometries with st_makepoint in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_makepoint |
| Create polygons from linestrings using st_makepolygon | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_makepolygon |
| Convert geometries to multi types with st_multi | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_multi |
| Get coordinate dimension with st_ndims in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_ndims |
| Count points in geometries using st_npoints | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_npoints |
| Count polygon rings with st_nrings in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_nrings |
| Get geometry count with st_numgeometries in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_numgeometries |
| Get interior ring count using st_numinteriorrings | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_numinteriorrings |
| Count non-empty points with st_numpoints in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_numpoints |
| Calculate geometry perimeter with st_perimeter in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_perimeter |
| Create SRID-aware points with st_point in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_point |
| Generate point from geohash using st_pointfromgeohash | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_pointfromgeohash |
| Access nth linestring point with st_pointn in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_pointn |
| Remove nth linestring point using st_removepoint | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_removepoint |
| Reverse vertex order with st_reverse in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_reverse |
| Rotate geometries around Z axis with st_rotate | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_rotate |
| Scale geometries in PySpark using st_scale | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_scale |
| Set nth linestring point with st_setpoint in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_setpoint |
| Change geometry SRID using st_setsrid in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_setsrid |
| Simplify geometries with st_simplify in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_simplify |
| Retrieve SRID from geospatial values using st_srid | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_srid |
| Get first linestring point with st_startpoint in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_startpoint |
| Test geometry adjacency with st_touches in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_touches |
| Transform geometry CRS with st_transform in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_transform |
| Translate geometries using st_translate in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_translate |
| Compute geometry union with st_union in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_union |
| Aggregate geometry unions with st_union_agg in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_union_agg |
| Check containment relationships with st_within in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_within |
| Get X coordinate from point using st_x in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_x |
| Get maximum X coordinate with st_xmax in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_xmax |
| Get minimum X coordinate with st_xmin in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_xmin |
| Get Y coordinate from point using st_y in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_y |
| Get maximum Y coordinate with st_ymax in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_ymax |
| Get minimum Y coordinate with st_ymin in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_ymin |
| Get Z coordinate from point using st_z in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_z |
| Get maximum Z coordinate with st_zmax in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/st_zmax |
| Transform columns into rows with stack in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/stack |
| Check string prefixes with startswith in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/startswith |
| Use std aggregate alias in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/std |
| Use stddev alias for stddev_samp in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/stddev |
| Compute population standard deviation with stddev_pop | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/stddev_pop |
| Compute sample standard deviation with stddev_samp | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/stddev_samp |
| Convert delimited strings to maps with str_to_map | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/str_to_map |
| Concatenate values with string_agg in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/string_agg |
| Concatenate distinct values with string_agg_distinct | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/string_agg_distinct |
| Create struct columns with struct in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/struct |
| Extract substrings with substr in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/substr |
| Extract substrings with substring in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/substring |
| Split strings by delimiter with substring_index | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/substring_index |
| Aggregate numeric values with sum in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/sum |
| Aggregate distinct values with sum_distinct in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/sum_distinct |
| Compute tangent with tan in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/tan |
| Compute hyperbolic tangent with tanh in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/tanh |
| Compute Theta Sketch set difference with theta_difference | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/theta_difference |
| Compute Theta Sketch intersection with theta_intersection | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/theta_intersection |
| Aggregate Theta Sketch intersections with theta_intersection_agg | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/theta_intersection_agg |
| Build Theta Sketch aggregates with theta_sketch_agg | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/theta_sketch_agg |
| Estimate unique counts from Theta Sketch with theta_sketch_estimate | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/theta_sketch_estimate |
| Merge Theta Sketches with theta_union in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/theta_union |
| Aggregate Theta Sketch unions with theta_union_agg | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/theta_union_agg |
| Calculate time differences with time_diff in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/time_diff |
| Create TIME values from microseconds with time_from_micros | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/time_from_micros |
| Create TIME values from milliseconds with time_from_millis | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/time_from_millis |
| Use to_avro with Databricks Schema Registry | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/to_avro |
| Use to_geometry PySpark function in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/to_geometry |
| Use try_ip_as_string PySpark function in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_ip_as_string |
| Use try_ip_cidr PySpark function in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_ip_cidr |
| Use try_ip_host PySpark function in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_ip_host |
| Handle intervals with try_make_interval in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_make_interval |
| Create timestamps with try_make_timestamp in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_make_timestamp |
| Create LTZ timestamps with try_make_timestamp_ltz | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_make_timestamp_ltz |
| Create NTZ timestamps with try_make_timestamp_ntz | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_make_timestamp_ntz |
| Use try_mod for safe modulo in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_mod |
| Use try_multiply for overflow-safe multiplication | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_multiply |
| Parse JSON safely with try_parse_json in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_parse_json |
| Use try_parse_url for robust URL parsing | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_parse_url |
| Invoke Java methods safely with try_reflect | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_reflect |
| Use try_subtract for overflow-safe subtraction | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_subtract |
| Aggregate with overflow-safe try_sum in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_sum |
| Convert data safely with try_to_binary in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_to_binary |
| Convert values to dates with try_to_date | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_to_date |
| Parse spatial data with try_to_geography in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_to_geography |
| Convert formatted strings to numbers with try_to_number | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_to_number |
| Convert columns to TimeType with try_to_time | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_to_time |
| Parse timestamps safely with try_to_timestamp | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_to_timestamp |
| Decode URLs safely with try_url_decode in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_url_decode |
| Validate UTF-8 strings with try_validate_utf8 | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_validate_utf8 |
| Extract and cast sub-variants with try_variant_get | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_variant_get |
| Decompress Zstandard data with try_zstd_decompress | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/try_zstd_decompress |
| Use TableValuedFunction.stack in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/tvf-stack |
| Explode variant arrays/objects with variant_explode | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/tvf-variant_explode |
| Outer explode of variants with variant_explode_outer | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/tvf-variant_explode_outer |
| Inspect column data types with typeof in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/typeof |
| Uppercase strings with ucase in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/ucase |
| Create user-defined functions (UDFs) in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/udf |
| Create user-defined table functions (UDTFs) in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/udtf |
| Decode Base64 strings with unbase64 in PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/unbase64 |
| Convert hex strings to bytes with unhex in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/unhex |
| Generate uniform random values with uniform in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/uniform |
| Get days since epoch with unix_date in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/unix_date |
| Get microseconds since epoch with unix_micros | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/unix_micros |
| Get milliseconds since epoch with unix_millis | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/unix_millis |
| Get seconds since epoch with unix_seconds | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/unix_seconds |
| Convert time strings to Unix timestamps with unix_timestamp | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/unix_timestamp |
| Unwrap UDT columns with unwrap_udt in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/unwrap_udt |
| Uppercase strings with upper in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/upper |
| Decode URL-encoded strings with url_decode in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/url_decode |
| Use url_encode PySpark function in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/url_encode |
| Use user PySpark function in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/user |
| Generate UUIDs with Databricks PySpark uuid function | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/uuid |
| Validate UTF-8 strings with Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/validate_utf8 |
| Compute population variance with var_pop in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/var_pop |
| Compute sample variance with var_samp in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/var_samp |
| Use variance alias for var_samp in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/variance |
| Extract sub-variants with variant_get in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/variant_get |
| Use vector_avg PySpark function in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/vector_avg |
| Use vector_cosine_similarity in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/vector_cosine_similarity |
| Use vector_inner_product in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/vector_inner_product |
| Use vector_l2_distance in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/vector_l2_distance |
| Use vector_norm function in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/vector_norm |
| Use vector_normalize in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/vector_normalize |
| Use vector_sum PySpark function in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/vector_sum |
| Get Spark version with Databricks PySpark version function | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/version |
| Determine weekday from dates in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/weekday |
| Get ISO week number with weekofyear in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/weekofyear |
| Use conditional expressions with when in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/when |
| Bucket numeric values with width_bucket in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/width_bucket |
| Create time windows with window function in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/window |
| Compute event time from window columns in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/window_time |
| Extract XML values with xpath in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath |
| Evaluate XML XPath to boolean in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath_boolean |
| Get double from XML XPath with xpath_double | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath_double |
| Get float from XML XPath with xpath_float | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath_float |
| Get int from XML XPath with xpath_int | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath_int |
| Get long from XML XPath with xpath_long | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath_long |
| Get numeric double from XML XPath with xpath_number | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath_number |
| Get short from XML XPath with xpath_short | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath_short |
| Extract text from XML with xpath_string in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xpath_string |
| Hash columns with xxhash64 in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/xxhash64 |
| Extract year from dates with year function in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/year |
| Partition data by years with years transform in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/years |
| Replace nulls with zero using zeroifnull in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/zeroifnull |
| Merge arrays element-wise with zip_with in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/zip_with |
| Compress data with zstd_compress in Databricks PySpark | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/zstd_compress |
| Decompress Zstandard data with zstd_decompress in Databricks | https://learn.microsoft.com/en-us/azure/databricks/pyspark/reference/functions/zstd_decompress |
| Configure Databricks Lakehouse Federation for BigQuery | https://learn.microsoft.com/en-us/azure/databricks/query-federation/bigquery |
| Create and use HTTP connections in Databricks | https://learn.microsoft.com/en-us/azure/databricks/query-federation/http |
| Configure Lakehouse Federation for MySQL in Databricks | https://learn.microsoft.com/en-us/azure/databricks/query-federation/mysql |
| Configure OneLake catalog federation for Databricks | https://learn.microsoft.com/en-us/azure/databricks/query-federation/onelake |
| Configure Lakehouse Federation for Oracle databases | https://learn.microsoft.com/en-us/azure/databricks/query-federation/oracle |
| Configure Lakehouse Federation for PostgreSQL in Databricks | https://learn.microsoft.com/en-us/azure/databricks/query-federation/postgresql |
| Configure Databricks federated queries to Amazon Redshift | https://learn.microsoft.com/en-us/azure/databricks/query-federation/redshift |
| Run remote_query against external databases in Databricks | https://learn.microsoft.com/en-us/azure/databricks/query-federation/remote-queries |
| Configure Databricks federation for Salesforce Data 360 | https://learn.microsoft.com/en-us/azure/databricks/query-federation/salesforce-data-cloud |
| Use Salesforce Data 360 file sharing connector | https://learn.microsoft.com/en-us/azure/databricks/query-federation/salesforce-data-cloud-file-sharing |
| Set up Snowflake OAuth federation in Databricks | https://learn.microsoft.com/en-us/azure/databricks/query-federation/snowflake |
| Set up Snowflake federation using basic auth | https://learn.microsoft.com/en-us/azure/databricks/query-federation/snowflake-basic-auth |
| Enable Snowflake catalog federation for Iceberg tables | https://learn.microsoft.com/en-us/azure/databricks/query-federation/snowflake-catalog-federation |
| Configure Snowflake federation with Microsoft Entra ID | https://learn.microsoft.com/en-us/azure/databricks/query-federation/snowflake-entra |
| Use OAuth access tokens for Snowflake federation | https://learn.microsoft.com/en-us/azure/databricks/query-federation/snowflake-oauth-access-token |
| Configure Snowflake federation using Okta OAuth | https://learn.microsoft.com/en-us/azure/databricks/query-federation/snowflake-okta |
| Configure Snowflake federation with PEM private keys | https://learn.microsoft.com/en-us/azure/databricks/query-federation/snowflake-pem |
| Configure Databricks federation to Microsoft SQL Server | https://learn.microsoft.com/en-us/azure/databricks/query-federation/sql-server |
| Configure Lakehouse Federation for Azure Synapse | https://learn.microsoft.com/en-us/azure/databricks/query-federation/sqldw |
| Configure Lakehouse Federation for Teradata in Databricks | https://learn.microsoft.com/en-us/azure/databricks/query-federation/teradata |
| Use Azure Databricks to read and write Avro data | https://learn.microsoft.com/en-us/azure/databricks/query/formats/avro |
| Load binary file data into Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/query/formats/binary |
| Read and write CSV files in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/query/formats/csv |
| Read and stream Excel files with Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/query/formats/excel |
| Ingest image files using Azure Databricks image source | https://learn.microsoft.com/en-us/azure/databricks/query/formats/image |
| Read and write JSON data in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/query/formats/json |
| Load MLflow experiment runs into Spark DataFrames | https://learn.microsoft.com/en-us/azure/databricks/query/formats/mlflow-experiment |
| Query OpenSharing shared tables with Spark DataFrames | https://learn.microsoft.com/en-us/azure/databricks/query/formats/opensharing |
| Read and write ORC files in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/query/formats/orc |
| Use Azure Databricks to process Parquet data | https://learn.microsoft.com/en-us/azure/databricks/query/formats/parquet |
| Read and write text files using Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/query/formats/text |
| Read and write XML data in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/query/formats/xml |
| Use MLflow REST APIs on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/reference/mlflow-api |
| Use Account SCIM v2.1 API for identity management | https://learn.microsoft.com/en-us/azure/databricks/reference/scim-2-1 |
| Query and extract JSON string fields in Azure Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/semi-structured/json |
| Query VARIANT semi-structured data in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/semi-structured/variant |
| Reference Spark reader and writer options on Databricks | https://learn.microsoft.com/en-us/azure/databricks/spark/api-options |
| Use SparkR, sparklyr, and dplyr DataFrames on Databricks | https://learn.microsoft.com/en-us/azure/databricks/sparkr/dataframes-tables |
| Connect local RStudio to Azure Databricks compute | https://learn.microsoft.com/en-us/azure/databricks/sparkr/rstudio |
| Run Shiny applications on Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/sparkr/shiny |
| Migrate SparkR code to sparklyr on Databricks | https://learn.microsoft.com/en-us/azure/databricks/sparkr/sparkr-migration |
| Migrate to the latest Databricks SQL REST API version | https://learn.microsoft.com/en-us/azure/databricks/sql/dbsql-api-latest |
| Use Databricks SQL language constructs and syntax | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/ |
| Control flow with CASE statement in Databricks SQL scripts | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/case-stmt |
| Close cursors with CLOSE statement in Databricks SQL scripts | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/close-stmt |
| Fetch cursor rows with FETCH statement in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/fetch-stmt |
| Iterate query results with FOR statement in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/for-stmt |
| Use GET DIAGNOSTICS in Databricks SQL procedures | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/get-diagnostics-stmt |
| Control flow with IF THEN ELSE in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/if-stmt |
| Use ITERATE to control Databricks SQL loops | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/iterate-stmt |
| Exit loops with LEAVE in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/leave-stmt |
| Create and manage LOOP blocks in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/loop-stmt |
| Open and use cursors with OPEN in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/open-stmt |
| Use REPEAT loops in Databricks SQL procedures | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/repeat-stmt |
| Re-raise exceptions with RESIGNAL in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/resignal-stmt |
| Raise custom conditions with SIGNAL in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/signal-stmt |
| Implement WHILE loops in Databricks SQL procedures | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/control-flow/while-stmt |
| Use GEOGRAPHY data type in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/data-types/geography-type |
| Use GEOMETRY data type in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/data-types/geometry-type |
| Clone Delta and Parquet tables with Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/delta-clone |
| Use ai_analyze_sentiment function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_analyze_sentiment |
| Classify text with ai_classify in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_classify |
| Extract structured data using ai_extract function | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_extract |
| Correct text grammar with ai_fix_grammar function | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_fix_grammar |
| Forecast time series with ai_forecast in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_forecast |
| Generate text with ai_gen in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_gen |
| Mask sensitive entities using ai_mask function | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_mask |
| Use ai_parse_document in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_parse_document |
| Use ai_prep_search for RAG in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_prep_search |
| Query model serving endpoints with ai_query | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_query |
| Compute semantic similarity using ai_similarity | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_similarity |
| Summarize text with ai_summarize in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_summarize |
| Translate text using ai_translate function | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ai_translate |
| Accumulate top-K sketches with approx_top_k_accumulate | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/approx_top_k_accumulate |
| Combine top-K sketches with approx_top_k_combine | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/approx_top_k_combine |
| Use array_contains in Databricks SQL expressions | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/array_contains |
| Use bitmap_and_agg for Databricks SQL bitmaps | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/bitmap_and_agg |
| Construct bitmap aggregates with bitmap_construct_agg | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/bitmap_construct_agg |
| Implement CASE expressions in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/case |
| Compute cube roots with cbrt in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/cbrt |
| Apply classifier() in MATCH_RECOGNIZE patterns | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/classifier |
| Use cloud_files_state TVF in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/cloud_files_state |
| Aggregate values into arrays with collect_list | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/collect_list |
| Extract JSON content with Databricks colon operator | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/colonsign |
| Use concat_ws string function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/concat_ws |
| Check substring presence with contains in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/contains |
| Convert number bases with conv in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/conv |
| Convert time zones with convert_timezone in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/convert_timezone |
| Compute Pearson correlation with corr in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/corr |
| Calculate cosine values with cos in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/cos |
| Use hyperbolic cosine via cosh in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/cosh |
| Compute cotangent with cot in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/cot |
| Use count aggregate function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/count |
| Use count_if aggregate in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/count_if |
| Generate count_min_sketch aggregates in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/count_min_sketch |
| Compute crc32 checksums in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/crc32 |
| Create aggregation cubes with cube in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/cube |
| Get current date with curdate in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/curdate |
| Retrieve current catalog with current_catalog in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/current_catalog |
| Retrieve current database/schema in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/current_database |
| Get current date with current_date in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/current_date |
| Retrieve current metastore ID in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/current_metastore |
| Retrieve current schema with current_schema in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/current_schema |
| Get current timestamp with current_timestamp in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/current_timestamp |
| Retrieve current session time zone in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/current_timezone |
| Cast expressions to date with date function in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/date |
| Add days to dates with date_add in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/date_add |
| Add time units with date_add (timestamp) in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/date_add3 |
| Compute timestamp differences with date_diff in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/date_diff |
| Format dates and timestamps with date_format in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/date_format |
| Convert Unix days to dates with date_from_unix_date in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/date_from_unix_date |
| Subtract days from dates with date_sub in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/date_sub |
| Truncate timestamps with date_trunc in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/date_trunc |
| Add time units with dateadd in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/dateadd |
| Add days to dates with dateadd (days) in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/dateadd2 |
| Use event_log TVF for Databricks streaming diagnostics | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/event_log |
| Apply first aggregate function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/first |
| Cast values to FLOAT with Databricks SQL float | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/float |
| Use from_avro to parse Avro in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/from_avro |
| Use from_csv function in Azure Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/from_csv |
| Parse JSON to structs with Databricks from_json | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/from_json |
| Use from_xml to parse XML in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/from_xml |
| Use h3_boundaryasgeojson in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_boundaryasgeojson |
| Use h3_boundaryaswkb in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_boundaryaswkb |
| Use h3_boundaryaswkt in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_boundaryaswkt |
| Get H3 cell center as GeoJSON in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_centerasgeojson |
| Get H3 cell center as WKB in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_centeraswkb |
| Get H3 cell center as WKT in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_centeraswkt |
| Compact H3 cell sets with Databricks h3_compact | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_compact |
| Cover geography with H3 cells using h3_coverash3 | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_coverash3 |
| Cover geography with H3 strings using h3_coverash3string | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_coverash3string |
| Compute H3 grid distance with h3_distance in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_distance |
| Convert H3 IDs to hex strings with h3_h3tostring | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_h3tostring |
| Generate H3 hexagonal rings with h3_hexring in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_hexring |
| Check H3 parent-child relationships with h3_ischildof | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_ischildof |
| Detect pentagon H3 cells with h3_ispentagon in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_ispentagon |
| Validate H3 cell IDs with h3_isvalid in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_isvalid |
| Get H3 k-ring neighborhoods with h3_kring in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_kring |
| Convert longitude/latitude to H3 BIGINT with h3_longlatash3 | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_longlatash3 |
| Convert longitude/latitude to H3 string with h3_longlatash3string | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_longlatash3string |
| Get maximum child H3 cell with h3_maxchild in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_maxchild |
| Get minimum child H3 cell with h3_minchild in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_minchild |
| Convert geometry point to H3 BIGINT with h3_pointash3 | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_pointash3 |
| Convert geometry point to H3 string with h3_pointash3string | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_pointash3string |
| Polyfill areal geography with H3 BIGINT using h3_polyfillash3 | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_polyfillash3 |
| Polyfill areal geography with H3 strings using h3_polyfillash3string | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_polyfillash3string |
| Get H3 cell resolution with h3_resolution in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_resolution |
| Convert H3 hex string to BIGINT with h3_stringtoh3 | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_stringtoh3 |
| Tessellate geography into H3 WKB cells with h3_tessellateaswkb | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_tessellateaswkb |
| List child H3 cells at resolution with h3_tochildren | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_tochildren |
| Get parent H3 cell at resolution with h3_toparent | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_toparent |
| Safely cover geography with H3 BIGINT using h3_try_coverash3 | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_try_coverash3 |
| Safely cover geography with H3 strings using h3_try_coverash3string | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/h3_try_coverash3string |
| Use Databricks SQL hex function for conversions | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/hex |
| Compute numeric histograms with Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/histogram_numeric |
| Build HLL sketch aggregates in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/hll_sketch_agg |
| Estimate unique counts from HLL sketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/hll_sketch_estimate |
| Union HyperLogLog sketches in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/hll_union |
| Use Databricks SQL http_request for external HTTP calls | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/http_request |
| Use Databricks SQL if conditional function | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/if |
| Use Databricks SQL iff conditional function | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/iff |
| Handle nulls with ifnull in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ifnull |
| Capitalize words with initcap in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/initcap |
| Explode struct arrays with inline in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/inline |
| Use inline_outer to explode arrays with outer semantics | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/inline_outer |
| Get input file block length in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/input_file_block_length |
| Get input file block start offset in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/input_file_block_start |
| Find substring positions with instr in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/instr |
| Cast expressions to int in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/int |
| Use ip_as_binary in Azure Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_as_binary |
| Use ip_as_string in Azure Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_as_string |
| Normalize CIDR blocks with ip_cidr in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_cidr |
| Check CIDR containment with ip_cidr_contains in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_cidr_contains |
| Use ip_host SQL function in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_host |
| Get network portion of CIDR with ip_network in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_network |
| Use ip_network_first alias for ip_network in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_network_first |
| Get last IP in CIDR with ip_network_last in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_network_last |
| Retrieve CIDR prefix length with ip_prefix_length in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_prefix_length |
| Determine IP version with ip_version in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ip_version |
| Call Java reflection methods from Databricks SQL with java_method | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/java_method |
| Use kll_merge_agg_bigint for KLL sketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_merge_agg_bigint |
| Use kll_merge_agg_double for KLL sketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_merge_agg_double |
| Use kll_merge_agg_float for KLL sketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_merge_agg_float |
| Use kll_sketch_agg_bigint in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_agg_bigint |
| Use kll_sketch_agg_double in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_agg_double |
| Use kll_sketch_agg_float in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_agg_float |
| Query item count from bigint KLL sketch | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_get_n_bigint |
| Query item count from double KLL sketch | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_get_n_double |
| Query item count from float KLL sketch | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_get_n_float |
| Use kll_sketch_get_rank_double in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_get_rank_double |
| Use kll_sketch_get_rank_float in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_get_rank_float |
| Merge bigint KLL sketches in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_merge_bigint |
| Merge double KLL sketches in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_merge_double |
| Merge float KLL sketches in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_merge_float |
| Convert bigint KLL sketch to debug string | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_to_string_bigint |
| Convert double KLL sketch to debug string | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_to_string_double |
| Convert float KLL sketch to debug string | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kll_sketch_to_string_float |
| Calculate kurtosis with Databricks SQL function | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/kurtosis |
| Use lag window function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/lag |
| Pattern matching with like in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/like |
| Use make_valid_utf8 in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/make_valid_utf8 |
| Create year-month intervals with make_ym_interval | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/make_ym_interval |
| Build map literals using Databricks SQL map | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map |
| Merge maps with map_concat in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_concat |
| Check map keys with map_contains_key | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_contains_key |
| Return map entries with map_entries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_entries |
| Filter map elements using map_filter | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_filter |
| Create maps from arrays with map_from_arrays | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_from_arrays |
| Build maps from entries using map_from_entries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_from_entries |
| Extract map keys with map_keys in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_keys |
| Extract map values with map_values in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_values |
| Merge maps with map_zip_with in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/map_zip_with |
| Mask sensitive strings using Databricks SQL mask | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/mask |
| Use match_number in Databricks SQL MATCH_RECOGNIZE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/match_number |
| Use first navigation function in MATCH_RECOGNIZE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/match_recognize_first |
| Use last navigation function in MATCH_RECOGNIZE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/match_recognize_last |
| Use next navigation function in MATCH_RECOGNIZE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/match_recognize_next |
| Use prev navigation function in MATCH_RECOGNIZE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/match_recognize_prev |
| Compute maximum values with Databricks SQL max | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/max |
| Generate MD5 checksums with Databricks SQL md5 | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/md5 |
| Calculate averages with mean aggregate function | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/mean |
| Use measure aggregate with Databricks metric views | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/measure |
| Compute minimum values with Databricks SQL min | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/min |
| Subtract values using Databricks SQL minus operator | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/minussign |
| Negate expressions with Databricks SQL unary minus | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/minussignunary |
| Compute remainders with mod in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/mod |
| Create named structs with Databricks SQL named_struct | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/named_struct |
| Negate numeric values using Databricks SQL negative | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/negative |
| Find next weekday dates with Databricks SQL next_day | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/next_day |
| Apply logical negation with Databricks SQL not | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/not |
| Get current timestamp using Databricks SQL now | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/now |
| Access window offsets with Databricks SQL nth_value | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/nth_value |
| Bucket window rows with Databricks SQL ntile | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/ntile |
| Return conditional nulls with Databricks SQL nullif | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/nullif |
| Convert zeros to nulls with Databricks SQL nullifzero | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/nullifzero |
| Provide default values with Databricks SQL nvl | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/nvl |
| Use parse_timestamp in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/parse_timestamp |
| Calculate exact percentiles in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/percentile |
| Use modulo % operator in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/percentsign |
| Compute positive modulo with pmod in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/pmod |
| Use pow function in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/pow |
| Use power function in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/power |
| Cast with ?:: operator in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/questiondoublecolonsign |
| Use radians function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/radians |
| Generate random numbers with rand in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/rand |
| Generate random numbers with random in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/random |
| Use read_files TVF to load files in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/read_files |
| Read Kafka topics with Databricks SQL read_kafka | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/read_kafka |
| Use read_kinesis to stream data into Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/read_kinesis |
| Stream Google Pub/Sub data with read_pubsub in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/read_pubsub |
| Use read_pulsar to stream Pulsar topics into Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/read_pulsar |
| Use read_state_metadata for streaming state inspection | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/read_state_metadata |
| Access streaming state with read_statestore in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/read_statestore |
| Aggregate arrays with reduce in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/reduce |
| Call Java methods with Databricks SQL reflect | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/reflect |
| Compute regression mean with regr_avgx in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/regr_avgx |
| Compute regression SXX with regr_sxx in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/regr_sxx |
| Compute regression SXY with regr_sxy in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/regr_sxy |
| Query remote databases with remote_query in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/remote_query |
| Use schema_of_csv in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/schema_of_csv |
| Use schema_of_json in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/schema_of_json |
| Infer JSON group schema with schema_of_json_agg | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/schema_of_json_agg |
| Get VARIANT column schema using schema_of_variant | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/schema_of_variant |
| Aggregate VARIANT schemas with schema_of_variant_agg | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/schema_of_variant_agg |
| Use schema_of_xml in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/schema_of_xml |
| Use Databricks search function with full-text indexes | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/search |
| Use second() timestamp function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/second |
| Split text into sentences with Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/sentences |
| Generate value sequences with Databricks SQL sequence() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/sequence |
| Create session windows with Databricks SQL session_window() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/session_window |
| Compute SHA1 hashes with Databricks SQL sha() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/sha |
| Compute SHA1 hashes with Databricks SQL sha1() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/sha1 |
| Compute SHA-2 checksums with Databricks SQL sha2() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/sha2 |
| Use shiftleft() bitwise operator in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/shiftleft |
| Use shiftright() signed bitwise operator in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/shiftright |
| Use shiftrightunsigned() bitwise operator in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/shiftrightunsigned |
| Randomize arrays with Databricks SQL shuffle() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/shuffle |
| Determine numeric sign with Databricks SQL sign() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/sign |
| Determine numeric sign with Databricks SQL signum() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/signum |
| Get array or map size with Databricks SQL size() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/size |
| Use division operator in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/slashsign |
| Extract array slices with Databricks SQL slice() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/slice |
| Cast values to SMALLINT with Databricks SQL smallint() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/smallint |
| Evaluate boolean aggregates with Databricks SQL some() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/some |
| Sort arrays with Databricks SQL sort_array() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/sort_array |
| Compute soundex codes with Databricks SQL soundex() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/soundex |
| Generate space-filled strings with Databricks SQL space() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/space |
| Get current partition ID with spark_partition_id() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/spark_partition |
| Split strings with Databricks SQL split() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/split |
| Extract string parts with Databricks SQL split_part() | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/split_part |
| Use st_addpoint for Databricks spatial linestrings | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_addpoint |
| Calculate geometry area with st_area in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_area |
| Convert geometries to WKB with st_asbinary | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_asbinary |
| Export geometries as EWKB using st_asewkb | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_asewkb |
| Return geometries as EWKT with st_asewkt | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_asewkt |
| Generate GeoJSON from geometries via st_asgeojson | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_asgeojson |
| Convert geometries to WKT with st_astext | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_astext |
| Output WKB from geometries using st_aswkb | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_aswkb |
| Return geometries as WKT with st_aswkt | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_aswkt |
| Compute azimuth between points with st_azimuth | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_azimuth |
| Get geometry boundaries using st_boundary | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_boundary |
| Create geometry buffers with st_buffer in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_buffer |
| Find geometry centroids using st_centroid | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_centroid |
| Project closest point on geometry via st_closestpoint | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_closestpoint |
| Compute concave hulls using st_concavehull | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_concavehull |
| Test geometry containment with st_contains | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_contains |
| Generate convex hulls via st_convexhull in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_convexhull |
| Check geometry coverage using st_covers | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_covers |
| Compute geometry differences with st_difference | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_difference |
| Get geometry topological dimension via st_dimension | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_dimension |
| Determine disjoint geometries with st_disjoint | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_disjoint |
| Measure 2D distances using st_distance in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_distance |
| Compute spherical distances with st_distancesphere | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_distancesphere |
| Calculate geodesic distances via st_distancespheroid | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_distancespheroid |
| Explode multi-geometries using st_dump in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_dump |
| Filter geometries within distance using st_dwithin | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_dwithin |
| Get linestring endpoints with st_endpoint | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_endpoint |
| Use st_envelope geometry function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_envelope |
| Aggregate geometry envelopes with st_envelope_agg | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_envelope_agg |
| Compare geometries with st_equals in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_equals |
| Estimate projected SRID with st_estimatesrid | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_estimatesrid |
| Extract polygon exterior ring with st_exteriorring | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_exteriorring |
| Swap geometry coordinates using st_flipcoordinates | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_flipcoordinates |
| Force 2D projection with st_force2d in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_force2d |
| Use st_geogfromewkt in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geogfromewkt |
| Parse GeoJSON geography with st_geogfromgeojson | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geogfromgeojson |
| Parse WKT geography with st_geogfromtext | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geogfromtext |
| Parse WKB geography with st_geogfromwkb | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geogfromwkb |
| Use st_geogfromwkt to parse WKT geography in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geogfromwkt |
| Generate geohash strings with st_geohash | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geohash |
| Access n-th geometry element with st_geometryn | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geometryn |
| Get geometry type string with st_geometrytype | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geometrytype |
| Create geometry from EWKB with st_geomfromewkb | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geomfromewkb |
| Create geometry from EWKT with st_geomfromewkt | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geomfromewkt |
| Convert geohash to geometry with st_geomfromgeohash | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geomfromgeohash |
| Create geometry from GeoJSON with st_geomfromgeojson | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geomfromgeojson |
| Create geometry from WKT with st_geomfromtext | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geomfromtext |
| Create geometry from WKB with st_geomfromwkb | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geomfromwkb |
| Create geometry from WKT with st_geomfromwkt | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_geomfromwkt |
| Access polygon interior rings with st_interiorringn | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_interiorringn |
| Compute geometry intersection with st_intersection | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_intersection |
| Test geometry intersection with st_intersects | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_intersects |
| Check for empty geometries with st_isempty | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_isempty |
| Validate geometries with st_isvalid in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_isvalid |
| Measure geometry length with st_length | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_length |
| Access M coordinate with st_m in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_m |
| Construct envelope geometries with st_makeenvelope | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_makeenvelope |
| Build linestrings from points with st_makeline | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_makeline |
| Create point geometries with st_makepoint | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_makepoint |
| Construct polygons from rings with st_makepolygon | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_makepolygon |
| Convert to multi-geometry with st_multi | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_multi |
| Get geometry coordinate dimension with st_ndims | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_ndims |
| Count points in geometries with st_npoints | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_npoints |
| Count polygon rings with st_nrings in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_nrings |
| Count component geometries with st_numgeometries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_numgeometries |
| Count polygon interior rings with st_numinteriorrings | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_numinteriorrings |
| Count points in geometries with st_numpoints | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_numpoints |
| Use st_perimeter in Databricks SQL geospatial queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_perimeter |
| Create point geometries with st_point in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_point |
| Convert geohash to point with st_pointfromgeohash | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_pointfromgeohash |
| Access n-th linestring point using st_pointn | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_pointn |
| Remove linestring point using st_removepoint in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_removepoint |
| Reverse geospatial geometries with st_reverse in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_reverse |
| Rotate geometries around Z axis using st_rotate | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_rotate |
| Scale geometries in Databricks SQL with st_scale | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_scale |
| Set linestring point coordinates using st_setpoint | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_setpoint |
| Assign SRID to geometries with st_setsrid in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_setsrid |
| Simplify geometries using st_simplify in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_simplify |
| Retrieve geometry SRID with st_srid in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_srid |
| Get first linestring point using st_startpoint | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_startpoint |
| Test geometry boundary contact with st_touches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_touches |
| Transform geometry CRS with st_transform in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_transform |
| Translate geometries with st_translate in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_translate |
| Compute geometry union with st_union in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_union |
| Aggregate geometry unions with st_union_agg in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_union_agg |
| Check geometry containment with st_within in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_within |
| Get X coordinate of point with st_x in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_x |
| Retrieve maximum X of geometry using st_xmax | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_xmax |
| Retrieve minimum X of geometry using st_xmin | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_xmin |
| Get Y coordinate of point with st_y in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_y |
| Retrieve maximum Y of geometry using st_ymax | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_ymax |
| Retrieve minimum Y of geometry using st_ymin | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_ymin |
| Get Z coordinate of point with st_z in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_z |
| Retrieve maximum Z of geometry using st_zmax | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_zmax |
| Retrieve minimum Z of geometry using st_zmin | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/st_zmin |
| Use stack table-valued generator in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/stack |
| Use startswith string function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/startswith |
| Use std aggregate function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/std |
| Use stddev aggregate function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/stddev |
| Use stddev_pop aggregate function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/stddev_pop |
| Use stddev_samp aggregate function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/stddev_samp |
| Create maps from strings with str_to_map | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/str_to_map |
| Cast expressions to STRING in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/string |
| Use string_agg aggregate function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/string_agg |
| Create structs with struct function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/struct |
| Use substr function for string slicing | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/substr |
| Use substring function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/substring |
| Extract substrings with substring_index in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/substring_index |
| Use sum aggregate function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/sum |
| Query Delta Lake change logs with table_changes | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/table_changes |
| Use tan trigonometric function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tan |
| Use tanh hyperbolic function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tanh |
| Compute theta_difference on Databricks Theta Sketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/theta_difference |
| Use theta_intersection with Databricks Theta Sketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/theta_intersection |
| Aggregate Theta Sketch intersections in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/theta_intersection_agg |
| Build Theta Sketch aggregates in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/theta_sketch_agg |
| Estimate unique counts from Theta Sketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/theta_sketch_estimate |
| Union Theta Sketches with Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/theta_union |
| Aggregate Theta Sketch unions across partitions | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/theta_union_agg |
| Use bitwise NOT (~) operator in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tildesign |
| Use time_diff in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/time_diff |
| Create TIME from microseconds in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/time_from_micros |
| Create TIME from milliseconds in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/time_from_millis |
| Create TIME from seconds in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/time_from_seconds |
| Get microseconds from TIME in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/time_to_micros |
| Get milliseconds from TIME in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/time_to_millis |
| Get seconds from TIME in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/time_to_seconds |
| Truncate TIME values in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/time_trunc |
| Format values as strings using to_char | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/to_char |
| Convert spatial data with to_geometry in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/to_geometry |
| Convert formatted strings to DECIMAL with to_number | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/to_number |
| Use Databricks SQL to_time function for time casting | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/to_time |
| Format values as VARCHAR using to_varchar | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/to_varchar |
| Convert complex types to VARIANT objects in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/to_variant_object |
| Compute averages safely with try_avg aggregate | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/try_avg |
| Use try_ip_as_binary in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/try_ip_as_binary |
| Use try_ip_as_string in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/try_ip_as_string |
| Use try_ip_cidr for CIDR handling in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/try_ip_cidr |
| Parse timestamps safely with try_parse_timestamp | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/try_parse_timestamp |
| Convert formatted strings to DECIMAL with try_to_number | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/try_to_number |
| Compute tuple_difference_double in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_difference_double |
| Compute tuple_difference_integer in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_difference_integer |
| Aggregate tuple_intersection_agg_double sketches in SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_intersection_agg_double |
| Aggregate tuple_intersection_agg_integer sketches in SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_intersection_agg_integer |
| Use tuple_intersection_double on TupleSketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_intersection_double |
| Use tuple_intersection_integer on TupleSketches | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_intersection_integer |
| Create TupleSketches with tuple_sketch_agg_double | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_sketch_agg_double |
| Create TupleSketches with tuple_sketch_agg_integer | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_sketch_agg_integer |
| Estimate unique keys with tuple_sketch_estimate_double | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_sketch_estimate_double |
| Estimate unique keys with tuple_sketch_estimate_integer | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_sketch_estimate_integer |
| Summarize TupleSketch doubles with tuple_sketch_summary_double | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_sketch_summary_double |
| Summarize TupleSketch integers with tuple_sketch_summary_integer | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_sketch_summary_integer |
| Union multiple TupleSketches with tuple_union_agg_double | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_union_agg_double |
| Union multiple TupleSketches with tuple_union_agg_integer | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_union_agg_integer |
| Merge two TupleSketches with tuple_union_double | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_union_double |
| Merge two TupleSketches with tuple_union_integer | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/tuple_union_integer |
| Use unbase64 in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/unbase64 |
| Convert hex to binary with unhex in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/unhex |
| Get days since epoch using unix_date in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/unix_date |
| Compute microsecond epoch with unix_micros in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/unix_micros |
| Compute millisecond epoch with unix_millis in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/unix_millis |
| Compute second epoch with unix_seconds in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/unix_seconds |
| Use unix_timestamp in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/unix_timestamp |
| Uppercase strings with upper in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/upper |
| Decode URL-encoded strings with url_decode in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/url_decode |
| Encode strings as URLs with url_encode in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/url_encode |
| Get executing user with user function in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/user |
| Validate UTF-8 strings with validate_utf8 in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/validate_utf8 |
| Explode VARIANT data with variant_explode in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/variant_explode |
| Outer explode VARIANT data with variant_explode_outer | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/variant_explode_outer |
| Extract values from VARIANT with variant_get in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/variant_get |
| Compute element-wise vector averages with vector_avg in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/vector_avg |
| Calculate vector norms with vector_norm in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/vector_norm |
| Normalize vectors with vector_normalize in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/vector_normalize |
| Use vector_search SQL function with Azure AI Search | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/vector_search |
| Compute element-wise vector sums with vector_sum in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/vector_sum |
| Get week of year with weekofyear in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/weekofyear |
| Bucket numeric values with width_bucket in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/width_bucket |
| Define sliding windows with window grouping in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/window |
| Get window end time with window_time in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/window_time |
| Query XML nodes with xpath in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/xpath |
| Evaluate XML XPath booleans with xpath_boolean in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/xpath_boolean |
| Extract integers from XML with xpath_int in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/xpath_int |
| Extract BIGINT values from XML with xpath_long in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/xpath_long |
| Use xpath_short to extract SMALLINT from XML | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/xpath_short |
| Use xpath_string to extract text from XML | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/xpath_string |
| Compute 64-bit hashes with xxhash64 in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/xxhash64 |
| Use zeroifnull to handle NULL values in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/zeroifnull |
| Merge arrays with zip_with in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/zip_with |
| Compress data with zstd_compress in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/zstd_compress |
| Decompress data with zstd_decompress in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/functions/zstd_decompress |
| Run federated queries across external databases in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-federated-queries |
| Implement Databricks SQL user-defined aggregate functions | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-functions-udf-aggregate |
| Integrate Hive UDFs and UDAFs with Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-functions-udf-hive |
| Create and register Databricks SQL scalar UDFs | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-functions-udf-scalar |
| Use JSON path expressions on JSON and VARIANT in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-json-path-expression |
| Download volume files with Databricks GET | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-aux-connector-get |
| Upload local files with Databricks PUT INTO | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-aux-connector-put-into |
| Remove volume files with Databricks REMOVE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-aux-connector-remove |
| Use DESCRIBE TABLE metadata in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-aux-describe-table |
| Execute dynamic SQL with EXECUTE IMMEDIATE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-aux-execute-immediate |
| Retrieve CREATE TABLE statements in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-aux-show-create-table |
| List views with SHOW VIEWS in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-aux-show-views |
| Add comments and hints in Databricks SQL statements | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-comment |
| Use DROP CONNECTION for Unity Catalog foreign catalogs | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-ddl-alter-catalog-drop-connection |
| Alter materialized views in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-ddl-alter-materialized-view |
| Modify Databricks SQL streaming tables with ALTER | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-ddl-alter-streaming-table |
| Alter table schema and properties in Databricks | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-ddl-alter-table |
| Use ALTER VIEW to change Databricks view metadata | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-ddl-alter-view |
| Convert foreign views to managed views in Unity Catalog | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-ddl-alter-view-set-managed |
| Use CREATE TABLE LIKE in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-ddl-create-table-like |
| Use MATCH_RECOGNIZE for row pattern queries in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-qry-select-match-recognize |
| Define boolean pattern variables in MATCH_RECOGNIZE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-qry-select-match-recognize-define |
| Specify MEASURES output columns in MATCH_RECOGNIZE | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-qry-select-match-recognize-measures |
| Define PATTERN clause for MATCH_RECOGNIZE in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-qry-select-match-recognize-pattern |
| Use table references in Databricks SQL queries | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-qry-select-table-reference |
| Invoke table-valued functions as table references in Databricks SQL | https://learn.microsoft.com/en-us/azure/databricks/sql/language-manual/sql-ref-syntax-qry-select-tvf |
| Build custom stateful apps with transformWithState | https://learn.microsoft.com/en-us/azure/databricks/stateful-applications/ |
| Example Databricks transformWithState streaming applications | https://learn.microsoft.com/en-us/azure/databricks/stateful-applications/examples |
| Use Avro with Kafka streaming in Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/avro-dataframe |
| Use Delta Lake tables as streaming sources and sinks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/delta-lake |
| Structured Streaming integration patterns with external systems | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/examples |
| Use foreachBatch for custom Databricks streaming sinks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/foreach |
| Process protocol buffers with Databricks Structured Streaming | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/protocol-buffers |
| Implement real-time Structured Streaming integrations in Databricks | https://learn.microsoft.com/en-us/azure/databricks/structured-streaming/real-time/examples |
| Use change data feed for Delta and Iceberg tables | https://learn.microsoft.com/en-us/azure/databricks/tables/features/change-data-feed |
| Run ACID SQL transactions on Unity Catalog tables | https://learn.microsoft.com/en-us/azure/databricks/transactions/ |
| Create Scala user-defined aggregate functions in Databricks | https://learn.microsoft.com/en-us/azure/databricks/udf/aggregate-scala |
| Implement and register Python UDFs in Azure Databricks | https://learn.microsoft.com/en-us/azure/databricks/udf/python |
| Define Python user-defined table functions in Databricks | https://learn.microsoft.com/en-us/azure/databricks/udf/python-udtf |
| Implement Scala scalar UDFs for Spark SQL | https://learn.microsoft.com/en-us/azure/databricks/udf/scala |
| Access task context inside Databricks UDFs | https://learn.microsoft.com/en-us/azure/databricks/udf/udf-task-context |
| Create and manage Unity Catalog volumes with SQL | https://learn.microsoft.com/en-us/azure/databricks/volumes/utility-commands |
| Manage files in Azure Databricks Unity Catalog volumes | https://learn.microsoft.com/en-us/azure/databricks/volumes/volume-files |
