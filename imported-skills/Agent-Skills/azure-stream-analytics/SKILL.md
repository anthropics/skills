---
name: azure-stream-analytics
description: Expert knowledge for Azure Stream Analytics development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building ASA jobs with Event Hubs/Kafka, Cosmos DB/SQL/ADX outputs, ML/AML, IoT Edge, or Power BI, and other Azure Stream Analytics related development tasks. Not for Azure Data Factory (use azure-data-factory), Azure Synapse Analytics (use azure-synapse-analytics), Azure Databricks (use azure-databricks), Azure Event Hubs (use azure-event-hubs).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-14"
  generator: "docs2skills/1.0.0"
---
# Azure Stream Analytics Skill

This skill provides expert guidance for Azure Stream Analytics. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L56 | Diagnosing and fixing Stream Analytics job issues: error codes (config, data, internal/external), input/output and query problems, and debugging with job diagrams, metrics, logs, and UDF tools. |
| Best Practices | L57-L73 | Best practices for Stream Analytics job design, query patterns, performance tuning, scaling, reliability, time handling, geospatial logic, ML/Cosmos/SQL outputs, and alerting. |
| Decision Making | L74-L81 | Guidance on choosing tools, migration paths, autoscaling options, and comparing Azure real-time/stream processing services for designing Stream Analytics solutions. |
| Architecture & Design Patterns | L82-L87 | Designing resilient, geo-redundant Stream Analytics topologies and scaling jobs using Streaming Units, input/output partitioning, and performance tuning patterns. |
| Limits & Quotas | L88-L94 | Info on Stream Analytics capacity limits, streaming units (SUs), how to size/resize clusters, performance tuning, and specific constraints for Azure Stream Analytics on IoT Edge. |
| Security | L95-L114 | Securing Stream Analytics jobs with managed identities, private endpoints, VNets, data protection, credential rotation, and Azure Policy for outputs like Event Hubs, SQL, ADX, Cosmos DB, and Power BI |
| Configuration | L115-L148 | Configuring Stream Analytics jobs: inputs, outputs (SQL, Cosmos DB, Event Hubs, Kafka, Power BI, Delta Lake, etc.), autoscale, ordering, error handling, monitoring, and compatibility settings. |
| Integrations & Coding Patterns | L149-L166 | Patterns for integrating Stream Analytics with Kafka, Event Hubs, ML/AML, schema registry, and custom code (C#/JS UDFs/aggregates), plus JSON/Avro parsing and advanced scenarios like HFT. |
| Deployment | L167-L179 | Deploying, starting/stopping, scaling, and moving Stream Analytics jobs and clusters, plus CI/CD automation via ARM/Bicep, GitHub Actions, Azure DevOps, npm/NuGet, and IoT Edge/Stack Hub. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve Stream Analytics configuration error codes | https://learn.microsoft.com/en-us/azure/stream-analytics/configuration-error-codes |
| Resolve Stream Analytics data error codes | https://learn.microsoft.com/en-us/azure/stream-analytics/data-error-codes |
| Understand Stream Analytics resource log data errors | https://learn.microsoft.com/en-us/azure/stream-analytics/data-errors |
| Debug Stream Analytics queries locally with Visual Studio job diagram | https://learn.microsoft.com/en-us/azure/stream-analytics/debug-locally-using-job-diagram |
| Debug Stream Analytics queries locally with VS Code job diagram | https://learn.microsoft.com/en-us/azure/stream-analytics/debug-locally-using-job-diagram-vs-code |
| Debug user-defined functions in Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/debug-user-defined-functions |
| Resolve Stream Analytics external availability error codes | https://learn.microsoft.com/en-us/azure/stream-analytics/external-availability-error-codes |
| Resolve Stream Analytics external error codes | https://learn.microsoft.com/en-us/azure/stream-analytics/external-error-codes |
| Resolve Stream Analytics internal error codes | https://learn.microsoft.com/en-us/azure/stream-analytics/internal-error-codes |
| Use Stream Analytics job diagram and metrics to troubleshoot jobs | https://learn.microsoft.com/en-us/azure/stream-analytics/job-diagram-with-metrics |
| Troubleshoot Stream Analytics jobs with resource logs | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-job-diagnostic-logs |
| Debug Stream Analytics jobs with logical job diagram | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-job-logical-diagram-with-metrics |
| Use physical job diagram metrics to debug Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-job-physical-diagram-with-metrics |
| Diagnose and fix Azure Stream Analytics input issues | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-troubleshoot-input |
| Troubleshoot Azure Stream Analytics output connection problems | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-troubleshoot-output |
| Troubleshoot Azure Stream Analytics query problems | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-troubleshoot-query |

### Best Practices
| Topic | URL |
|-------|-----|
| Develop and debug Azure Stream Analytics jobs locally | https://learn.microsoft.com/en-us/azure/stream-analytics/develop-locally |
| Build geofencing and geospatial aggregation with Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/geospatial-scenarios |
| Implement input validation patterns for Stream Analytics resiliency | https://learn.microsoft.com/en-us/azure/stream-analytics/input-validation |
| Optimize Stream Analytics query performance with Job Simulation | https://learn.microsoft.com/en-us/azure/stream-analytics/optimize-query-using-job-diagram-simulator |
| Optimize non-parallelizable Stream Analytics jobs with repartitioning | https://learn.microsoft.com/en-us/azure/stream-analytics/repartition |
| Apply best practices for Stream Analytics to Cosmos DB | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-documentdb-output |
| Analyze Stream Analytics job performance using metrics and dimensions | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-job-analysis-with-metric-dimensions |
| Improve Azure Stream Analytics job reliability and upgrades | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-job-reliability |
| Optimize Azure Stream Analytics with query parallelization | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-parallelization |
| Optimize Azure SQL Database output performance for Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-sql-output-perf |
| Apply common query patterns in Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-stream-analytics-query-patterns |
| Implement configurable threshold-based alerting in Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-threshold-based-rules |
| Design time handling and lateness in Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-time-handling |

### Decision Making
| Topic | URL |
|-------|-----|
| Select developer tools for Azure Stream Analytics jobs | https://learn.microsoft.com/en-us/azure/stream-analytics/feature-comparison |
| Migrate Stream Analytics projects from Visual Studio to VS Code | https://learn.microsoft.com/en-us/azure/stream-analytics/migrate-to-vscode |
| Choose and configure autoscale for Stream Analytics SUs | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-autoscale |
| Choose Azure real-time and stream processing services | https://learn.microsoft.com/en-us/azure/stream-analytics/streaming-technologies |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design geo-redundant Azure Stream Analytics job architectures | https://learn.microsoft.com/en-us/azure/stream-analytics/geo-redundancy |
| Scale Azure Stream Analytics jobs with SUs and partitioning | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-scale-jobs |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Resize Azure Stream Analytics clusters by streaming units | https://learn.microsoft.com/en-us/azure/stream-analytics/scale-cluster |
| Understand Azure Stream Analytics on IoT Edge limits and support | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-edge |
| Understand and tune Azure Stream Analytics streaming units | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-streaming-unit-consumption |

### Security
| Topic | URL |
|-------|-----|
| Configure managed identity for Azure Data Explorer outputs | https://learn.microsoft.com/en-us/azure/stream-analytics/azure-data-explorer-managed-identity |
| Configure managed identity auth for Stream Analytics Blob output | https://learn.microsoft.com/en-us/azure/stream-analytics/blob-output-managed-identity |
| Securely connect Stream Analytics jobs to Azure VNets | https://learn.microsoft.com/en-us/azure/stream-analytics/connect-job-to-vnet |
| Use managed identities for Cosmos DB outputs in Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/cosmos-db-managed-identity |
| Configure data protection for Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/data-protection |
| Access Event Hubs from Stream Analytics with managed identities | https://learn.microsoft.com/en-us/azure/stream-analytics/event-hubs-managed-identity |
| Apply built-in Azure Policy definitions to Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/policy-reference |
| Set up managed identity authentication for Stream Analytics Power BI output | https://learn.microsoft.com/en-us/azure/stream-analytics/powerbi-output-managed-identity |
| Configure Stream Analytics cluster managed private endpoints | https://learn.microsoft.com/en-us/azure/stream-analytics/private-endpoints |
| Secure Azure Stream Analytics jobs in virtual networks | https://learn.microsoft.com/en-us/azure/stream-analytics/run-job-in-virtual-network |
| Apply Azure Policy compliance controls to Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/security-controls-policy |
| Send Stream Analytics outputs to Service Bus with managed identity | https://learn.microsoft.com/en-us/azure/stream-analytics/service-bus-managed-identity |
| Use managed identities from Stream Analytics to Azure SQL and Synapse | https://learn.microsoft.com/en-us/azure/stream-analytics/sql-database-output-managed-identity |
| Rotate input and output credentials for Azure Stream Analytics jobs | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-login-credentials-inputs-outputs |
| Use managed identities with Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-managed-identities-overview |
| Configure user-assigned managed identities for Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-user-assigned-managed-identity-overview |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Cosmos DB as Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/azure-cosmos-db-output |
| Configure Azure Data Explorer as Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/azure-database-explorer-output |
| Connect Azure Stream Analytics outputs to Azure Functions | https://learn.microsoft.com/en-us/azure/stream-analytics/azure-functions-output |
| Configure Azure Synapse Analytics dedicated SQL pool as Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/azure-synapse-analytics-output |
| Configure Blob Storage and Data Lake Gen2 outputs for Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/blob-storage-azure-data-lake-gen2-output |
| Configure Stream Analytics autoscale settings via CI/CD tool | https://learn.microsoft.com/en-us/azure/stream-analytics/cicd-autoscale |
| Configure Azure Event Hubs as output for Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/event-hubs-output |
| Configure event ordering policies in Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/event-ordering |
| Reference for Stream Analytics JobConfig.json fields in VS Code | https://learn.microsoft.com/en-us/azure/stream-analytics/job-config-json |
| Configure Kafka output for Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/kafka-output |
| Configure monitoring for Azure Stream Analytics with Azure Monitor | https://learn.microsoft.com/en-us/azure/stream-analytics/monitor-azure-stream-analytics |
| Reference for Azure Stream Analytics monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/stream-analytics/monitor-azure-stream-analytics-reference |
| Configure Azure Database for PostgreSQL as Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/postgresql-database-output |
| Configure Power BI as an Azure Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/power-bi-output |
| Configure Service Bus queues as Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/service-bus-queues-output |
| Configure Service Bus topics as Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/service-bus-topics-output |
| Configure Azure SQL Database as Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/sql-database-output |
| Configure Azure SQL Database as Stream Analytics output | https://learn.microsoft.com/en-us/azure/stream-analytics/sql-db-table |
| Use Azure SQL Database as reference data input for Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/sql-reference-data |
| Configure compatibility levels for Azure Stream Analytics jobs | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-compatibility-level |
| Configure custom blob output partitioning in Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-custom-path-patterns-blob-storage-output |
| Configure input sources for Azure Stream Analytics jobs | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-define-inputs |
| Monitor and manage Stream Analytics jobs with PowerShell | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-monitor-and-manage-jobs-use-powershell |
| Programmatically enable and configure Stream Analytics job monitoring | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-monitor-jobs |
| Monitor Stream Analytics jobs using Azure portal metrics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-monitoring |
| Configure output error handling policies in Azure Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-output-error-policy |
| Configure Protobuf input deserialization in Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-parsing-protobuf |
| Set up Azure Monitor alerts for Stream Analytics jobs | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-set-up-alerts |
| Set up Azure Table storage output for Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/table-storage-output |
| Configure Azure Stream Analytics output to Delta Lake | https://learn.microsoft.com/en-us/azure/stream-analytics/write-to-delta-lake |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Confluent Cloud Kafka as Stream Analytics input | https://learn.microsoft.com/en-us/azure/stream-analytics/confluent-kafka-input |
| Send Stream Analytics output to Confluent Cloud Kafka | https://learn.microsoft.com/en-us/azure/stream-analytics/confluent-kafka-output |
| Integrate Azure Machine Learning models as Stream Analytics UDFs | https://learn.microsoft.com/en-us/azure/stream-analytics/machine-learning-udf |
| Implement SQL UPDATE/UPSERT via Azure Functions from Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/sql-database-upsert |
| Connect Azure Stream Analytics jobs to Kafka streams | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-define-kafka-input |
| Manage Stream Analytics jobs with .NET Management SDK | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-dotnet-management-sdk |
| Write C# user-defined functions for Stream Analytics in Visual Studio | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-edge-csharp-udf |
| Develop .NET Standard user-defined functions for Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-edge-csharp-udf-methods |
| Implement high-frequency trading with Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-high-frequency-trading |
| Create JavaScript user-defined aggregates in Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-javascript-user-defined-aggregates |
| Implement JavaScript user-defined functions in Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-javascript-user-defined-functions |
| Use built-in ML anomaly detection in Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-machine-learning-anomaly-detection |
| Parse JSON, Avro, and complex data in Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-parsing-json |
| Integrate Azure Stream Analytics with Event Hubs Schema Registry | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-schema-registry-integration |

### Deployment
| Topic | URL |
|-------|-----|
| Generate and deploy Stream Analytics jobs with Bicep | https://learn.microsoft.com/en-us/azure/stream-analytics/cicd-deploy-with-bicep |
| Deploy Stream Analytics jobs using GitHub Actions workflows | https://learn.microsoft.com/en-us/azure/stream-analytics/cicd-github-actions |
| Move Azure Stream Analytics clusters across regions | https://learn.microsoft.com/en-us/azure/stream-analytics/move-cluster |
| Deploy Stream Analytics edge jobs to Azure Stack Hub | https://learn.microsoft.com/en-us/azure/stream-analytics/on-azure-stack |
| Export Stream Analytics jobs as ARM templates | https://learn.microsoft.com/en-us/azure/stream-analytics/resource-manager-export |
| Set up Azure DevOps CI/CD for Stream Analytics | https://learn.microsoft.com/en-us/azure/stream-analytics/set-up-cicd-pipeline |
| Start Azure Stream Analytics jobs via portal, PowerShell, and Visual Studio | https://learn.microsoft.com/en-us/azure/stream-analytics/start-job |
| Implement CI/CD for Stream Analytics on IoT Edge via REST | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-cicd-api |
| Stop and delete Azure Stream Analytics jobs safely | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-clean-up-your-job |
| Use Stream Analytics CI/CD NuGet package with MSBuild | https://learn.microsoft.com/en-us/azure/stream-analytics/stream-analytics-tools-for-visual-studio-cicd |