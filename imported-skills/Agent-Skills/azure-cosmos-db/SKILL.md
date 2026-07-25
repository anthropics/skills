---
name: azure-cosmos-db
description: Expert knowledge for Azure Cosmos DB development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using Cosmos DB NoSQL/Mongo/Cassandra/PostgreSQL APIs, change feed, multi-region, vector search, or migrations, and other Azure Cosmos DB related development tasks. Not for Azure Table Storage (use azure-table-storage), Azure SQL Database (use azure-sql-database), Azure SQL Managed Instance (use azure-sql-managed-instance), Azure Database for PostgreSQL (use azure-database-postgresql).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Cosmos DB Skill

This skill provides expert guidance for Azure Cosmos DB. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Location | Description |
|----------|----------|-------------|
| Troubleshooting | L37-L91 | Diagnosing and fixing Cosmos DB errors, performance, connectivity, encryption, and SDK/API-specific issues (SQL, MongoDB, Cassandra, Gremlin, PostgreSQL, DocumentDB) using logs, metrics, and KQL. |
| Best Practices | L92-L158 | Performance, cost, resiliency, and SDK best practices for Cosmos DB (NoSQL, Mongo, Cassandra, PostgreSQL), including partitioning, indexing, RU optimization, change feed, DR, and HA. |
| Decision Making | L159-L220 | Guides for choosing Cosmos DB/DocumentDB/PostgreSQL options (throughput, consistency, regions, pricing) and planning migrations, upgrades, analytics, and vector index strategies. |
| Architecture & Design Patterns | L221-L252 | Architectural patterns for AI/RAG, agent memory, knowledge graphs, multi-tenant and microservice designs, high availability, change feed, analytics, and vector search on Cosmos DB and PostgreSQL. |
| Limits & Quotas | L253-L293 | Limits, quotas, and behaviors for Cosmos DB (and DocumentDB): throughput, autoscale, burst, partitions, backups/restore, serverless, free tier, indexing, Gremlin, PostgreSQL, and Cassandra. |
| Security | L294-L366 | Securing Cosmos DB across all APIs: identity/RBAC, network isolation, encryption/CMK, auditing, firewall/TLS, data masking, Defender/Policy governance, and PostgreSQL/Cassandra/Mongo-specific hardening. |
| Configuration | L367-L495 | Configuring Cosmos DB and related services: throughput, indexing, backup/restore, monitoring, emulators, vector/search, multi-region, Cassandra/Mongo/PostgreSQL/Table APIs, and SDK performance/observability. |
| Integrations & Coding Patterns | [integrations.md](integrations.md) | SDK usage, integrations, and patterns for connecting apps and tools to Cosmos DB (NoSQL, Mongo, Cassandra, PostgreSQL), including bulk ops, change feed, Kafka/Spark/BI, vector/search, and migration. |
| Deployment | [deployment.md](deployment.md) | Deploying and managing Cosmos DB (NoSQL, Mongo, Cassandra, PostgreSQL, Table, DocumentDB) with Bicep/ARM/Terraform, CI/CD, emulator, migrations, upgrades, and maintenance. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Run advanced diagnostics queries for Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/diagnostic-queries |
| Use Log Analytics for Cosmos DB Cassandra error codes | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/error-codes-solution |
| Resolve issues with Cassandra materialized views in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/materialized-views-faq |
| Resolve common Cosmos DB Cassandra API errors | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/troubleshoot-common-issues |
| Fix NoHostAvailable and NoNodeAvailable in Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/troubleshoot-nohostavailable-exception |
| Troubleshoot revoked-state Cosmos DB CMK accounts | https://learn.microsoft.com/en-us/azure/cosmos-db/cmk-troubleshooting-guide |
| Troubleshoot Cosmos DB with advanced diagnostics log queries | https://learn.microsoft.com/en-us/azure/cosmos-db/diagnostic-queries |
| Run advanced diagnostics queries for Cosmos DB Gremlin | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/diagnostic-queries |
| Troubleshoot common questions for Azure Cosmos DB Gremlin API | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/faq |
| Interpret Cosmos DB Gremlin response headers for debugging | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/headers |
| Use diagnostics queries to troubleshoot Cosmos DB MongoDB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/diagnostic-queries |
| Resolve common Azure Cosmos DB MongoDB error codes | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/error-codes-solutions |
| Resolve common Azure Cosmos DB for MongoDB issues | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/faq |
| Prevent rate-limiting errors in Cosmos DB MongoDB operations | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/prevent-rate-limiting-errors |
| Troubleshoot query performance issues in Cosmos DB MongoDB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/troubleshoot-query-performance |
| Use aggregated diagnostics logs to troubleshoot Cosmos DB requests | https://learn.microsoft.com/en-us/azure/cosmos-db/monitor-aggregated-logs |
| Troubleshoot Cosmos DB with basic diagnostics KQL queries | https://learn.microsoft.com/en-us/azure/cosmos-db/monitor-logs-basic-queries |
| Monitor normalized request units to diagnose Cosmos DB load | https://learn.microsoft.com/en-us/azure/cosmos-db/monitor-normalized-request-units |
| Analyze Cosmos DB request unit usage for operations | https://learn.microsoft.com/en-us/azure/cosmos-db/monitor-request-unit-usage |
| Monitor and troubleshoot Cosmos DB server-side latency | https://learn.microsoft.com/en-us/azure/cosmos-db/monitor-server-side-latency |
| Troubleshoot connection issues to Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-troubleshoot-common-connection-issues |
| Diagnose and fix read-only Azure Cosmos DB for PostgreSQL clusters | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-troubleshoot-read-only |
| Run useful diagnostic queries on Cosmos DB for PostgreSQL clusters | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-useful-diagnostic-queries |
| Troubleshoot Azure Cosmos DB Shell installation and usage issues | https://learn.microsoft.com/en-us/azure/cosmos-db/shell/troubleshooting |
| Use Azure SRE Agent to diagnose Cosmos DB issues | https://learn.microsoft.com/en-us/azure/cosmos-db/site-reliability-engineering-agent |
| Fix Cosmos DB 400 bad request and partition key errors | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-bad-request |
| Troubleshoot Azure Functions trigger for Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-changefeed-functions |
| Troubleshoot cross-tenant CMK issues in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-cmk |
| Resolve Cosmos DB 409 conflict exceptions | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-conflict |
| Troubleshoot Azure Cosmos DB .NET SDK issues | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-dotnet-sdk |
| Resolve Cosmos DB .NET SDK request header too large (400) errors | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-dotnet-sdk-request-header-too-large |
| Troubleshoot HTTP 408 timeouts in Cosmos DB .NET SDK | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-dotnet-sdk-request-time-out |
| Diagnose and fix slow requests in Cosmos DB .NET SDK | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-dotnet-sdk-slow-request |
| Troubleshoot Cosmos DB 403 forbidden exceptions | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-forbidden |
| Diagnose and troubleshoot Cosmos DB Async Java SDK v2 | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-java-async-sdk |
| Troubleshoot HTTP 408 timeouts in Cosmos DB Java v4 SDK | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-java-sdk-request-time-out |
| Fix service unavailable errors in Cosmos DB Java v4 SDK | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-java-sdk-service-unavailable |
| Troubleshoot Azure Cosmos DB Java SDK v4 issues | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-java-sdk-v4 |
| Troubleshoot Cosmos DB 404 Not Found exceptions | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-not-found |
| Diagnose and troubleshoot Cosmos DB Python SDK issues | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-python-sdk |
| Troubleshoot Azure Cosmos DB SQL query performance issues | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-query-performance |
| Troubleshoot Azure Cosmos DB 429 request rate errors | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-request-rate-too-large |
| Resolve Azure Cosmos DB HTTP 408 request timeout errors | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-request-time-out |
| Diagnose SDK availability and failover in multi-region Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-sdk-availability |
| Troubleshoot Cosmos DB service unavailable connectivity errors | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-service-unavailable |
| Troubleshoot Cosmos DB 401 unauthorized access errors | https://learn.microsoft.com/en-us/azure/cosmos-db/troubleshoot-unauthorized |
| Use Cosmos DB metrics and insights to debug common issues | https://learn.microsoft.com/en-us/azure/cosmos-db/use-metrics |
| Troubleshoot CMK-based encryption issues in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/how-to-database-encryption-troubleshoot |
| Diagnose Azure DocumentDB query performance with explain() | https://learn.microsoft.com/en-us/azure/documentdb/how-to-read-explain-output |
| Diagnose and fix common Azure DocumentDB errors | https://learn.microsoft.com/en-us/azure/documentdb/troubleshoot-common-issues |
| Troubleshoot Azure DocumentDB replication issues | https://learn.microsoft.com/en-us/azure/documentdb/troubleshoot-replication |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply automated performance, cost, and security recommendations in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/automated-recommendations |
| Benchmark Cosmos DB for NoSQL with YCSB | https://learn.microsoft.com/en-us/azure/cosmos-db/benchmarking-framework |
| Follow best practices for Cosmos DB .NET SDK v3 | https://learn.microsoft.com/en-us/azure/cosmos-db/best-practice-dotnet |
| Apply Java v4 Cosmos DB SDK best practices | https://learn.microsoft.com/en-us/azure/cosmos-db/best-practice-java |
| Optimize Azure Cosmos DB with Python SDK best practices | https://learn.microsoft.com/en-us/azure/cosmos-db/best-practice-python |
| Optimize Azure Cosmos DB with JavaScript SDK best practices | https://learn.microsoft.com/en-us/azure/cosmos-db/best-practices-javascript |
| Adapt Apache Cassandra apps to Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/adoption |
| Consume change feed from Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/change-feed |
| Map Cassandra consistency levels to Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/consistency-mapping |
| Configure Cosmos DB Cassandra extension driver settings | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/driver-extensions |
| Measure RU charges for Cosmos DB Cassandra queries | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/find-request-unit-charge |
| Use lightweight transactions in Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/lightweight-transactions |
| Use materialized views (preview) in Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/materialized-views |
| Design partitions for Cosmos DB Cassandra workloads | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/partitioning |
| Avoid rate limiting with server-side retry in Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/prevent-rate-limiting-errors |
| Use secondary indexing in Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/secondary-indexing |
| Use tokens and token() with Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/tokens |
| Implement and consume Azure Cosmos DB change feed | https://learn.microsoft.com/en-us/azure/cosmos-db/change-feed |
| Design resilient Cosmos DB SDK client applications | https://learn.microsoft.com/en-us/azure/cosmos-db/conceptual-resilient-sdk-applications |
| Understand Cosmos DB conflict types and policies | https://learn.microsoft.com/en-us/azure/cosmos-db/conflict-resolution-policies |
| Choose IoT partition keys for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/design-partitioning-iot |
| Apply disaster recovery strategies for Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/disaster-recovery-guidance |
| Optimize vector indexing and search in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/gen-ai/vector-search-performance-tips |
| Apply GitHub Copilot best practices for Azure Cosmos DB in VS Code | https://learn.microsoft.com/en-us/azure/cosmos-db/github-copilot-visual-studio-code-best-practices |
| Use hierarchical partition keys for scalable Cosmos DB data | https://learn.microsoft.com/en-us/azure/cosmos-db/hierarchical-partition-keys |
| Enable autoscale throughput for Cosmos DB resources | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-provision-autoscale-throughput |
| Use shared database throughput safely in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-provision-database-throughput |
| Monitor Azure Cosmos DB change feed processor progress | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-use-change-feed-estimator |
| Merge Cosmos DB partitions to reduce fragmentation | https://learn.microsoft.com/en-us/azure/cosmos-db/merge |
| Model and partition real-world data in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/model-partition-example |
| Redistribute throughput across Cosmos DB MongoDB partitions | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/distribute-throughput-across-partitions |
| Optimize Cosmos DB for MongoDB indexing configuration | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/indexing |
| Optimize write performance for Cosmos DB MongoDB workloads | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/optimize-write-performance |
| Optimize Cosmos DB MongoDB workloads after migration | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/post-migration-optimization |
| Use MongoDB read preference with globally distributed Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/readpreference-global-distribution |
| Use MongoDB aggregation pipelines on Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/tutorial-aggregation |
| Optimize Azure Cosmos DB costs for dev and production workloads | https://learn.microsoft.com/en-us/azure/cosmos-db/optimize-costs |
| Use Azure Cosmos DB partial document update effectively | https://learn.microsoft.com/en-us/azure/cosmos-db/partial-document-update-faq |
| Choose and manage partition keys in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/partitioning |
| Optimize performance of Cosmos DB .NET SDK v2 clients | https://learn.microsoft.com/en-us/azure/cosmos-db/performance-tips |
| Optimize performance of Cosmos DB .NET SDK v3 clients | https://learn.microsoft.com/en-us/azure/cosmos-db/performance-tips-dotnet-sdk-v3 |
| Apply Cosmos DB SDK query performance best practices | https://learn.microsoft.com/en-us/azure/cosmos-db/performance-tips-query-sdk |
| Tune query performance in Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-performance-tuning |
| Choose distribution columns in Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-choose-distribution-column |
| Optimize pgvector performance in Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-optimize-performance-pgvector |
| Use priority-based execution for Cosmos DB workloads | https://learn.microsoft.com/en-us/azure/cosmos-db/priority-based-execution-faq |
| Estimate and manage Cosmos DB request units | https://learn.microsoft.com/en-us/azure/cosmos-db/request-units |
| Apply best practices for scaling Cosmos DB throughput | https://learn.microsoft.com/en-us/azure/cosmos-db/scaling-provisioned-throughput-best-practices |
| Design synthetic partition keys in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/synthetic-partition-keys |
| Optimize Cosmos DB request unit consumption | https://learn.microsoft.com/en-us/azure/cosmos-db/understand-request-unit-consumption |
| Apply background indexing best practices in DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/background-indexing |
| Apply cross-region replication best practices in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/cross-region-replication |
| Implement HA and cross-region replication best practices in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/high-availability-replication-best-practices |
| Follow indexing best practices for DocumentDB collections | https://learn.microsoft.com/en-us/azure/documentdb/how-to-create-indexes |
| Configure and tune text indexes in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/how-to-create-text-index |
| Design and use wildcard indexes in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/how-to-create-wildcard-indexes |
| Migrate safely to ordered indexes in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/how-to-migrate-ordered-indexes |
| Optimize Azure DocumentDB queries using Index Advisor | https://learn.microsoft.com/en-us/azure/documentdb/index-advisor |
| Design sharding strategy for scalable Azure DocumentDB collections | https://learn.microsoft.com/en-us/azure/documentdb/partitioning |
| Apply security best practices for Azure DocumentDB clusters | https://learn.microsoft.com/en-us/azure/documentdb/security |
| Optimize performance for Azure Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/best-practice-performance |
| Apply HA and DR best practices for Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/resilient-applications |
| Use write-through cache to improve Cassandra managed instance performance | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/write-through-cache |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose analytics and BI options for Azure Cosmos DB data | https://learn.microsoft.com/en-us/azure/cosmos-db/analytics-and-business-intelligence-overview |
| Live dual-write migration to Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/migrate-data-dual-write-proxy |
| Choose scaling options for Cosmos DB Cassandra throughput | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/scale-account-throughput |
| Choose Azure Cosmos DB consistency levels | https://learn.microsoft.com/en-us/azure/cosmos-db/consistency-levels |
| Convert vCores to Cosmos DB RU/s for migration | https://learn.microsoft.com/en-us/azure/cosmos-db/convert-vcore-to-request-unit |
| Decide when to use Cosmos DB dedicated gateway | https://learn.microsoft.com/en-us/azure/cosmos-db/dedicated-gateway |
| Estimate Cosmos DB RU/s and cost with capacity planner | https://learn.microsoft.com/en-us/azure/cosmos-db/estimate-ru-with-capacity-planner |
| Manage multitenant throughput with Cosmos DB fleet pools | https://learn.microsoft.com/en-us/azure/cosmos-db/fleet-pools |
| Use global secondary indexes in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/global-secondary-indexes |
| Choose Cosmos DB manual vs autoscale throughput | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-choose-offer |
| Migrate from Cosmos DB .NET bulk executor to SDK v3 bulk support | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-migrate-from-bulk-executor-library |
| Migrate from Java bulk executor to Cosmos DB Java V4 bulk support | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-migrate-from-bulk-executor-library-java |
| Migrate from change feed processor library to .NET V3 SDK | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-migrate-from-change-feed-library |
| Migrate from Cosmos DB Kafka connector V1 to V2 | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-migrate-from-kafka-connector-v1-to-v2 |
| Plan and size Cosmos DB integrated cache | https://learn.microsoft.com/en-us/azure/cosmos-db/integrated-cache |
| Migrate Cosmos DB legacy metrics APIs to Azure Monitor | https://learn.microsoft.com/en-us/azure/cosmos-db/legacy-migrate-az-monitor |
| Migrate Cosmos DB from periodic to continuous backup | https://learn.microsoft.com/en-us/azure/cosmos-db/migrate-continuous-backup |
| Upgrade applications to Azure Cosmos DB .NET SDK v2 | https://learn.microsoft.com/en-us/azure/cosmos-db/migrate-dotnet-v2 |
| Upgrade applications to Azure Cosmos DB .NET SDK v3 | https://learn.microsoft.com/en-us/azure/cosmos-db/migrate-dotnet-v3 |
| Upgrade applications to Azure Cosmos DB Java SDK v4 | https://learn.microsoft.com/en-us/azure/cosmos-db/migrate-java-v4-sdk |
| Decide between Cosmos DB MongoDB and MongoDB Atlas | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/compare-mongodb-atlas |
| Evaluate benefits of upgrading to Cosmos DB MongoDB 4.0+ | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/compression-cost-savings |
| Map MongoDB consistency to Cosmos DB levels | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/consistency-mapping |
| Estimate RU/s and cost for Cosmos DB MongoDB workloads | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/estimate-ru-capacity-planner |
| Decide and migrate from Cosmos DB for MongoDB to DocumentDB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/how-to-migrate-documentdb |
| Plan pre-migration steps from MongoDB to Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/pre-migration-steps |
| Plan Cosmos DB network bandwidth usage and costs | https://learn.microsoft.com/en-us/azure/cosmos-db/network-bandwidth |
| Request Cosmos DB data restore from periodic backups via support | https://learn.microsoft.com/en-us/azure/cosmos-db/periodic-backup-request-data-restore |
| Understand burstable compute workloads on Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-burstable-compute |
| Plan and manage Cosmos DB for PostgreSQL cluster upgrades | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-upgrade |
| Determine application type for distributed modeling | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-app-type |
| Choose initial cluster size for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-scale-initial |
| Choose shard count for distributed tables in Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-shard-count |
| Plan migration from Cosmos DB PostgreSQL to Elastic Cluster | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/migrate-postgresql-elastic-cluster |
| Classify workloads for Cosmos DB for PostgreSQL scaling | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/quickstart-build-scalable-apps-classify |
| Plan compute and storage for Azure Cosmos DB for PostgreSQL clusters | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/resources-compute |
| Estimate and optimize pricing for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/resources-pricing |
| Choose Azure regions and resiliency options for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/resources-regions |
| Choose Azure Cosmos DB SQL SDK connectivity modes | https://learn.microsoft.com/en-us/azure/cosmos-db/sdk-connection-modes |
| Choose Cosmos DB serverless vs provisioned throughput | https://learn.microsoft.com/en-us/azure/cosmos-db/serverless |
| Use Azure Cosmos DB for Table with Azure Table Storage | https://learn.microsoft.com/en-us/azure/cosmos-db/table/support |
| Configure global distribution for Azure Cosmos DB for Table | https://learn.microsoft.com/en-us/azure/cosmos-db/table/tutorial-global-distribution |
| Decide between Cosmos DB provisioned and serverless | https://learn.microsoft.com/en-us/azure/cosmos-db/throughput-serverless |
| Use Cosmos DB Migration Assistant for RDBMS decisions | https://learn.microsoft.com/en-us/azure/cosmos-db/vscode-extension/cosmos-db-migration-assistant |
| Decide between Azure DocumentDB and MongoDB Atlas | https://learn.microsoft.com/en-us/azure/documentdb/compare-mongodb-atlas |
| Evaluate MongoDB feature compatibility in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/compatibility-features |
| Assess MongoDB Query Language compatibility in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/compatibility-query-language |
| Choose Azure DocumentDB cross-region failover modes | https://learn.microsoft.com/en-us/azure/documentdb/failover-modes |
| Assess MongoDB workloads for migration to Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/how-to-assess-plan-migration-readiness |
| Evaluate MongoDB compatibility for managed DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/managed-service-compatibility |
| Choose migration options from MongoDB to DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/migration-options |
| Plan MongoDB to DocumentDB migration strategies | https://learn.microsoft.com/en-us/azure/documentdb/migration-options |
| Compare vector search algorithms in DocumentDB using .NET | https://learn.microsoft.com/en-us/azure/documentdb/quickstart-dotnet-select-algorithm |
| Compare and tune DocumentDB vector index algorithms in Go | https://learn.microsoft.com/en-us/azure/documentdb/quickstart-go-select-algorithm |
| Evaluate DocumentDB vector index algorithms using Java | https://learn.microsoft.com/en-us/azure/documentdb/quickstart-java-select-algorithm |
| Select vector index algorithm in DocumentDB with TypeScript | https://learn.microsoft.com/en-us/azure/documentdb/quickstart-nodejs-select-algorithm |
| Choose optimal vector index and similarity in DocumentDB (Python) | https://learn.microsoft.com/en-us/azure/documentdb/quickstart-python-select-algorithm |
| Select Azure DocumentDB regions for deployment | https://learn.microsoft.com/en-us/azure/documentdb/regional-availability |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Implement AI agents and memory on Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/ai-agents |
| Design bulk import and update patterns with Cosmos DB bulk executor | https://learn.microsoft.com/en-us/azure/cosmos-db/bulk-executor-overview |
| Apply Azure Cosmos DB change feed design patterns | https://learn.microsoft.com/en-us/azure/cosmos-db/change-feed-design-patterns |
| Use Cosmos DB change feed for real-time analytics | https://learn.microsoft.com/en-us/azure/cosmos-db/changefeed-ecommerce-solution |
| Design agent memory patterns with Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/gen-ai/agentic-memories |
| Design AI knowledge graphs with Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/gen-ai/cosmos-ai-graph |
| Supply chain traceability solution with Cosmos DB Gremlin | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/solution-supply-chain-traceability |
| Configure multiple Azure Functions triggers for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-create-multiple-cosmos-db-triggers |
| Design Azure Cosmos DB multi-region write strategies | https://learn.microsoft.com/en-us/azure/cosmos-db/multi-region-writes |
| Apply per-partition automatic failover in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/per-partition-automatic-failover |
| Plan availability zone outage resiliency for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-availability-zones |
| Use table colocation for faster queries in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-colocation |
| Design high availability for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-high-availability |
| Use read replicas in Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-read-replicas |
| Model high-throughput transactional apps on Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/quickstart-build-scalable-apps-model-high-throughput |
| Design multi-tenant SaaS on Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/quickstart-build-scalable-apps-model-multi-tenant |
| Model real-time analytics apps on Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/quickstart-build-scalable-apps-model-real-time |
| Design microservices using Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/tutorial-design-database-microservices |
| Design scalable multi-tenant database on Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/tutorial-design-database-multi-tenant |
| Design real-time dashboard on Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/tutorial-design-database-realtime |
| Build serverless apps with Cosmos DB and Azure Functions | https://learn.microsoft.com/en-us/azure/cosmos-db/serverless-computing-database |
| Apply Cosmos DB design pattern for social media apps | https://learn.microsoft.com/en-us/azure/cosmos-db/social-media-apps |
| Use Autoscale for variable workloads in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/autoscale |
| Design hybrid BM25 and vector search in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/full-text-search-hybrid |
| Apply half-precision vectors for efficient AI storage in DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/half-precision |
| Use product quantization for scalable vector search in DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/product-quantization |
| Design dual-write Spark migration to Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/dual-write-proxy-migration |
| Architect Spark-based migrations to Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/spark-migration |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Autoscale throughput limits and behavior in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/autoscale-faq |
| Use Cosmos DB burst capacity limits effectively | https://learn.microsoft.com/en-us/azure/cosmos-db/burst-capacity |
| Burst capacity limits and usage rules in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/burst-capacity-faq |
| Choose Azure Cosmos DB change feed modes and limits | https://learn.microsoft.com/en-us/azure/cosmos-db/change-feed-modes |
| Azure Cosmos DB service quotas and default limits reference | https://learn.microsoft.com/en-us/azure/cosmos-db/concepts-limits |
| Understand limits for Cosmos DB continuous backup restore | https://learn.microsoft.com/en-us/azure/cosmos-db/continuous-backup-restore-frequently-asked-questions |
| Use Cosmos DB continuous backup and point-in-time restore | https://learn.microsoft.com/en-us/azure/cosmos-db/continuous-backup-restore-introduction |
| Throughput redistribution limits across Cosmos DB partitions | https://learn.microsoft.com/en-us/azure/cosmos-db/distribute-throughput-across-partitions-faq |
| Reference Azure Cosmos DB service limits and quotas | https://learn.microsoft.com/en-us/azure/cosmos-db/faq |
| Use Cosmos DB lifetime free tier limits | https://learn.microsoft.com/en-us/azure/cosmos-db/free-tier |
| Reference stopwords for Cosmos DB full text search | https://learn.microsoft.com/en-us/azure/cosmos-db/gen-ai/stopwords |
| Review runtime limits for Cosmos DB Gremlin engine | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/limits |
| Scale beyond 20-GB logical partition limits with HPK | https://learn.microsoft.com/en-us/azure/cosmos-db/hierarchical-partition-keys-unlimited-scale |
| Alert when Cosmos DB logical partition approaches 20 GB limit | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-alert-on-logical-partition-key-storage-size |
| Change Cosmos DB from serverless to provisioned throughput | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-change-capacity-mode |
| Redistribute throughput across Cosmos DB partitions | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-redistribute-throughput-across-partitions |
| Understand limits and behavior of Cosmos integrated cache | https://learn.microsoft.com/en-us/azure/cosmos-db/integrated-cache-faq |
| Estimate RU charges for key-value operations | https://learn.microsoft.com/en-us/azure/cosmos-db/key-value-store-cost |
| Create Cosmos DB containers with large partition keys | https://learn.microsoft.com/en-us/azure/cosmos-db/large-partition-keys |
| Migrate nonpartitioned Cosmos DB containers to partitioned | https://learn.microsoft.com/en-us/azure/cosmos-db/migrate-containers-partitioned-to-nonpartitioned |
| Use Azure Cosmos DB automatic backup and restore | https://learn.microsoft.com/en-us/azure/cosmos-db/online-backup-and-restore |
| Modify Cosmos DB periodic backup interval and retention limits | https://learn.microsoft.com/en-us/azure/cosmos-db/periodic-backup-modify-interval-retention |
| Change vCore compute quotas per region for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-compute-quota |
| Cluster limits and quotas for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/reference-limits |
| Use same-account restore with Cosmos DB continuous backup | https://learn.microsoft.com/en-us/azure/cosmos-db/restore-in-account-continuous-backup-frequently-asked-questions |
| Understand performance limits of Cosmos DB serverless | https://learn.microsoft.com/en-us/azure/cosmos-db/serverless-performance |
| Configure and understand Cosmos DB soft delete retention | https://learn.microsoft.com/en-us/azure/cosmos-db/soft-delete |
| Throughput bucket limits and throttling behavior in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/throughput-buckets-faq |
| Review compute and storage configuration options for Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/compute-storage |
| Review compute and storage configuration options for Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/compute-storage |
| Azure DocumentDB FAQ with limits and behaviors | https://learn.microsoft.com/en-us/azure/documentdb/faq |
| Understand Azure DocumentDB Free Tier limits | https://learn.microsoft.com/en-us/azure/documentdb/free-tier |
| Configure Premium SSD v2 performance for Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/high-performance-storage |
| Understand and configure indexes in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/indexing |
| Reference Azure DocumentDB service limits and quotas | https://learn.microsoft.com/en-us/azure/documentdb/limitations |
| Understand document size and batch write limits in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/max-document-size |
| Review limits and configuration FAQs for Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/faq |

### Security
| Topic | URL |
|-------|-----|
| Use managed identity for Cosmos DB access to Key Vault | https://learn.microsoft.com/en-us/azure/cosmos-db/access-key-vault-managed-identity |
| Configure private endpoints for Cosmos DB analytical store | https://learn.microsoft.com/en-us/azure/cosmos-db/analytical-store-private-endpoints |
| Audit Cosmos DB control plane operations with logs | https://learn.microsoft.com/en-us/azure/cosmos-db/audit-control-plane-logs |
| Secure Azure Cosmos DB for Apache Cassandra accounts | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/security |
| Configure RBAC permissions for Cosmos DB continuous restore | https://learn.microsoft.com/en-us/azure/cosmos-db/continuous-backup-restore-permissions |
| Configure Cosmos DB to meet data residency requirements | https://learn.microsoft.com/en-us/azure/cosmos-db/data-residency |
| Understand encryption at rest in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/database-encryption-at-rest |
| Protect Cosmos DB with Microsoft Defender for Cloud | https://learn.microsoft.com/en-us/azure/cosmos-db/defender-for-cosmos-db |
| Configure Dynamic Data Masking in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/dynamic-data-masking |
| Configure security for Azure Cosmos DB Gremlin accounts | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/security |
| Add and assign RBAC user roles in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-add-assign-user-roles |
| Use Always Encrypted client-side encryption in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-always-encrypted |
| Configure CORS for Azure Cosmos DB for NoSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-cross-origin-resource-sharing |
| Configure IP firewall rules for Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-firewall |
| Secure Cosmos DB with Network Security Perimeter | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-nsp |
| Configure Azure Private Link for Cosmos DB access | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-private-endpoints |
| Set up virtual network service endpoints for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-vnet-service-endpoint |
| Configure RBAC and Entra ID for Cosmos DB access | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-connect-role-based-access-control |
| Rotate primary and secondary keys in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-rotate-keys |
| Set up cross-tenant customer-managed keys for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-setup-cross-tenant-customer-managed-keys |
| Configure customer-managed keys with Azure Key Vault for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-setup-customer-managed-keys |
| Enable customer-managed keys on existing Cosmos DB accounts | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-setup-customer-managed-keys-existing-accounts |
| Configure CMK for Cosmos DB using Azure Managed HSM | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-setup-customer-managed-keys-mhsm |
| Authenticate Spark to Cosmos DB using Entra service principal | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-spark-service-principal |
| Configure RBAC for Cosmos DB for MongoDB data access | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/how-to-setup-role-based-access-control |
| Understand role-based access control in Cosmos DB MongoDB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/role-based-access-control |
| Harden security for Azure Cosmos DB for MongoDB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/security |
| Enforce governance for Cosmos DB with Azure Policy | https://learn.microsoft.com/en-us/azure/cosmos-db/policy |
| Use built-in Azure Policy definitions for Cosmos DB governance | https://learn.microsoft.com/en-us/azure/cosmos-db/policy-reference |
| Configure PostgreSQL and Entra ID authentication | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-authentication |
| Use customer-managed keys with Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-customer-managed-keys |
| Configure public access for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-firewall-rules |
| Configure private access for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-private-access |
| Implement row-level security for multi-tenant Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-row-level-security |
| Configure Microsoft Entra ID and PostgreSQL roles for Cosmos DB for PostgreSQL authentication | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/how-to-configure-authentication |
| Enable encryption with customer-managed keys for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/how-to-customer-managed-keys |
| Enable and configure pgAudit audit logging in Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/how-to-enable-audit |
| Create and manage firewall rules for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-manage-firewall-using-portal |
| Enable private access with Private Link for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-private-access |
| Configure TLS connection security for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-ssl-connection-security |
| Create Cosmos DB for PostgreSQL cluster with private access | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/tutorial-private-access |
| Reference data plane RBAC actions and roles in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/reference-data-plane-security |
| Reference data plane RBAC actions and roles in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/reference-data-plane-security |
| Apply Azure resource locks to Cosmos DB resources | https://learn.microsoft.com/en-us/azure/cosmos-db/resource-locks |
| Secure Azure Cosmos DB for NoSQL deployments | https://learn.microsoft.com/en-us/azure/cosmos-db/security |
| Apply security considerations and best practices to Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/security-considerations |
| Use Azure Policy regulatory compliance controls for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/security-controls-policy |
| Enforce minimum TLS version for Cosmos DB accounts | https://learn.microsoft.com/en-us/azure/cosmos-db/self-serve-minimum-tls-enforcement |
| Apply security best practices for Azure Cosmos DB Shell | https://learn.microsoft.com/en-us/azure/cosmos-db/shell/security |
| Store Cosmos DB credentials securely in Azure Key Vault | https://learn.microsoft.com/en-us/azure/cosmos-db/store-credentials-key-vault |
| Configure RBAC and Entra ID for Cosmos DB Table | https://learn.microsoft.com/en-us/azure/cosmos-db/table/how-to-connect-role-based-access-control |
| Configure RBAC and Entra ID for Cosmos DB Table | https://learn.microsoft.com/en-us/azure/cosmos-db/table/how-to-connect-role-based-access-control |
| Configure RBAC and Entra ID for Cosmos DB Table | https://learn.microsoft.com/en-us/azure/cosmos-db/table/how-to-connect-role-based-access-control |
| Configure RBAC with Microsoft Entra ID for Cosmos DB Table | https://learn.microsoft.com/en-us/azure/cosmos-db/table/how-to-connect-role-based-access-control |
| Reference for data plane RBAC roles in Azure Cosmos DB for Table | https://learn.microsoft.com/en-us/azure/cosmos-db/table/reference-data-plane-security |
| Reference for data plane RBAC roles in Azure Cosmos DB for Table | https://learn.microsoft.com/en-us/azure/cosmos-db/table/reference-data-plane-security |
| Secure Azure Cosmos DB for Table accounts and data | https://learn.microsoft.com/en-us/azure/cosmos-db/table/security |
| Prepare Cosmos DB workloads for TLS 1.3 support | https://learn.microsoft.com/en-us/azure/cosmos-db/tls-support |
| Configure Azure DocumentDB firewall rules for secure access | https://learn.microsoft.com/en-us/azure/documentdb/how-to-configure-firewall |
| Configure Entra ID RBAC access for Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/how-to-connect-role-based-access-control |
| Configure customer-managed key encryption for Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/how-to-data-encryption |
| Use Azure Private Link with Azure DocumentDB securely | https://learn.microsoft.com/en-us/azure/documentdb/how-to-private-link |
| Manage public network access to Azure DocumentDB clusters | https://learn.microsoft.com/en-us/azure/documentdb/how-to-public-access |
| Manage secondary native users and privileges in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/secondary-users |
| Assign Cosmos DB service principal roles for Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/add-service-principal |
| Configure customer-managed keys for Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/customer-managed-keys |
| Configure LDAP authentication for Azure Cassandra MI | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/ldap |
| Configure outbound network rules for Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/network-rules |
| Secure Cassandra managed instances with VPN and routing rules | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/use-vpn |

### Configuration
| Topic | URL |
|-------|-----|
| Configure change data capture for Cosmos DB analytical store | https://learn.microsoft.com/en-us/azure/cosmos-db/analytical-store-change-data-capture |
| Audit Cosmos DB point-in-time restore operations via activity logs | https://learn.microsoft.com/en-us/azure/cosmos-db/audit-restore-continuous |
| Create Cosmos DB Cassandra containers via portal and SDKs | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/how-to-create-container |
| Configure provisioned and autoscale throughput for Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/how-to-provision-throughput |
| Configure monitoring insights for Cosmos DB Cassandra | https://learn.microsoft.com/en-us/azure/cosmos-db/cassandra/monitor-insights |
| Reconfigure Azure Cosmos DB container partition key | https://learn.microsoft.com/en-us/azure/cosmos-db/change-partition-key |
| Configure and manage Azure Cosmos DB container copy jobs | https://learn.microsoft.com/en-us/azure/cosmos-db/container-copy |
| Configure resource model for Cosmos DB point-in-time restore | https://learn.microsoft.com/en-us/azure/cosmos-db/continuous-backup-restore-resource-model |
| Configure Azure Monitor alerts for Cosmos DB metrics and logs | https://learn.microsoft.com/en-us/azure/cosmos-db/create-alerts |
| Configure and use the Cosmos DB local emulator | https://learn.microsoft.com/en-us/azure/cosmos-db/emulator |
| Configure and run Azure Cosmos DB Linux-based emulator | https://learn.microsoft.com/en-us/azure/cosmos-db/emulator-linux |
| Use Windows Cosmos DB emulator command-line and PowerShell | https://learn.microsoft.com/en-us/azure/cosmos-db/emulator-windows-arguments |
| Use Fleet Analytics to monitor Cosmos DB usage and cost | https://learn.microsoft.com/en-us/azure/cosmos-db/fleet-analytics |
| Reference schema for Cosmos DB Fleet Analytics tables | https://learn.microsoft.com/en-us/azure/cosmos-db/fleet-analytics-schema-reference |
| Configure hybrid vector and full-text search in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/gen-ai/hybrid-search |
| Configure Sharded DiskANN vector indexes in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/gen-ai/sharded-diskann |
| Enable and use CDC in Cosmos DB analytical store | https://learn.microsoft.com/en-us/azure/cosmos-db/get-started-change-data-capture |
| Access and use system properties in Cosmos DB Gremlin | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/access-system-properties |
| Interpret execution profile metrics in Cosmos DB Gremlin | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/reference-execution-profile |
| Understand Gremlin feature support in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/gremlin/support |
| Configure Azure Functions trigger for Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-cosmos-db-trigger |
| Configure global secondary indexes in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-global-secondary-indexes |
| Configure Cosmos DB integrated cache and gateway | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-integrated-cache |
| Configure per-partition automatic failover for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-configure-per-partition-automatic-failover |
| Create and configure Cosmos DB fleets and fleetspaces | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-create-fleet |
| Define unique key constraints in Azure Cosmos DB containers | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-define-unique-keys |
| Enable Cosmos DB Fleet Analytics in Fabric workspace | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-enable-fleet-analytics |
| Configure and query geospatial indexing in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-geospatial-index-query |
| Configure and manage Cosmos DB conflict resolution | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-manage-conflicts |
| Configure and override Azure Cosmos DB consistency levels | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-manage-consistency |
| Manage and update Cosmos DB indexing policies via SDKs | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-manage-indexing-policy |
| Configure Cosmos DB multi-region writes in SDKs | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-multi-master |
| Provision container-level throughput in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-provision-container-throughput |
| Configure time to live (TTL) in Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/how-to-time-to-live |
| Interpret Cosmos DB indexing metrics to optimize queries | https://learn.microsoft.com/en-us/azure/cosmos-db/index-metrics |
| Configure Azure Cosmos DB indexing policies for performance | https://learn.microsoft.com/en-us/azure/cosmos-db/index-policy |
| Configure account-level throughput limits in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/limit-total-account-throughput |
| Provision Cosmos DB NoSQL with Bicep templates | https://learn.microsoft.com/en-us/azure/cosmos-db/manage-with-bicep |
| Manage Cosmos DB NoSQL resources using Azure CLI | https://learn.microsoft.com/en-us/azure/cosmos-db/manage-with-cli |
| Automate Azure Cosmos DB management with PowerShell | https://learn.microsoft.com/en-us/azure/cosmos-db/manage-with-powershell |
| Create Cosmos DB NoSQL resources with Terraform | https://learn.microsoft.com/en-us/azure/cosmos-db/manage-with-terraform |
| Check MongoDB 3.2 feature support in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/feature-support-32 |
| Check MongoDB 3.6 feature support in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/feature-support-36 |
| Check MongoDB 4.0 feature support in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/feature-support-40 |
| Check MongoDB 4.2 feature support in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/feature-support-42 |
| Check MongoDB 5.0 feature support in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/feature-support-50 |
| Reference supported MongoDB 6.0 features in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/feature-support-60 |
| Reference supported MongoDB 7.0 features in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/feature-support-70 |
| Retrieve RU charge for Cosmos DB MongoDB operations | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/find-request-unit-charge |
| Configure capabilities on Cosmos DB MongoDB accounts | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/how-to-configure-capabilities |
| Configure multi-region writes for Cosmos DB MongoDB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/how-to-configure-multi-region-write |
| Configure and create Cosmos DB MongoDB collections | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/how-to-create-container |
| Configure throughput for Cosmos DB MongoDB resources | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/how-to-provision-throughput |
| Configure per-document TTL in Cosmos DB for MongoDB | https://learn.microsoft.com/en-us/azure/cosmos-db/mongodb/time-to-live |
| Track Cosmos DB partition split and merge via activity logs | https://learn.microsoft.com/en-us/azure/cosmos-db/monitor-activity-logs-elastic-operations |
| Reference for Cosmos DB monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/cosmos-db/monitor-reference |
| Configure diagnostic settings and resource logs for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/monitor-resource-logs |
| Optimize Async Java v2 Cosmos DB client settings | https://learn.microsoft.com/en-us/azure/cosmos-db/performance-tips-async-java |
| Optimize Sync Java v2 Cosmos DB client settings | https://learn.microsoft.com/en-us/azure/cosmos-db/performance-tips-java |
| Configure Java v4 Cosmos DB client for performance | https://learn.microsoft.com/en-us/azure/cosmos-db/performance-tips-java-sdk-v4 |
| Configure Python Cosmos DB SDK for performance | https://learn.microsoft.com/en-us/azure/cosmos-db/performance-tips-python-sdk |
| Configure Cosmos DB periodic backup redundancy options | https://learn.microsoft.com/en-us/azure/cosmos-db/periodic-backup-storage-redundancy |
| Configure periodic backup storage redundancy for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/periodic-backup-update-storage-redundancy |
| Configure backup and restore for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-backup |
| Use columnar table storage in Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-columnar |
| Start and stop compute on Cosmos DB cluster nodes | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-compute-start-stop |
| Configure PgBouncer connection pooling for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-connection-pool |
| Configure monitoring and tuning for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-monitoring |
| Configure multi-tenant monitoring for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-multi-tenant-monitoring |
| Use DNS names and connection strings for Cosmos DB nodes | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/concepts-node-domain-name |
| Start and stop compute for Cosmos DB for PostgreSQL clusters | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/how-to-start-stop-cluster |
| Configure metric alerts for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-alert-on-metric |
| Configure and view availability zones for Cosmos DB for PostgreSQL nodes | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-availability-zones |
| Connect applications to Azure Cosmos DB for PostgreSQL clusters | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-connect |
| Configure high availability settings for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-high-availability |
| Access and configure logs for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-logging |
| Configure scheduled maintenance windows for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-maintenance |
| Monitor tenant statistics with multi-tenant metrics in Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-monitor-tenant-stats |
| View and interpret metrics for Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-monitoring |
| Manage read replicas for Cosmos DB for PostgreSQL in the Azure portal | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-read-replicas-portal |
| Restart Azure Cosmos DB for PostgreSQL clusters from the portal | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-restart |
| Restore Azure Cosmos DB for PostgreSQL clusters in same or different region | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-restore-portal |
| Configure cluster scale and high availability for Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-scale-grow |
| Rebalance shards in Azure Cosmos DB for PostgreSQL using the portal | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-scale-rebalance |
| Enable and use pgvector in Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/howto-use-pgvector |
| Use system tables for distributed queries in Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/reference-metadata |
| Configure server parameters in Azure Cosmos DB for PostgreSQL | https://learn.microsoft.com/en-us/azure/cosmos-db/postgresql/reference-parameters |
| Configure priority-based request execution in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/priority-based-execution |
| Provision Cosmos DB accounts with continuous backup | https://learn.microsoft.com/en-us/azure/cosmos-db/provision-account-continuous-backup |
| Configure autoscale throughput for Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/provision-throughput-autoscale |
| Use Cosmos DB SQL query metrics for performance analysis | https://learn.microsoft.com/en-us/azure/cosmos-db/query-metrics |
| Retrieve Cosmos DB SQL query performance metrics with .NET SDK | https://learn.microsoft.com/en-us/azure/cosmos-db/query-metrics-performance |
| Retrieve Cosmos DB query execution metrics with Python SDK | https://learn.microsoft.com/en-us/azure/cosmos-db/query-metrics-performance-python |
| Configure Cosmos DB account, database, and container | https://learn.microsoft.com/en-us/azure/cosmos-db/quickstart-portal |
| Provision Cosmos DB resources using Bicep | https://learn.microsoft.com/en-us/azure/cosmos-db/quickstart-template-bicep |
| Provision Cosmos DB with ARM templates | https://learn.microsoft.com/en-us/azure/cosmos-db/quickstart-template-json |
| Provision Cosmos DB with Terraform | https://learn.microsoft.com/en-us/azure/cosmos-db/quickstart-terraform |
| Restore Cosmos DB accounts using continuous backup | https://learn.microsoft.com/en-us/azure/cosmos-db/restore-account-continuous-backup |
| Configure resource model for Cosmos DB same-account restore | https://learn.microsoft.com/en-us/azure/cosmos-db/restore-in-account-continuous-backup-resource-model |
| Configure Cosmos DB SDK observability with OpenTelemetry and App Insights | https://learn.microsoft.com/en-us/azure/cosmos-db/sdk-observability |
| Use Azure Cosmos DB Shell commands and settings | https://learn.microsoft.com/en-us/azure/cosmos-db/shell/ |
| Set up Model Context Protocol server for Cosmos DB Shell | https://learn.microsoft.com/en-us/azure/cosmos-db/shell/model-context-protocol-setup |
| Find RU charges for Azure Cosmos DB for Table operations | https://learn.microsoft.com/en-us/azure/cosmos-db/table/find-request-unit-charge |
| Create and configure containers in Azure Cosmos DB for Table | https://learn.microsoft.com/en-us/azure/cosmos-db/table/how-to-create-container |
| Configure throughput buckets for shared Cosmos DB containers | https://learn.microsoft.com/en-us/azure/cosmos-db/throughput-buckets |
| Configure throughput control groups in Cosmos DB Java SDK | https://learn.microsoft.com/en-us/azure/cosmos-db/throughput-control-java |
| Configure throughput control in Azure Cosmos DB Spark connector | https://learn.microsoft.com/en-us/azure/cosmos-db/throughput-control-spark |
| Configure Cosmos DB time-to-live for automatic expiry | https://learn.microsoft.com/en-us/azure/cosmos-db/time-to-live |
| Tune Java v4 Cosmos DB connection configuration | https://learn.microsoft.com/en-us/azure/cosmos-db/tune-connection-configurations-java-sdk-v4 |
| Tune Azure Cosmos DB .NET SDK v3 connection settings | https://learn.microsoft.com/en-us/azure/cosmos-db/tune-connection-configurations-net-sdk-v3 |
| Configure workspace data transformations for Cosmos DB logs | https://learn.microsoft.com/en-us/azure/cosmos-db/tutorial-log-transformation |
| Define and use unique key policies in Cosmos DB | https://learn.microsoft.com/en-us/azure/cosmos-db/unique-keys |
| Configure and manage Azure DocumentDB cross-region replication | https://learn.microsoft.com/en-us/azure/documentdb/how-to-cluster-replica |
| Create and use Azure DocumentDB replica clusters for DR | https://learn.microsoft.com/en-us/azure/documentdb/how-to-cross-region-replica-portal |
| Set up metric-based alerts for DocumentDB clusters | https://learn.microsoft.com/en-us/azure/documentdb/how-to-manage-alerts |
| Configure and operate the Azure DocumentDB MCP Toolkit | https://learn.microsoft.com/en-us/azure/documentdb/mcp-toolkit |
| Configure and interpret DocumentDB monitoring metrics | https://learn.microsoft.com/en-us/azure/documentdb/monitor-metrics |
| Configure vector indexes and queries in Azure DocumentDB | https://learn.microsoft.com/en-us/azure/documentdb/vector-search |
| Configure hybrid Cassandra clusters using Azure CLI | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/configure-hybrid-cluster-cli |
| Create and scale Cassandra managed clusters with CLI | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/create-cluster-cli |
| Configure multi-region Cassandra managed clusters via CLI | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/create-multi-region-cluster |
| Run nodetool and SSTable DBA commands on Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/dba-commands |
| Automate Cassandra managed instance resource management with CLI | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/manage-resources-cli |
| Enable and configure materialized views in Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/materialized-views |
| Configure Azure Monitor metrics and logs for Cassandra managed instances | https://learn.microsoft.com/en-us/azure/managed-instance-apache-cassandra/monitor-clusters |
