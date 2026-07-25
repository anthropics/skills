---
name: azure-sql-database
description: Expert knowledge for Azure SQL Database development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when choosing tiers/Hyperscale, setting geo-replication/DR, using Entra auth/Always Encrypted, or automating deployments, and other Azure SQL Database related development tasks. Not for Azure SQL Managed Instance (use azure-sql-managed-instance), SQL Server on Azure Virtual Machines (use azure-sql-virtual-machines), Azure Cosmos DB (use azure-cosmos-db), Azure Synapse Analytics (use azure-synapse-analytics).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure SQL Database Skill

This skill provides expert guidance for Azure SQL Database. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L61 | Diagnosing and fixing Azure SQL issues: performance (CPU, memory, deadlocks, blocking), connectivity, scaling, import/export, geo-replication, Data Sync, Elastic Scale, and log-full errors. |
| Best Practices | L62-L79 | Best practices for Azure SQL operations: monitoring, security, HA/DR, failover, read replicas, maintenance, space management, elastic pools, Data Sync, and post-migration T-SQL adaptation. |
| Decision Making | L80-L107 | Guidance for choosing Azure SQL tiers, pricing models, licensing, Hyperscale options, DR/HA, automation, and migration paths from SQL Server or legacy features. |
| Architecture & Design Patterns | L108-L124 | Patterns and architectures for geo-replication, DR, availability, sharding/elastic scale-out, connectivity/routing, rolling upgrades, and multitenant SaaS design in Azure SQL. |
| Limits & Quotas | L125-L136 | Limits, quotas, and resource caps for Azure SQL (free offers, DTU/vCore for single DBs and pools), plus maintenance windows and how to request quota increases. |
| Security | L137-L202 | Securing Azure SQL: Entra auth and managed identities, auditing and Defender, Always Encrypted and TDE with CMK, network/firewall controls, data masking/classification, and secure backup/DR. |
| Configuration | L203-L267 | Configuring Azure SQL databases/servers: monitoring, backups, geo-replication/failover, security (TLS, Always Encrypted, immutability), scaling, elastic pools/jobs, Data Sync, and CLI/PowerShell setup. |
| Integrations & Coding Patterns | L268-L298 | Connecting apps and tools to Azure SQL (EF Core, .NET, Node.js, Python, Go), plus PowerShell/CLI automation for auditing, scaling, geo-replication, data sync, and streaming/Spark integration. |
| Deployment | L299-L314 | Deploying and scaling Azure SQL databases/MI: automation (GitHub, ARM, Bicep, Terraform), Hyperscale/zone-redundant setup, regional moves, feature availability, and dev environment setup. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure SQL capacity deployment and scaling errors | https://learn.microsoft.com/en-us/azure/azure-sql/capacity-errors-troubleshoot?view=azuresql |
| Resolve common Azure SQL database watcher issues | https://learn.microsoft.com/en-us/azure/azure-sql/database-watcher-faq?view=azuresql |
| Analyze and prevent deadlocks in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/analyze-prevent-deadlocks?view=azuresql |
| Fix slow database import and export in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/database-import-export-hang?view=azuresql |
| Use RecoveryManager to fix Azure SQL shard maps | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-database-recovery-manager?view=azuresql |
| Troubleshoot Azure SQL Database Elastic Scale issues | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-scale-faq?view=azuresql |
| Diagnose and fix high CPU in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/high-cpu-diagnose-troubleshoot?view=azuresql |
| Troubleshoot performance issues in Azure SQL Hyperscale | https://learn.microsoft.com/en-us/azure/azure-sql/database/hyperscale-performance-diagnostics?view=azuresql |
| Diagnose Azure SQL query performance bottlenecks | https://learn.microsoft.com/en-us/azure/azure-sql/database/identify-query-performance-issues?view=azuresql |
| Monitor and troubleshoot In-Memory OLTP storage capacity | https://learn.microsoft.com/en-us/azure/azure-sql/database/in-memory-oltp-monitor-space?view=azuresql |
| Use DMVs to troubleshoot Azure SQL performance | https://learn.microsoft.com/en-us/azure/azure-sql/database/monitoring-with-dmvs?view=azuresql |
| Use Azure Resource Health to troubleshoot Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/resource-health-to-troubleshoot-connectivity?view=azuresql |
| Troubleshoot common Azure SQL Data Sync issues | https://learn.microsoft.com/en-us/azure/azure-sql/database/sql-data-sync-troubleshoot?view=azuresql |
| Troubleshoot transient connectivity errors for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-common-connectivity-issues?view=azuresql |
| Troubleshoot Azure SQL and Fabric SQL connectivity errors | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-common-errors-issues?view=azuresql |
| Troubleshoot geo-replication and redo lag in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-geo-replication-redo?view=azuresql |
| Investigate and fix memory issues in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-memory-errors-issues?view=azuresql |
| Resolve transaction log full errors in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/troubleshoot-transaction-log-errors-issues?view=azuresql-db |
| Identify and resolve blocking in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/understand-resolve-blocking?view=azuresql |
| Resolve known issues in Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/azure-sql/managed-instance/doc-changes-updates-known-issues?view=azuresql |
| Resolve transaction log full errors in Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/azure-sql/managed-instance/troubleshoot-transaction-log-errors-issues?view=azuresql-mi |

### Best Practices
| Topic | URL |
|-------|-----|
| Analyze Azure SQL monitoring data with KQL and T-SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database-watcher-analyze?view=azuresql |
| Apply auditing best practices in production Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/auditing-best-practices?view=azuresql |
| Run disaster recovery drills for Azure SQL workloads | https://learn.microsoft.com/en-us/azure/azure-sql/database/disaster-recovery-drills?view=azuresql |
| Optimize resource management in dense Azure SQL elastic pools | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-pool-resource-management?view=azuresql |
| Configure and operate Azure SQL failover groups with best practices | https://learn.microsoft.com/en-us/azure/azure-sql/database/failover-group-sql-db?view=azuresql |
| Manage and reclaim Azure SQL Database file space | https://learn.microsoft.com/en-us/azure/azure-sql/database/file-space-manage?view=azuresql-db |
| Apply HA and DR configuration checklist for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/high-availability-disaster-recovery-checklist?view=azuresql |
| Operate Azure SQL databases effectively after migration | https://learn.microsoft.com/en-us/azure/azure-sql/database/manage-data-after-migrating-to-database?view=azuresql |
| Plan for Azure SQL planned maintenance events | https://learn.microsoft.com/en-us/azure/azure-sql/database/planned-maintenance?view=azuresql |
| Configure and use read scale-out replicas in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/read-scale-out?view=azuresql |
| Apply security best practices to Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/secure-database?view=azuresql |
| Apply security best practices for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/security-best-practice?view=azuresql |
| Apply best practices for Azure SQL Data Sync | https://learn.microsoft.com/en-us/azure/azure-sql/database/sql-data-sync-best-practices?view=azuresql |
| Adapt SQL Server T-SQL for Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/transact-sql-tsql-differences-sql-server?view=azuresql |

### Decision Making
| Topic | URL |
|-------|-----|
| Decide when to use Azure Hybrid Benefit for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/azure-hybrid-benefit?view=azuresql |
| Use Azure SQL decision tree to choose service | https://learn.microsoft.com/en-us/azure/azure-sql/azure-sql-decision-tree?view=azuresql |
| Understand Copilot in Azure SQL capabilities and usage | https://learn.microsoft.com/en-us/azure/azure-sql/copilot/copilot-azure-sql-faq?view=azuresql |
| Plan deployment of Always Encrypted secure enclaves | https://learn.microsoft.com/en-us/azure/azure-sql/database/always-encrypted-enclaves-plan?view=azuresql |
| Plan and manage Azure SQL Database costs | https://learn.microsoft.com/en-us/azure/azure-sql/database/cost-management?view=azuresql |
| Choose Azure SQL disaster recovery options for regional outages | https://learn.microsoft.com/en-us/azure/azure-sql/database/disaster-recovery-guidance?view=azuresql |
| Choose migration path from elastic query shard map manager | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-query-horizontal-partitioning-migration?view=azuresql |
| Compare Azure SQL Database vs Managed Instance features | https://learn.microsoft.com/en-us/azure/azure-sql/database/features-comparison?view=azuresql |
| Plan and use Hyperscale elastic pools for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/hyperscale-elastic-pool-overview?view=azuresql |
| Choose job automation options for Azure SQL and Synapse | https://learn.microsoft.com/en-us/azure/azure-sql/database/job-automation-overview?view=azuresql |
| Plan and manage Azure SQL Hyperscale databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/manage-hyperscale-database?view=azuresql |
| Migrate Azure SQL databases from DTU to vCore model | https://learn.microsoft.com/en-us/azure/azure-sql/database/migrate-dtu-to-vcore?view=azuresql |
| Choose Azure SQL Database vCore vs DTU purchasing | https://learn.microsoft.com/en-us/azure/azure-sql/database/purchasing-models?view=azuresql |
| Choose and use Azure Reservations for Azure SQL compute | https://learn.microsoft.com/en-us/azure/azure-sql/database/reservations-discount-overview?view=azuresql |
| Reverse migrate Azure SQL Hyperscale to General Purpose | https://learn.microsoft.com/en-us/azure/azure-sql/database/reverse-migrate-from-hyperscale?view=azuresql |
| Choose and configure Azure SQL serverless tier | https://learn.microsoft.com/en-us/azure/azure-sql/database/serverless-tier-overview?view=azuresql |
| Evaluate Azure SQL Hyperscale capabilities and constraints | https://learn.microsoft.com/en-us/azure/azure-sql/database/service-tier-hyperscale-frequently-asked-questions-faq?view=azuresql |
| Choose and use Hyperscale secondary replica types | https://learn.microsoft.com/en-us/azure/azure-sql/database/service-tier-hyperscale-replicas?view=azuresql |
| Decide when to use Azure SQL Hyperscale tier | https://learn.microsoft.com/en-us/azure/azure-sql/database/service-tier-hyperscale?view=azuresql |
| Use DTU-based purchasing model for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/service-tiers-dtu?view=azuresql |
| Choose Azure SQL vCore tiers and configurations | https://learn.microsoft.com/en-us/azure/azure-sql/database/service-tiers-sql-database-vcore?view=azuresql |
| Select migration alternatives for retiring SQL Data Sync | https://learn.microsoft.com/en-us/azure/azure-sql/database/sql-data-sync-retirement-migration?view=azuresql |
| Configure license-free standby replicas for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/standby-replica-how-to-configure?view=azuresql |
| Plan and decide SQL Server to Azure SQL migrations | https://learn.microsoft.com/en-us/azure/azure-sql/migration-guides/modernization?view=azuresql |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design and use active geo-replication for Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/active-geo-replication-overview?view=azuresql |
| Use automatic geo-redundant backups and restore in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/automated-backups-overview?view=azuresql |
| Understand Azure SQL connectivity architecture and routing | https://learn.microsoft.com/en-us/azure/azure-sql/database/connectivity-architecture?view=azuresql |
| Understand Azure SQL connectivity architecture and connection policies | https://learn.microsoft.com/en-us/azure/azure-sql/database/connectivity-architecture?view=azuresql |
| Choose geo-replication patterns for global Azure SQL apps | https://learn.microsoft.com/en-us/azure/azure-sql/database/designing-cloud-solutions-for-disaster-recovery?view=azuresql |
| Disaster recovery patterns for Azure SQL elastic pools | https://learn.microsoft.com/en-us/azure/azure-sql/database/disaster-recovery-strategies-for-applications-with-elastic-pool?view=azuresql |
| Design elastic scale-out architectures with Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-scale-introduction?view=azuresql |
| Move and rebalance data between sharded Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-scale-overview-split-and-merge?view=azuresql |
| Configure geo-distributed Azure SQL applications with failover | https://learn.microsoft.com/en-us/azure/azure-sql/database/geo-distributed-application-configure-tutorial?view=azuresql |
| Understand Azure SQL local and zone-redundant availability architecture | https://learn.microsoft.com/en-us/azure/azure-sql/database/high-availability-sla-local-zone-redundancy?view=azuresql |
| Understand Azure SQL Hyperscale distributed architecture | https://learn.microsoft.com/en-us/azure/azure-sql/database/hyperscale-architecture?view=azuresql |
| Design rolling upgrade patterns with Azure SQL geo-replication | https://learn.microsoft.com/en-us/azure/azure-sql/database/manage-application-rolling-upgrade?view=azuresql |
| Select multitenant SaaS tenancy models on Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/saas-tenancy-app-design-patterns?view=azuresql |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure SQL Database free offer limits | https://learn.microsoft.com/en-us/azure/azure-sql/database/free-offer-faq?view=azuresql |
| Understand Azure SQL Database free tier limits | https://learn.microsoft.com/en-us/azure/azure-sql/database/free-offer?view=azuresql |
| Use Azure free account to deploy free Azure SQL database | https://learn.microsoft.com/en-us/azure/azure-sql/database/free-sql-db-free-account-how-to-deploy?view=azuresql |
| Understand Azure SQL Database maintenance window behavior | https://learn.microsoft.com/en-us/azure/azure-sql/database/maintenance-window-faq?view=azuresql |
| Elastic pool DTU resource limits for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/resource-limits-dtu-elastic-pools?view=azuresql |
| Single database DTU resource limits for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/resource-limits-dtu-single-databases?view=azuresql |
| Review vCore resource limits for Azure SQL elastic pools | https://learn.microsoft.com/en-us/azure/azure-sql/database/resource-limits-vcore-elastic-pools?view=azuresql |
| Review vCore resource limits for single Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/resource-limits-vcore-single-databases?view=azuresql |

### Security
| Topic | URL |
|-------|-----|
| Connect .NET to Azure SQL with Entra MFA | https://learn.microsoft.com/en-us/azure/azure-sql/database/active-directory-interactive-connect-azure-sql-db?view=azuresql |
| Configure security for Azure SQL disaster recovery replicas | https://learn.microsoft.com/en-us/azure/azure-sql/database/active-geo-replication-security-configure?view=azuresql |
| Configure Azure Attestation for Always Encrypted enclaves | https://learn.microsoft.com/en-us/azure/azure-sql/database/always-encrypted-enclaves-configure-attestation?view=azuresql |
| Enable Always Encrypted with secure enclaves in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/always-encrypted-enclaves-enable?view=azuresql |
| Get started with Always Encrypted secure enclaves in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/always-encrypted-enclaves-getting-started?view=azuresql |
| Register Entra applications for Azure SQL access | https://learn.microsoft.com/en-us/azure/azure-sql/database/application-authentication-get-client-id-keys?view=azuresql |
| Configure Azure SQL auditing to storage behind VNet | https://learn.microsoft.com/en-us/azure/azure-sql/database/audit-write-storage-account-behind-vnet-firewall?view=azuresql |
| Configure managed identity for Azure SQL auditing to storage | https://learn.microsoft.com/en-us/azure/azure-sql/database/auditing-managed-identity?view=azuresql |
| Audit Microsoft support operations on Azure SQL servers | https://learn.microsoft.com/en-us/azure/azure-sql/database/auditing-microsoft-support-operations?view=azuresql |
| Understand server vs database-level auditing policies | https://learn.microsoft.com/en-us/azure/azure-sql/database/auditing-server-level-database-level?view=azuresql |
| Configure auditing for Azure SQL and Synapse | https://learn.microsoft.com/en-us/azure/azure-sql/database/auditing-setup?view=azuresql |
| Configure Microsoft Entra authentication for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-aad-configure?view=azuresql |
| Understand Directory Readers role requirements for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-aad-directory-readers-role?view=azuresql |
| Configure Microsoft Entra authentication for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-aad-overview?view=azuresql |
| Configure Entra service principals for Azure SQL access | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-aad-service-principal-tutorial?view=azuresql |
| Use Entra service principals with Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-aad-service-principal?view=azuresql |
| Create and manage Entra logins in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-azure-ad-logins-tutorial?view=azuresql |
| Use Microsoft Entra server principals in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-azure-ad-logins?view=azuresql |
| Create Azure SQL server with Entra-only authentication | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-azure-ad-only-authentication-create-server?view=azuresql |
| Create Azure SQL logical server with user-assigned managed identity | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-azure-ad-user-assigned-managed-identity-create-server?view=azuresql |
| Configure managed identities for Azure SQL access | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-azure-ad-user-assigned-managed-identity?view=azuresql |
| Configure Microsoft Entra authentication for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/authentication-microsoft-entra-connect-to-azure-sql?view=azuresql |
| Configure and use Microsoft Defender for SQL with Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/azure-defender-for-sql?view=azuresql |
| Migrate Node.js apps to passwordless Azure SQL authentication | https://learn.microsoft.com/en-us/azure/azure-sql/database/azure-sql-passwordless-migration-nodejs?view=azuresql |
| Migrate Python apps to passwordless Azure SQL authentication | https://learn.microsoft.com/en-us/azure/azure-sql/database/azure-sql-passwordless-migration-python?view=azuresql |
| Migrate .NET apps to passwordless Azure SQL authentication | https://learn.microsoft.com/en-us/azure/azure-sql/database/azure-sql-passwordless-migration?view=azuresql |
| Use backup immutability for long-term retention in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/backup-immutability?view=azuresql |
| Block T-SQL CRUD for Azure SQL resource protection | https://learn.microsoft.com/en-us/azure/azure-sql/database/block-crud-tsql?view=azuresql |
| Classify and label sensitive data in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/data-discovery-and-classification-overview?view=azuresql |
| Import/export Azure SQL databases with Azure services access disabled | https://learn.microsoft.com/en-us/azure/azure-sql/database/database-import-export-azure-services-off?view=azuresql |
| Use managed identity for Azure SQL import and export | https://learn.microsoft.com/en-us/azure/azure-sql/database/database-import-export-managed-identity?view=azuresql |
| Import/export Azure SQL databases over Private Link | https://learn.microsoft.com/en-us/azure/azure-sql/database/database-import-export-private-link?view=azuresql |
| Set up dynamic data masking in Azure SQL portal | https://learn.microsoft.com/en-us/azure/azure-sql/database/dynamic-data-masking-configure-portal?view=azuresql |
| Configure dynamic data masking in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/dynamic-data-masking-overview?view=azuresql |
| Configure split-merge service security with certificates | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-scale-split-merge-security-configuration?view=azuresql |
| Configure Azure SQL Database IP firewall rules securely | https://learn.microsoft.com/en-us/azure/azure-sql/database/firewall-configure?view=azuresql |
| Configure isolated security for Hyperscale named replicas | https://learn.microsoft.com/en-us/azure/azure-sql/database/hyperscale-named-replica-security-configure?view=azuresql |
| Configure logins and user access in Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/logins-create-manage?view=azuresql |
| Configure network access controls for Azure SQL and Synapse | https://learn.microsoft.com/en-us/azure/azure-sql/database/network-access-controls-overview?view=azuresql |
| Configure Network Security Perimeter for Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/network-security-perimeter?view=azuresql |
| Configure outbound firewall rules for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/outbound-firewall-rule-overview?view=azuresql |
| Apply built-in Azure Policy definitions for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/policy-reference?view=azuresql |
| Manage Azure SQL VNet service endpoints with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/vnet-service-endpoint-rule-powershell-create?view=azuresql |
| Secure an Azure SQL Database using built-in features | https://learn.microsoft.com/en-us/azure/azure-sql/database/secure-database-tutorial?view=azuresql |
| Use Azure Policy regulatory controls for Azure SQL compliance | https://learn.microsoft.com/en-us/azure/azure-sql/database/security-controls-policy?view=azuresql |
| Use fixed server roles on Azure SQL logical servers | https://learn.microsoft.com/en-us/azure/azure-sql/database/security-server-roles?view=azuresql |
| Store SQL Vulnerability Assessment scans in secured storage | https://learn.microsoft.com/en-us/azure/azure-sql/database/sql-database-vulnerability-assessment-storage?view=azuresql |
| Configure Advanced Threat Protection for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/threat-detection-configure?view=azuresql |
| Use Advanced Threat Protection for Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/threat-detection-overview?view=azuresql |
| Enable TDE with Azure Key Vault for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-configure?view=azuresql |
| Configure cross-tenant CMK TDE with user-assigned identity | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-create-server-cross-tenant?view=azuresql |
| Create Azure SQL server with user-assigned identity and CMK TDE | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-create-server?view=azuresql |
| Set up cross-tenant customer-managed keys for Azure SQL TDE | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-cross-tenant?view=azuresql |
| Manage database-level customer-managed TDE keys in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-database-level-basic-actions?view=azuresql |
| Configure geo-replication and restore for database-level CMK TDE | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-database-level-geo-replication-restore?view=azuresql |
| Configure database-level TDE with customer-managed keys in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-database-level-overview?view=azuresql |
| Configure TDE with user-assigned managed identity in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-identity?view=azuresql |
| Rotate Azure SQL TDE protector with PowerShell and CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-key-rotation?view=azuresql |
| Implement customer-managed TDE with Azure Key Vault | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-overview?view=azuresql |
| Rotate and remove BYOK TDE protector via PowerShell/CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/transparent-data-encryption-byok-remove-tde-protector?view=azuresql |
| Secure Azure SQL with virtual network service endpoints and rules | https://learn.microsoft.com/en-us/azure/azure-sql/database/vnet-service-endpoint-rule-overview?view=azuresql |
| Prepare for Azure SQL TLS root certificate rotation | https://learn.microsoft.com/en-us/azure/azure-sql/updates/ssl-root-certificate-expiring?view=azuresql |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Monitor alerts for database watcher data | https://learn.microsoft.com/en-us/azure/azure-sql/database-watcher-alerts?view=azuresql |
| Understand database watcher datasets and collected metrics | https://learn.microsoft.com/en-us/azure/azure-sql/database-watcher-data?view=azuresql |
| Configure Azure SQL Database watcher settings | https://learn.microsoft.com/en-us/azure/azure-sql/database-watcher-manage?view=azuresql |
| Create a database watcher with Entra auth and private connectivity | https://learn.microsoft.com/en-us/azure/azure-sql/database-watcher-quickstart?view=azuresql |
| Configure active geo-replication and failover for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/active-geo-replication-configure-portal?view=azuresql |
| Configure ADO.NET direct routing ports for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/adonet-v12-develop-direct-route-ports?view=azuresql |
| Configure advance maintenance notifications for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/advance-notifications?view=azuresql |
| Configure Always Encrypted with Intel SGX enclaves in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/always-encrypted-enclaves-getting-started-sgx?view=azuresql |
| Configure Always Encrypted with VBS enclaves in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/always-encrypted-enclaves-getting-started-vbs?view=azuresql |
| Define and deploy Azure SQL resources with ARM templates | https://learn.microsoft.com/en-us/azure/azure-sql/database/arm-templates-content-guide?view=azuresql |
| Interpret Azure SQL Database audit log format | https://learn.microsoft.com/en-us/azure/azure-sql/database/audit-log-format?view=azuresql |
| Change automated backup retention and redundancy in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/automated-backups-change-settings?view=azuresql |
| Configure legal hold immutability for Azure SQL LTR backups | https://learn.microsoft.com/en-us/azure/azure-sql/database/backup-immutability-legal-hold?view=azuresql |
| Configure time-based immutability for Azure SQL LTR backups | https://learn.microsoft.com/en-us/azure/azure-sql/database/backup-immutability-time-based?view=azuresql |
| Configure MAXDOP for Azure SQL and Fabric databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/configure-max-degree-of-parallelism?view=azuresql |
| Configure TLS and connection policy for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/connectivity-settings?view=azuresql |
| Configure and use soft delete for Azure SQL logical servers | https://learn.microsoft.com/en-us/azure/azure-sql/database/deleted-logical-server-restore?view=azuresql |
| Understand DTU benchmark characteristics for Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/dtu-benchmark?view=azuresql |
| Use performance counters for Azure SQL shard maps | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-database-perf-counters?view=azuresql |
| Understand and configure Azure SQL elastic jobs | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-jobs-overview?view=azuresql |
| Configure Azure SQL elastic jobs with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-jobs-powershell-create?view=azuresql |
| Configure Azure SQL elastic jobs with T-SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-jobs-tsql-create-manage?view=azuresql |
| Create and manage Azure SQL elastic jobs | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-jobs-tutorial?view=azuresql |
| Create and manage Azure SQL elastic pools | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-pool-manage?view=azuresql |
| Configure scaling for Azure SQL elastic pools | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-pool-scale?view=azuresql |
| Configure elastic queries for vertically partitioned databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-query-getting-started-vertical?view=azuresql |
| Configure cross-database queries for different schemas | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-query-vertical-partitioning?view=azuresql |
| Enable availability zone redundancy for Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/enable-zone-redundancy?view=azuresql |
| Configure failover groups for Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/failover-group-configure-sql-db?view=azuresql |
| Configure automated backups for Hyperscale databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/hyperscale-automated-backups-overview?view=azuresql |
| Configure and manage Azure SQL Hyperscale named replicas | https://learn.microsoft.com/en-us/azure/azure-sql/database/hyperscale-named-replica-configure?view=azuresql |
| Configure In-Memory OLTP for Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/in-memory-oltp-configure?view=azuresql |
| Configure Intelligent Insights monitoring for Azure SQL performance | https://learn.microsoft.com/en-us/azure/azure-sql/database/intelligent-insights-overview?view=azuresql |
| Configure dev container templates for Azure SQL development | https://learn.microsoft.com/en-us/azure/azure-sql/database/local-dev-experience-dev-containers?view=azuresql |
| Configure long-term backup retention for Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/long-term-backup-retention-configure?view=azuresql |
| Configure maintenance windows for Azure SQL databases and pools | https://learn.microsoft.com/en-us/azure/azure-sql/database/maintenance-window-configure?view=azuresql |
| Understand and use maintenance windows for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/maintenance-window?view=azuresql |
| Reference for Azure SQL Database monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/azure-sql/database/monitoring-sql-database-azure-monitor-reference?view=azuresql |
| Configure monitoring for Azure SQL with Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-sql/database/monitoring-sql-database-azure-monitor?view=azuresql |
| Restore Azure SQL databases from automatic backups | https://learn.microsoft.com/en-us/azure/azure-sql/database/recovery-using-backups?view=azuresql |
| Query Azure SQL resources with Azure Resource Graph | https://learn.microsoft.com/en-us/azure/azure-sql/database/resource-graph-samples?view=azuresql |
| Add Azure SQL databases to failover groups via CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/add-database-to-failover-group-cli?view=azuresql |
| Configure failover groups for Azure SQL elastic pools | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/add-elastic-pool-to-failover-group-cli?view=azuresql |
| Back up Azure SQL databases to storage with CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/backup-database-cli?view=azuresql |
| Copy Azure SQL databases to new servers via CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/copy-database-to-new-server-cli?view=azuresql |
| Create and configure an Azure SQL database with CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/create-and-configure-database-cli?view=azuresql |
| Create and configure an Azure SQL database with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/create-and-configure-database-powershell?view=azuresql |
| Import BACPAC files into Azure SQL using CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/import-from-bacpac-cli?view=azuresql |
| Monitor and scale an Azure SQL database with CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/monitor-and-scale-database-cli?view=azuresql |
| Move Azure SQL databases between elastic pools via CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/move-database-between-elastic-pools-cli?view=azuresql |
| Restore Azure SQL databases from backups using CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/restore-database-cli?view=azuresql |
| Scale Azure SQL elastic pools using CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/scale-pool-cli?view=azuresql |
| Configure active geo-replication for Azure SQL via CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/setup-geodr-failover-database-cli?view=azuresql |
| Configure Azure SQL failover groups with CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/setup-geodr-failover-group-cli?view=azuresql |
| Set up geo-replication for pooled databases with CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/setup-geodr-failover-pool-cli?view=azuresql |
| Configure SQL Data Sync between Azure SQL databases via REST | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/sql-data-sync-sync-data-between-sql-databases-rest-api?view=azuresql |
| Configure scaling for single Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/single-database-scale?view=azuresql |
| Install and configure Data Sync Agent for Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/sql-data-sync-agent-overview?view=azuresql |
| Set up Azure SQL Data Sync groups and schedules | https://learn.microsoft.com/en-us/azure/azure-sql/database/sql-data-sync-sql-server-configure?view=azuresql |
| Configure maintenance windows for Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-sql/maintenance-window-azure-sql?view=azuresql |
| Reference monitoring metrics for Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/azure-sql/managed-instance/monitoring-sql-managed-instance-azure-monitor-reference?view=azuresql |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Manage Azure SQL auditing using APIs and automation | https://learn.microsoft.com/en-us/azure/azure-sql/database/auditing-manage-using-api?view=azuresql |
| Use Entity Framework Core with Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/azure-sql-dotnet-entity-framework-core-quickstart?view=azuresql |
| Connect and query Azure SQL using .NET SqlClient | https://learn.microsoft.com/en-us/azure/azure-sql/database/azure-sql-dotnet-quickstart?view=azuresql |
| Query Azure SQL from Node.js using mssql package | https://learn.microsoft.com/en-us/azure/azure-sql/database/azure-sql-javascript-mssql-quickstart?view=azuresql |
| Connect to Azure SQL using Python mssql-python driver | https://learn.microsoft.com/en-us/azure/azure-sql/database/azure-sql-python-quickstart?view=azuresql |
| Connect to Azure SQL using Go and go-mssqldb | https://learn.microsoft.com/en-us/azure/azure-sql/database/connect-query-go?view=azuresql |
| Connect and query Azure SQL using Python | https://learn.microsoft.com/en-us/azure/azure-sql/database/connect-query-python?view=azuresql |
| Manage Azure SQL DNS aliases with PowerShell and CLI | https://learn.microsoft.com/en-us/azure/azure-sql/database/dns-alias-powershell-create?view=azuresql |
| Manage shard maps with Elastic Database client library | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-scale-shard-map-management?view=azuresql |
| Integrate Elastic Database tools with Entity Framework | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-scale-use-entity-framework-applications-visual-studio?view=azuresql |
| Integrate Elastic Database tools with Dapper | https://learn.microsoft.com/en-us/azure/azure-sql/database/elastic-scale-working-with-dapper?view=azuresql |
| Use in-memory OLTP and columnstore samples in Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/in-memory-oltp-sample?view=azuresql |
| Configure transactional replication to Azure SQL Database | https://learn.microsoft.com/en-us/azure/azure-sql/database/replication-to-sql-database?view=azuresql |
| Create Azure SQL failover group and add database via PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/add-database-to-failover-group-powershell?view=azuresql |
| Add Azure SQL elastic pool to failover group with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/add-elastic-pool-to-failover-group-powershell?view=azuresql |
| Copy Azure SQL database to new logical server via PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/copy-database-to-new-server-powershell?view=azuresql |
| Import BACPAC into Azure SQL database using PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/import-from-bacpac-powershell?view=azuresql |
| Monitor and scale single Azure SQL database using PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/monitor-and-scale-database-powershell?view=azuresql |
| Monitor and scale Azure SQL elastic pool with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/monitor-and-scale-pool-powershell?view=azuresql |
| Move Azure SQL databases between elastic pools with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/move-database-between-elastic-pools-powershell?view=azuresql |
| Restore Azure SQL database from automatic backups with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/restore-database-powershell?view=azuresql |
| Configure Azure SQL active geo-replication with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/setup-geodr-and-failover-database-powershell?view=azuresql |
| Set up elastic pool geo-replication with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/setup-geodr-and-failover-elastic-pool-powershell?view=azuresql |
| Sync data between Azure SQL Database and SQL Server with PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/sql-data-sync-sync-data-between-azure-onprem?view=azuresql |
| Configure SQL Data Sync between Azure SQL databases via PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/scripts/sql-data-sync-sync-data-between-sql-databases?view=azuresql |
| Configure and use Spark connector with Azure SQL | https://learn.microsoft.com/en-us/azure/azure-sql/database/spark-connector?view=azuresql |
| Stream real-time data into Azure SQL using Stream Analytics | https://learn.microsoft.com/en-us/azure/azure-sql/database/stream-data-stream-analytics-integration?view=azuresql |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Azure SQL database changes with GitHub Actions | https://learn.microsoft.com/en-us/azure/azure-sql/database/connect-github-actions-sql-db?view=azuresql |
| Convert Azure SQL Database to Hyperscale tier | https://learn.microsoft.com/en-us/azure/azure-sql/database/convert-to-hyperscale?view=azuresql |
| Create transactionally consistent copies of Azure SQL databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/database-copy?view=azuresql |
| Create zone-redundant Azure SQL Hyperscale databases | https://learn.microsoft.com/en-us/azure/azure-sql/database/hyperscale-create-zone-redundant-database?view=azuresql |
| Manage Hyperscale elastic pools with CLI and PowerShell | https://learn.microsoft.com/en-us/azure/azure-sql/database/hyperscale-elastic-pool-command-line?view=azuresql |
| Set up Azure SQL dev environment using dev containers | https://learn.microsoft.com/en-us/azure/azure-sql/database/local-dev-experience-dev-containers-quickstart?view=azuresql |
| Move Azure SQL databases and pools across regions | https://learn.microsoft.com/en-us/azure/azure-sql/database/move-resources-across-regions?view=azuresql |
| Check Azure SQL Database feature availability by region | https://learn.microsoft.com/en-us/azure/azure-sql/database/region-availability?view=azuresql |
| Scale Azure SQL Database and Managed Instance resources | https://learn.microsoft.com/en-us/azure/azure-sql/database/scale-resources?view=azuresql |
| Deploy Azure SQL single database with ARM template | https://learn.microsoft.com/en-us/azure/azure-sql/database/single-database-create-arm-template-quickstart?view=azuresql |
| Deploy Azure SQL single database using Bicep | https://learn.microsoft.com/en-us/azure/azure-sql/database/single-database-create-bicep-quickstart?view=azuresql |
| Provision Azure SQL server and database using Terraform | https://learn.microsoft.com/en-us/azure/azure-sql/database/single-database-create-terraform-quickstart?view=azuresql |
| Check Azure SQL Managed Instance feature availability by region | https://learn.microsoft.com/en-us/azure/azure-sql/managed-instance/region-availability?view=azuresql |