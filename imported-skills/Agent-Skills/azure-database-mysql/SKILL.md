---
name: azure-database-mysql
description: Expert knowledge for Azure Database for MySQL development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when deploying MySQL Flexible Server, configuring HA/networking, tuning performance, securing access, or integrating apps, and other Azure Database for MySQL related development tasks. Not for Azure Database for MariaDB (use azure-database-mariadb), Azure Database for PostgreSQL (use azure-database-postgresql), Azure SQL Database (use azure-sql-database), Azure SQL Managed Instance (use azure-sql-managed-instance).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Database for MySQL Skill

This skill provides expert guidance for Azure Database for MySQL. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L53 | Diagnosing and fixing MySQL Flexible Server issues: connectivity, performance (CPU/memory/queries), capacity, corruption, replication latency, CLI errors, and using logs/self-heal tools. |
| Best Practices | L54-L71 | Best practices for monitoring, performance tuning, troubleshooting, safe operations, BCDR, and end-to-end migration/optimization for Azure Database for MySQL Flexible Server |
| Decision Making | L72-L89 | Planning MySQL on Azure: version lifecycle, capacity and tier selection, HA/BCDR, performance features, and migration/upgrade strategies and tools from on-prem or other MySQL. |
| Architecture & Design Patterns | L90-L97 | Patterns for connecting AKS to MySQL Flexible Server, designing backup/restore, data-in/out replication, high availability (zone-redundant), and read-replica-based scaling. |
| Limits & Quotas | L98-L106 | Limits, quotas, and performance caps for MySQL Flexible Server: max connections/cores/IOPS, storage IOPS behavior, quota increase requests, restart/stop limits, and delete/restore time limits. |
| Security | L107-L133 | Securing Azure Database for MySQL Flexible Server: network isolation (Private Link, firewalls), TLS and cert rotation, encryption, Entra auth, users, and audit logging before/after migration. |
| Configuration | L134-L164 | Configuring MySQL Flexible Server: HA, networking, replication, maintenance windows, monitoring/alerts, logging, server parameters, scaling, and point-in-time restore via portal and CLI. |
| Integrations & Coding Patterns | L165-L175 | Connecting to Azure Database for MySQL Flexible Server via CLI, Java/JDBC, Power BI, managing connection strings with Key Vault, and migrating data from RDS, on-prem, VMs, or Workbench |
| Deployment | L176-L185 | Automating MySQL Flexible Server deployments and changes (Azure Pipelines, GitHub Actions, Automation), handling backups, geo-restore, version upgrades, and scheduled maintenance. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Use MySQL Flexible Server error logs for troubleshooting | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-error-logs |
| Resolve database corruption in Azure MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-fix-corrupt-database |
| Use self-heal to automatically repair MySQL flexible server issues | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-self-heal |
| Troubleshoot Azure CLI issues for MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-cli-errors |
| Diagnose and fix MySQL flexible server connection issues | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-common-connection-issues |
| Troubleshoot common migration and usage errors in MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-common-errors |
| Troubleshoot connectivity issues and connection handling in MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-connectivity-issues |
| Troubleshoot high CPU utilization in MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-high-cpu-utilization |
| Troubleshoot low memory issues in MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-low-memory-issues |
| Troubleshoot query performance issues in MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-query-performance-new |
| Diagnose and fix MySQL flexible server capacity errors | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/resolve-capacity-errors |
| Use Query Performance Insight to diagnose Azure MySQL queries | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/tutorial-query-performance-insights |
| Troubleshoot replication latency on MySQL flexible server read replicas | https://learn.microsoft.com/en-us/azure/mysql/how-to-troubleshoot-replication-latency |

### Best Practices
| Topic | URL |
|-------|-----|
| Implement monitoring best practices for MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concept-monitor-best-practices |
| Apply operational best practices for Azure Database for MySQL | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concept-operation-excellence-best-practices |
| Run performance benchmarks on Azure MySQL flexible server effectively | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concept-perf-benchmark-best-practices |
| Optimize performance of Azure MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concept-performance-best-practices |
| Use Azure Monitor and Advisor for MySQL business continuity | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-business-continuity-advisor-monitor |
| Apply troubleshooting best practices for MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-troubleshooting-best-practices |
| Prevent and recover accidental deletion of MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-prevent-recover-accidental-delete |
| Restart Azure MySQL Flexible Server safely via portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-restart-server-portal |
| Profile and optimize MySQL flexible server queries using EXPLAIN | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-query-performance |
| Use sys_schema to diagnose performance issues in MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-troubleshoot-sys-schema |
| Execute data migration from on-premises MySQL to Azure | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/08-data-migration |
| Manage Azure Database for MySQL after migration | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/10-post-migration-management |
| Optimize Azure Database for MySQL performance after migration | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/11-optimization |
| Design BCDR for Azure Database for MySQL migrations | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/12-business-continuity-and-disaster-recovery |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan MySQL version lifecycle on Azure Database | https://learn.microsoft.com/en-us/azure/mysql/concepts-version-policy |
| Choose and purchase MySQL Flexible Server reserved capacity | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concept-reserved-pricing |
| Plan business continuity for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-business-continuity |
| High availability FAQ and choices for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-high-availability-faq |
| Select MySQL Flexible Server service tiers and storage | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-service-tiers-storage |
| Perform minimal-downtime MySQL migration to Azure flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-migrate-online |
| Plan and execute Azure MySQL major version upgrades | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-upgrade |
| Plan Azure Database for MySQL major version upgrades | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-upgrade-faq |
| Use mydumper/myloader to migrate large MySQL databases to Azure | https://learn.microsoft.com/en-us/azure/mysql/migrate/concepts-migrate-mydumper-myloader |
| Plan and execute on-premises MySQL migration to Azure Database for MySQL | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/01-mysql-migration-guide-intro |
| Assess on-premises MySQL for migration to Azure | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/03-assessment |
| Plan Azure Database for MySQL migration landing zone | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/04-planning |
| Choose migration methods to Azure Database for MySQL | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/05-migration-methods |
| Establish performance baselines for MySQL migration to Azure | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/07-performance-baselines |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Connect Azure Kubernetes Service to MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-aks |
| Design data-in replication into MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-data-in-replication |
| Design data-out replication from MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-data-out-replication |
| Use read replicas to scale MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-read-replicas |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Service limitations for Azure MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-limitations |
| Storage IOPS performance characteristics for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-storage-iops |
| Request quota increases for Azure MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-request-quota-increase |
| Restore deleted Azure MySQL flexible servers within retention limits | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-restore-dropped-server |
| Restart, stop, and start MySQL flexible server with stop-duration limits | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-restart-stop-start |

### Security
| Topic | URL |
|-------|-----|
| Use Private Link with Azure MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-networking-private-link |
| Configure public network access for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-networking-public |
| Configure private network access for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-networking-vnet |
| Configure Azure MySQL Private Link using Azure CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-networking-private-link-azure-cli |
| Deny public network access for Azure MySQL via portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-networking-private-link-deny-public-access |
| Secure Azure MySQL with Private Link using portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-networking-private-link-portal |
| Create and connect to MySQL Flexible Server with private access | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/quickstart-create-connect-server-vnet |
| Configure audit logging for MySQL flexible server via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-audit-logs |
| Use customer-managed keys for MySQL Flexible Server encryption | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-customer-managed-key |
| Understand Microsoft Entra authentication for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-entra-authentication |
| Create and manage MySQL Flexible Server users securely | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-how-to-create-users |
| Configure data encryption for MySQL Flexible Server using Azure CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-how-to-data-encryption-cli |
| Configure data encryption for MySQL Flexible Server in Azure portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-how-to-data-encryption-portal |
| Set up Microsoft Entra authentication for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-how-to-entra |
| Manage MySQL Flexible Server firewall rules via Azure CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-how-to-manage-firewall-cli |
| Manage MySQL Flexible Server firewall rules in Azure portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-how-to-manage-firewall-portal |
| Secure Azure Database for MySQL Flexible Server deployments | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-overview |
| TLS requirements and configuration for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-tls |
| Connect securely to MySQL Flexible Server using TLS | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-tls-how-to-connect |
| Handle root certificate rotation for Azure MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-tls-root-certificate-rotation |
| FAQ on root certificate rotation for Azure MySQL | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/security-tls-root-certificate-rotation-faq |
| Configure and analyze audit logs for Azure MySQL | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/tutorial-configure-audit |
| Secure Azure Database for MySQL during and after migration | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/13-security |

### Configuration
| Topic | URL |
|-------|-----|
| Use built-in stored procedures in MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-built-in-store-procedure |
| Configure monitoring and alerts for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-monitor-mysql |
| Monitoring metrics and logs reference for MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-monitor-mysql-reference |
| Configure server parameters for Azure MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-server-parameters |
| Set up metric-based alerts for Azure MySQL | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-alert-on-metric |
| Enable or disable zone redundant high availability via portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-configure-high-availability |
| Configure zone redundant high availability for Azure MySQL via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-configure-high-availability-cli |
| Configure MySQL flexible server parameters via Azure CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-configure-server-parameters-cli |
| Configure MySQL Flexible Server parameters in Azure portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-configure-server-parameters-portal |
| Configure data-in replication into Azure MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-data-in-replication |
| Configure data-out replication from Azure MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-data-out-replication |
| Configure scheduled maintenance windows for Azure MySQL | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-maintenance-portal |
| Configure private VNet connectivity for Azure MySQL via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-manage-virtual-network-cli |
| Configure private VNet connectivity for Azure MySQL via portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-manage-virtual-network-portal |
| Create and manage Azure MySQL read replicas using CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-read-replicas-cli |
| Create and manage Azure MySQL read replicas via portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-read-replicas-portal |
| List and download Azure MySQL server logs using CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-server-logs-cli |
| Enable and download Azure MySQL server logs via portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-server-logs-portal |
| List and modify MySQL flexible server parameters via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-change-server-parameters |
| Create MySQL flexible server with VNet private access via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-create-connect-private-access |
| Configure public access and firewall for MySQL flexible server via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-create-connect-public-access |
| Monitor and scale MySQL flexible server compute, storage, and IOPS | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-monitor-and-scale |
| Create and manage MySQL flexible server read replicas via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-read-replicas |
| Restore Azure MySQL flexible server to a point in time via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-restore-server |
| Configure same-zone high availability for MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-same-zone-ha |
| Configure slow query logging for MySQL flexible server via CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-slow-query-logs |
| Configure zone-redundant high availability for MySQL flexible server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/scripts/sample-cli-zone-redundant-ha |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Azure CLI commands to connect to MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/connect-azure-cli |
| Connect Java applications to MySQL Flexible Server with JDBC | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/connect-java |
| Connect Azure MySQL Flexible Server to Power BI Desktop | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/connect-with-powerbi-desktop |
| Migrate Amazon RDS MySQL to Azure flexible server using data-in replication | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-migrate-rds-mysql-data-in-replication |
| Store MySQL Flexible Server connection strings in Azure Key Vault | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/tutorial-add-mysql-connection-in-key-vault |
| Migrate on-premises or VM MySQL to Azure flexible server using Import CLI | https://learn.microsoft.com/en-us/azure/mysql/migrate/migrate-external-mysql-import-cli |
| Migrate MySQL data to Azure using MySQL Workbench | https://learn.microsoft.com/en-us/azure/mysql/migrate/mysql-on-premises-azure-db/09-data-migration-with-mysql-workbench |

### Deployment
| Topic | URL |
|-------|-----|
| Configure Azure Pipelines task for Azure MySQL deployments | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/azure-pipelines-deploy-database-task |
| Plan for scheduled maintenance on MySQL Flexible Server | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/concepts-maintenance |
| Create Azure Automation tasks for MySQL Flexible Server management | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/create-automation-tasks |
| Move Azure MySQL Flexible Server between regions using geo-restore | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-move-regions |
| Restore Azure MySQL Flexible Server from backup using CLI | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-restore-server-cli |
| Restore Azure MySQL Flexible Server from backup via portal | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/how-to-restore-server-portal |
| Use GitHub Actions to deploy changes to Azure MySQL | https://learn.microsoft.com/en-us/azure/mysql/flexible-server/quickstart-mysql-github-actions |