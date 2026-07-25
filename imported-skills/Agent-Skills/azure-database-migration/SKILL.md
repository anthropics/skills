---
name: azure-database-migration
description: Expert knowledge for Azure Database Migration service development including troubleshooting, decision making, limits & quotas, security, integrations & coding patterns, and deployment. Use when planning Azure DMS migrations for SQL/MySQL/PostgreSQL, SSIS to Azure SQL/MI, or scripted PowerShell workflows, and other Azure Database Migration service related development tasks. Not for Azure Migrate (use azure-migrate), Azure SQL Database (use azure-sql-database), Azure SQL Managed Instance (use azure-sql-managed-instance), SQL Server on Azure Virtual Machines (use azure-sql-virtual-machines).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-05-17"
  generator: "docs2skills/1.0.0"
---
# Azure Database Migration service Skill

This skill provides expert guidance for Azure Database Migration service. Covers troubleshooting, decision making, limits & quotas, security, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L34-L40 | Diagnosing and fixing common Azure DMS and DMS classic migration failures, including connectivity to source databases, configuration issues, and typical error messages. |
| Decision Making | L41-L46 | Choosing the right Azure DMS tool and scenario for your source/target databases, plus FAQs on supported migrations, limitations, and how to use Azure Database Migration Service. |
| Limits & Quotas | L47-L55 | Migration-specific limits, unsupported features, and constraints when using Azure DMS to move MySQL, PostgreSQL, SQL Managed Instance, MongoDB, and hybrid deployments. |
| Security | L56-L61 | Security guidance for Azure DMS migrations, including SQL best practices (network, auth, encryption) and configuring custom RBAC roles for MySQL migration scenarios. |
| Integrations & Coding Patterns | L62-L66 | Automating MySQL-to-Azure Database for MySQL migrations using Azure Database Migration Service with PowerShell scripts, parameters, and end-to-end workflow examples. |
| Deployment | L67-L71 | Using Azure DMS to redeploy or migrate SSIS packages to Azure SQL Database or SQL Managed Instance, including configuration steps and migration considerations. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure Database Migration Service issues | https://learn.microsoft.com/en-us/azure/dms/faq |
| Troubleshoot common Azure DMS classic migration issues | https://learn.microsoft.com/en-us/azure/dms/known-issues-troubleshooting-dms |
| Fix Azure DMS source database connectivity problems | https://learn.microsoft.com/en-us/azure/dms/known-issues-troubleshooting-dms-source-connectivity |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose database migration tools with the Azure DMS matrix | https://learn.microsoft.com/en-us/azure/dms/dms-tools-matrix |
| Select supported Azure DMS migration scenarios | https://learn.microsoft.com/en-us/azure/dms/resource-scenario-status |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review migration limitations to Azure Database for MySQL | https://learn.microsoft.com/en-us/azure/dms/known-issues-azure-mysql-fs-online |
| Review online PostgreSQL to Azure Database for PostgreSQL migration limitations | https://learn.microsoft.com/en-us/azure/dms/known-issues-azure-postgresql-online |
| Review online migration limits to Azure SQL Managed Instance | https://learn.microsoft.com/en-us/azure/dms/known-issues-azure-sql-db-managed-instance-online |
| Understand Azure DMS hybrid mode limitations and issues | https://learn.microsoft.com/en-us/azure/dms/known-issues-dms-hybrid-mode |
| Review MongoDB to Azure Cosmos DB migration limitations with DMS | https://learn.microsoft.com/en-us/azure/dms/known-issues-mongo-cosmos-db |

### Security
| Topic | URL |
|-------|-----|
| Apply security best practices for DMS SQL migrations | https://learn.microsoft.com/en-us/azure/dms/dms-security-best-practices |
| Configure custom RBAC roles for MySQL migrations in DMS | https://learn.microsoft.com/en-us/azure/dms/resource-custom-roles-mysql-database-migration-service |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Automate MySQL to Azure MySQL migration with DMS PowerShell | https://learn.microsoft.com/en-us/azure/dms/migrate-mysql-to-azure-mysql-powershell |

### Deployment
| Topic | URL |
|-------|-----|
| Redeploy SSIS packages to Azure SQL Database with DMS | https://learn.microsoft.com/en-us/azure/dms/how-to-migrate-ssis-packages |
| Migrate SSIS packages to Azure SQL Managed Instance with DMS | https://learn.microsoft.com/en-us/azure/dms/how-to-migrate-ssis-packages-managed-instance |