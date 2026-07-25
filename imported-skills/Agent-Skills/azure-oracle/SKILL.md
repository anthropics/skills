---
name: azure-oracle
description: Expert knowledge for Azure Oracle development including troubleshooting, security, configuration, and integrations & coding patterns. Use when configuring TDE with Key Vault, Oracle@Azure connectivity, AI DB VNets, Exadata log export, or Sentinel, and other Azure Oracle related development tasks. Not for Azure SQL Database (use azure-sql-database), Azure SQL Managed Instance (use azure-sql-managed-instance), SQL Server on Azure Virtual Machines (use azure-sql-virtual-machines), Azure VMware Solution (use azure-vmware-solution).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-05-17"
  generator: "docs2skills/1.0.0"
---
# Azure Oracle Skill

This skill provides expert guidance for Azure Oracle. Covers troubleshooting, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L32-L36 | Operational FAQs and fixes for common Oracle Database@Azure issues, including connectivity, performance, deployment, configuration, and known platform limitations. |
| Security | L37-L41 | Configuring Oracle Transparent Data Encryption (TDE) to use Azure Key Vault, including key management, integration steps, and security best practices. |
| Configuration | L42-L46 | Designing and configuring network architecture for Oracle AI Database@Azure clusters, including VNet peering, private endpoints, connectivity, and security considerations. |
| Integrations & Coding Patterns | L47-L50 | Configuring Oracle Exadata log export to Azure Monitor and Microsoft Sentinel, including pipelines, data formats, and setup for monitoring and security analytics. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Oracle Database@Azure known issues | https://learn.microsoft.com/en-us/azure/oracle/oracle-db/oracle-database-known-issues |

### Security
| Topic | URL |
|-------|-----|
| Configure Oracle TDE keys with Azure Key Vault | https://learn.microsoft.com/en-us/azure/oracle/oracle-db/manage-oracle-transparent-data-encryption-azure-key-vault |

### Configuration
| Topic | URL |
|-------|-----|
| Plan networking for Oracle AI Database@Azure clusters | https://learn.microsoft.com/en-us/azure/oracle/oracle-db/oracle-database-network-plan |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Oracle Exadata logs with Azure Monitor and Sentinel | https://learn.microsoft.com/en-us/azure/oracle/oracle-db/oracle-exadata-database-dedicated-infrastructure-logs |