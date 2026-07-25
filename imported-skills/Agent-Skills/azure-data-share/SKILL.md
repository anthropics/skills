---
name: azure-data-share
description: Expert knowledge for Azure Data Share development including troubleshooting, decision making, security, configuration, and deployment. Use when estimating Data Share costs, securing invitations, fixing share errors, configuring datasets, or deploying across regions, and other Azure Data Share related development tasks. Not for Azure Data Box (use azure-data-box-family), Azure Data Explorer (use azure-data-explorer), Azure Data Factory (use azure-data-factory), Azure Open Datasets (use azure-open-datasets).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Data Share Skill

This skill provides expert guidance for Azure Data Share. Covers troubleshooting, decision making, security, configuration, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L37 | Diagnosing and fixing Azure Data Share invitation issues, common error codes/messages, permission and configuration problems when sending or accepting shares |
| Decision Making | L38-L42 | Guidance on estimating Azure Data Share costs, understanding pricing factors (shares, snapshots, storage), and planning budgets for data sharing scenarios. |
| Security | L43-L49 | Managing access and security for Data Share: RBAC roles, permissions, invitations/recipients, and configuring security controls for shared datasets. |
| Configuration | L50-L62 | How to set up and manage Azure Data Share: add datasets, configure mappings and storage (SQL, Synapse, Blob, Data Lake), enable monitoring, and deploy via PowerShell, ARM, or Bicep. |
| Deployment | L63-L67 | Guides for deploying Azure Data Share across regions, including disaster recovery setup, regional failover, and moving Data Share accounts between Azure regions. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot invitations and errors in Azure Data Share | https://learn.microsoft.com/en-us/azure/data-share/data-share-troubleshoot |

### Decision Making
| Topic | URL |
|-------|-----|
| Estimate and plan Azure Data Share pricing | https://learn.microsoft.com/en-us/azure/data-share/concepts-pricing |

### Security
| Topic | URL |
|-------|-----|
| Assign roles and permissions for Azure Data Share | https://learn.microsoft.com/en-us/azure/data-share/concepts-roles-permissions |
| Configure recipients and invitations in Azure Data Share | https://learn.microsoft.com/en-us/azure/data-share/how-to-add-recipients |
| Apply security controls for Azure Data Share | https://learn.microsoft.com/en-us/azure/data-share/security |

### Configuration
| Topic | URL |
|-------|-----|
| Add datasets to existing Azure Data Shares | https://learn.microsoft.com/en-us/azure/data-share/how-to-add-datasets |
| Configure dataset mappings for received Azure Data Shares | https://learn.microsoft.com/en-us/azure/data-share/how-to-configure-mapping |
| Configure Data Share with Azure SQL and Synapse | https://learn.microsoft.com/en-us/azure/data-share/how-to-share-from-sql |
| Configure Data Share with Blob and Data Lake Storage | https://learn.microsoft.com/en-us/azure/data-share/how-to-share-from-storage |
| Configure monitoring for Azure Data Share with Azure Monitor | https://learn.microsoft.com/en-us/azure/data-share/monitor-data-share |
| Reference metrics and logs for Azure Data Share monitoring | https://learn.microsoft.com/en-us/azure/data-share/monitor-data-share-reference |
| Use PowerShell scripts to manage Azure Data Share | https://learn.microsoft.com/en-us/azure/data-share/samples-powershell |
| Configure Azure Data Share using ARM templates | https://learn.microsoft.com/en-us/azure/data-share/share-your-data-arm |
| Define Azure Data Share with Bicep templates | https://learn.microsoft.com/en-us/azure/data-share/share-your-data-bicep |

### Deployment
| Topic | URL |
|-------|-----|
| Set up disaster recovery for Azure Data Share | https://learn.microsoft.com/en-us/azure/data-share/disaster-recovery |
| Move Azure Data Share accounts to another region | https://learn.microsoft.com/en-us/azure/data-share/move-to-new-region |