---
name: azure-resource-graph
description: Expert knowledge for Azure Resource Graph development including troubleshooting, best practices, decision making, limits & quotas, configuration, and integrations & coding patterns. Use when querying via CLI/PowerShell/REST, using GET/LIST vs Query APIs, shared queries, alerts, or Power BI, and other Azure Resource Graph related development tasks. Not for Azure Monitor (use azure-monitor), Azure Policy (use azure-policy), Azure Resource Manager (use azure-resource-manager), Azure Portal (use azure-portal).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-05-03"
  generator: "docs2skills/1.0.0"
---
# Azure Resource Graph Skill

This skill provides expert guidance for Azure Resource Graph. Covers troubleshooting, best practices, decision making, limits & quotas, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L34-L40 | Diagnosing and fixing Azure Resource Graph issues with alerts, query syntax/runtime errors, and Power BI connector connectivity, auth, and data refresh problems. |
| Best Practices | L41-L45 | Guidance on designing Azure Resource Graph queries to avoid throttling, including efficient patterns, batching, pagination, and performance-friendly query structures. |
| Decision Making | L46-L50 | Guidance on when to use Azure Resource Graph GET/LIST REST APIs vs the Query service, comparing capabilities, scenarios, and integration patterns. |
| Limits & Quotas | L51-L58 | Understanding ARG request limits, pagination behavior, handling large result sets, and implementing efficient paging (including with PowerShell) to avoid quota issues. |
| Configuration | L59-L66 | Configuring Resource Graph usage: keyboard shortcuts, supported resource types, and defining/deploying shared queries via Bicep and ARM templates. |
| Integrations & Coding Patterns | L67-L78 | Running Resource Graph queries via CLI, PowerShell, REST, Logic Apps, Power BI; creating shared queries and alerts; and retrieving resource change history for automation and reporting. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Resource Graph alert integration issues | https://learn.microsoft.com/en-us/azure/governance/resource-graph/troubleshoot/alerts |
| Resolve common Azure Resource Graph query errors | https://learn.microsoft.com/en-us/azure/governance/resource-graph/troubleshoot/general |
| Troubleshoot Azure Resource Graph Power BI connector problems | https://learn.microsoft.com/en-us/azure/governance/resource-graph/troubleshoot/power-bi-connector |

### Best Practices
| Topic | URL |
|-------|-----|
| Avoid Azure Resource Graph throttling with query patterns | https://learn.microsoft.com/en-us/azure/governance/resource-graph/concepts/guidance-for-throttled-requests |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose between ARG GET/LIST API and Query service | https://learn.microsoft.com/en-us/azure/governance/resource-graph/concepts/get-list-query-service-differences |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use Azure Resource Graph GET/LIST API quotas effectively | https://learn.microsoft.com/en-us/azure/governance/resource-graph/concepts/azure-resource-graph-get-list-api |
| Azure Resource Graph pagination behavior and limits | https://learn.microsoft.com/en-us/azure/governance/resource-graph/concepts/paging-results |
| Handle large Azure Resource Graph datasets and limits | https://learn.microsoft.com/en-us/azure/governance/resource-graph/concepts/work-with-data |
| Paginate Azure Resource Graph results with PowerShell | https://learn.microsoft.com/en-us/azure/governance/resource-graph/paginate-powershell |

### Configuration
| Topic | URL |
|-------|-----|
| Use keyboard shortcuts in Azure Resource Graph Explorer | https://learn.microsoft.com/en-us/azure/governance/resource-graph/reference/keyboard-shortcuts |
| Reference of Azure Resource Graph supported resource types | https://learn.microsoft.com/en-us/azure/governance/resource-graph/reference/supported-tables-resources |
| Define Azure Resource Graph shared queries using Bicep | https://learn.microsoft.com/en-us/azure/governance/resource-graph/shared-query-bicep |
| Deploy Azure Resource Graph shared queries with ARM templates | https://learn.microsoft.com/en-us/azure/governance/resource-graph/shared-query-template |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Create Azure Resource Graph-based alerts with Log Analytics | https://learn.microsoft.com/en-us/azure/governance/resource-graph/alerts-query-quickstart |
| Query Azure Resource Graph for resource change history | https://learn.microsoft.com/en-us/azure/governance/resource-graph/changes/get-resource-changes |
| Run Azure Resource Graph queries with Azure CLI | https://learn.microsoft.com/en-us/azure/governance/resource-graph/first-query-azurecli |
| Query Azure Resource Graph using PowerShell cmdlets | https://learn.microsoft.com/en-us/azure/governance/resource-graph/first-query-powershell |
| Call Azure Resource Graph via REST API | https://learn.microsoft.com/en-us/azure/governance/resource-graph/first-query-rest-api |
| Use Azure Resource Graph Power BI connector for queries | https://learn.microsoft.com/en-us/azure/governance/resource-graph/power-bi-connector-quickstart |
| Create Azure Resource Graph shared queries with CLI | https://learn.microsoft.com/en-us/azure/governance/resource-graph/shared-query-azure-cli |
| Create Azure Resource Graph shared queries with PowerShell | https://learn.microsoft.com/en-us/azure/governance/resource-graph/shared-query-azure-powershell |
| Automate Azure Resource Graph queries with Logic Apps | https://learn.microsoft.com/en-us/azure/governance/resource-graph/tutorials/logic-app-calling-arg |