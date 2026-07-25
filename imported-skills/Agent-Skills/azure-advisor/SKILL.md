---
name: azure-advisor
description: Expert knowledge for Azure Advisor development including best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. Use when managing Advisor alerts, digests, recommendation states, Resource Graph queries, or RBAC access, and other Azure Advisor related development tasks. Not for Azure Cost Management (use azure-cost-management), Azure Monitor (use azure-monitor), Azure Policy (use azure-policy), Azure Security (use azure-security).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Advisor Skill

This skill provides expert guidance for Azure Advisor. Covers best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L34-L46 | Guidance on using Azure Advisor for Well-Architected assessments and bulk fixes to optimize cost, performance, reliability, and operational excellence across VMs and other services. |
| Decision Making | L47-L55 | Using Advisor workbooks and critical risk views to assess reliability, plan migrations, and estimate cost impact of Azure Advisor recommendations across key resources |
| Limits & Quotas | L56-L60 | Advisor feature availability, limits, and differences when running in Azure sovereign clouds (e.g., Azure Government, China), including which recommendations are supported. |
| Security | L61-L65 | Managing Azure Advisor permissions, roles, and RBAC settings so users and apps have appropriate access to Advisor recommendations and data |
| Configuration | L66-L76 | Configuring Azure Advisor alerts, digests, and recommendation states via portal, ARM/Bicep, tags, and workbooks to control how and when recommendations are delivered and viewed. |
| Integrations & Coding Patterns | L77-L82 | Querying Azure Advisor data via Resource Graph, using sample Kusto queries, and integrating Advisor MCP tools with AI/LLM clients for automated insights |

### Best Practices
| Topic | URL |
|-------|-----|
| Run Well-Architected assessments in Azure Advisor | https://learn.microsoft.com/en-us/azure/advisor/advisor-assessments |
| Optimize VM and VMSS costs using Azure Advisor | https://learn.microsoft.com/en-us/azure/advisor/advisor-cost-recommendations |
| Calculate and export Azure Advisor cost savings | https://learn.microsoft.com/en-us/azure/advisor/advisor-how-to-calculate-total-cost-savings |
| Improve high-usage VM performance with Azure Advisor | https://learn.microsoft.com/en-us/azure/advisor/advisor-how-to-performance-resize-high-usage-vm-recommendations |
| Use Quick Fix for bulk remediation of Advisor recommendations | https://learn.microsoft.com/en-us/azure/advisor/advisor-quick-fix |
| Apply Azure Advisor cost recommendations across services | https://learn.microsoft.com/en-us/azure/advisor/advisor-reference-cost-recommendations |
| Apply Azure Advisor operational excellence recommendations | https://learn.microsoft.com/en-us/azure/advisor/advisor-reference-operational-excellence-recommendations |
| Leverage Azure Advisor performance recommendations | https://learn.microsoft.com/en-us/azure/advisor/advisor-reference-performance-recommendations |
| Apply Azure Advisor reliability recommendations | https://learn.microsoft.com/en-us/azure/advisor/advisor-reference-reliability-recommendations |

### Decision Making
| Topic | URL |
|-------|-----|
| Use Azure Advisor Critical Risks for key resources | https://learn.microsoft.com/en-us/azure/advisor/advisor-critical-risks |
| Assess cost impact of Azure Advisor recommendations | https://learn.microsoft.com/en-us/azure/advisor/advisor-how-to-evaluate-cost-implications-of-recommendations |
| Analyze and optimize Azure costs with the Advisor workbook | https://learn.microsoft.com/en-us/azure/advisor/advisor-workbook-cost-optimization |
| Evaluate application reliability using the Advisor workbook | https://learn.microsoft.com/en-us/azure/advisor/advisor-workbook-reliability |
| Use Advisor Service Retirement workbook for migration planning | https://learn.microsoft.com/en-us/azure/advisor/advisor-workbook-service-retirement |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure Advisor feature limits in sovereign clouds | https://learn.microsoft.com/en-us/azure/advisor/advisor-sovereign-clouds |

### Security
| Topic | URL |
|-------|-----|
| Configure Azure Advisor roles and access control | https://learn.microsoft.com/en-us/azure/advisor/permissions |

### Configuration
| Topic | URL |
|-------|-----|
| Create Azure Advisor alerts with ARM templates | https://learn.microsoft.com/en-us/azure/advisor/advisor-alerts-arm |
| Define Azure Advisor alert rules using Bicep | https://learn.microsoft.com/en-us/azure/advisor/advisor-alerts-bicep |
| Configure Azure Advisor alerts in the Azure portal | https://learn.microsoft.com/en-us/azure/advisor/advisor-alerts-portal |
| Configure Azure Advisor recommendation state management | https://learn.microsoft.com/en-us/azure/advisor/advisor-azure-state-management |
| Configure periodic Azure Advisor recommendation digests | https://learn.microsoft.com/en-us/azure/advisor/advisor-recommendations-digest |
| Filter Azure Advisor recommendations by resource tags | https://learn.microsoft.com/en-us/azure/advisor/advisor-tag-filtering |
| Use Azure Advisor workbook templates for insights | https://learn.microsoft.com/en-us/azure/advisor/advisor-workbooks |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Query Azure Advisor data with Resource Graph | https://learn.microsoft.com/en-us/azure/advisor/advisor-azure-resource-graph |
| Integrate Azure Advisor MCP tools with AI clients | https://learn.microsoft.com/en-us/azure/advisor/advisor-mcp-tools |
| Use Resource Graph sample queries for Azure Advisor data | https://learn.microsoft.com/en-us/azure/advisor/resource-graph-samples |