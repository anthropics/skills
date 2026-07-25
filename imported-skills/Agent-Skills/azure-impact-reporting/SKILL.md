---
name: azure-impact-reporting
description: Expert knowledge for Azure Impact Reporting development including troubleshooting, configuration, and integrations & coding patterns. Use when wiring Impact Reporting to Monitor alerts, Logic Apps, Service Health, HPC guest health, or diagnostic logs, and other Azure Impact Reporting related development tasks. Not for Azure Carbon Optimization (use azure-carbon-optimization), Azure Cost Management (use azure-cost-management), Azure Monitor (use azure-monitor), Azure Policy (use azure-policy).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Impact Reporting Skill

This skill provides expert guidance for Azure Impact Reporting. Covers troubleshooting, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L31-L35 | Diagnosing and fixing Azure Impact Reporting connector failures and resolving Azure HPC Guest Health Reporting issues, errors, and data/health reporting problems. |
| Configuration | L36-L44 | Configuring Azure Impact Reporting and HPC guest health: setting up connectors, valid impact/report categories, guest health settings, and attaching diagnostic logs to reports. |
| Integrations & Coding Patterns | L45-L50 | Patterns and examples for integrating Impact Reporting with Azure Monitor alerts, Logic Apps, diagnostic logs, Service Health, and APIs (sending, attaching data, and viewing insights). |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Impact Reporting connectors | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/connectors-troubleshooting-guide |

### Configuration
| Topic | URL |
|-------|-----|
| Create Azure Impact Reporting connectors for alerts | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/create-azure-monitor-connector |
| Use valid HPC Guest Health impact categories | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/guest-health-impact-categories |
| Configure Azure HPC guest health reporting | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/guest-health-impact-report |
| Attach diagnostic logs to Azure guest health reports | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/guest-health-log-upload |
| Retrieve valid Azure Impact Reporting categories | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/view-impact-categories |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure Monitor alerts with Impact Reporting | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/azure-monitor-connector |
| Use Logic Apps to send Azure impact reports | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/creating-logic-app |
| Report Azure workload impact via Service Health and API | https://learn.microsoft.com/en-us/azure/azure-impact-reporting/report-impact |