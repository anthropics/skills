---
name: azure-carbon-optimization
description: Expert knowledge for Azure Carbon Optimization development including troubleshooting, security, and integrations & coding patterns. Use when using Carbon Service REST API, Python exports, RBAC roles, emissions data quality, or dashboard issues, and other Azure Carbon Optimization related development tasks. Not for Azure Cost Management (use azure-cost-management), Azure Impact Reporting (use azure-impact-reporting), Azure Monitor (use azure-monitor), Azure Policy (use azure-policy).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure Carbon Optimization Skill

This skill provides expert guidance for Azure Carbon Optimization. Covers troubleshooting, security, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L31-L35 | Diagnosing and resolving common Azure Carbon Optimization issues, including data collection gaps, configuration problems, inaccurate emissions estimates, and troubleshooting dashboards or reports. |
| Security | L36-L40 | Setting up Azure RBAC roles and permissions so users and apps can securely access and manage Azure Carbon Optimization resources. |
| Integrations & Coding Patterns | L41-L45 | Using the Carbon Service REST API and Python scripts to programmatically export Azure emissions data, authenticate, query, and integrate carbon metrics into external systems. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot common Azure Carbon optimization issues | https://learn.microsoft.com/en-us/azure/carbon-optimization/troubleshooting |

### Security
| Topic | URL |
|-------|-----|
| Configure RBAC access for Azure Carbon optimization | https://learn.microsoft.com/en-us/azure/carbon-optimization/permissions |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Carbon Service REST API to export emissions data | https://learn.microsoft.com/en-us/azure/carbon-optimization/api-export-data |
| Export Azure carbon data via Python REST integration | https://learn.microsoft.com/en-us/azure/carbon-optimization/tutorial-export-python |