---
name: azure-portal
description: Expert knowledge for Azure Portal development including troubleshooting, security, and configuration. Use when managing portal RBAC sharing, Intune/Entra mobile access, dashboard JSON, portal policies, or HAR diagnostics, and other Azure Portal related development tasks. Not for Azure Cloud Shell (use azure-cloud-shell), Azure Resource Manager (use azure-resource-manager), Azure Monitor (use azure-monitor), Azure Security (use azure-security).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-07"
  generator: "docs2skills/1.0.0"
---
# Azure Portal Skill

This skill provides expert guidance for Azure Portal. Covers troubleshooting, security, and configuration. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L31-L35 | How to collect browser network traces, console logs, HAR files, and diagnostics to investigate and report Azure portal performance or UI issues |
| Security | L36-L44 | Tenant-wide admin/security policies, RBAC-based dashboard sharing, mobile app protection and user management with Intune/Entra ID, and roles needed to manage Azure support requests. |
| Configuration | L45-L53 | Configuring Azure portal behavior: dashboard JSON/templates, keyboard shortcuts, URL allowlists, mobile app alerts, and built-in Azure Policy definitions for portal governance. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Capture browser traces and diagnostics for Azure portal issues | https://learn.microsoft.com/en-us/azure/azure-portal/capture-browser-trace |

### Security
| Topic | URL |
|-------|-----|
| Configure tenant-wide Azure portal admin policies | https://learn.microsoft.com/en-us/azure/azure-portal/admin-policies |
| Share Azure dashboards using Azure RBAC roles | https://learn.microsoft.com/en-us/azure/azure-portal/azure-portal-dashboard-share-access |
| Apply Intune MAM app protection policies to Azure mobile app | https://learn.microsoft.com/en-us/azure/azure-portal/mobile-app/intune-management |
| Manage Microsoft Entra ID users via Azure mobile app | https://learn.microsoft.com/en-us/azure/azure-portal/mobile-app/microsoft-entra-id |
| Manage Azure support requests and required roles | https://learn.microsoft.com/en-us/azure/azure-portal/supportability/how-to-manage-azure-support-request |

### Configuration
| Topic | URL |
|-------|-----|
| Programmatically create Azure dashboards from JSON templates | https://learn.microsoft.com/en-us/azure/azure-portal/azure-portal-dashboards-create-programmatically |
| Understand Azure dashboard JSON structure and properties | https://learn.microsoft.com/en-us/azure/azure-portal/azure-portal-dashboards-structure |
| Use global keyboard shortcuts in Azure portal | https://learn.microsoft.com/en-us/azure/azure-portal/azure-portal-keyboard-shortcuts |
| Allowlist Azure portal URLs on firewalls and proxies | https://learn.microsoft.com/en-us/azure/azure-portal/azure-portal-safelist-urls |
| Configure alerts and push notifications in Azure mobile app | https://learn.microsoft.com/en-us/azure/azure-portal/mobile-app/alerts-notifications |
| Reference built-in Azure Policy definitions for Azure portal | https://learn.microsoft.com/en-us/azure/azure-portal/policy-reference |