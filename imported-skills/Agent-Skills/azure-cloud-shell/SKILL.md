---
name: azure-cloud-shell
description: Expert knowledge for Azure Cloud Shell development including troubleshooting, limits & quotas, and security. Use when configuring Cloud Shell storage accounts, private VNet access, session limits, concurrency, or RBAC roles, and other Azure Cloud Shell related development tasks. Not for Azure Portal (use azure-portal), Azure Virtual Machines (use azure-virtual-machines), Azure Kubernetes Service (AKS) (use azure-kubernetes-service), Azure App Service (use azure-app-service).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Cloud Shell Skill

This skill provides expert guidance for Azure Cloud Shell. Covers troubleshooting, limits & quotas, and security. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L31-L36 | Diagnosing and fixing common Cloud Shell errors, storage and connectivity issues, plus deployment and network problems when running Cloud Shell in private VNets. |
| Limits & Quotas | L37-L41 | Details on Cloud Shell session duration, resource and concurrency limits, required storage accounts, quotas, and how these constraints affect shell usage and persistence |
| Security | L42-L47 | Securing Cloud Shell storage: configuring shared storage safely, using private endpoints, and assigning RBAC roles for secure VNet-based Cloud Shell deployments. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot common Azure Cloud Shell issues and FAQs | https://learn.microsoft.com/en-us/azure/cloud-shell/faq-troubleshooting |
| Troubleshoot Cloud Shell deployments in private VNets | https://learn.microsoft.com/en-us/azure/cloud-shell/vnet/troubleshooting |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Azure Cloud Shell session and storage limits | https://learn.microsoft.com/en-us/azure/cloud-shell/overview |

### Security
| Topic | URL |
|-------|-----|
| Configure Cloud Shell storage for multiple users securely | https://learn.microsoft.com/en-us/azure/cloud-shell/security/how-to-support-multiple-users |
| Secure Cloud Shell storage with private endpoints | https://learn.microsoft.com/en-us/azure/cloud-shell/vnet/how-to-use-private-endpoint-storage |
| Assign RBAC roles for Cloud Shell VNet migration | https://learn.microsoft.com/en-us/azure/cloud-shell/vnet/migrate-container-permissions |