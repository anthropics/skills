---
name: azure-dedicated-hsm
description: Expert knowledge for Azure Dedicated HSM development including troubleshooting, decision making, architecture & design patterns, and security. Use when deploying Dedicated HSMs, configuring VNet/ExpressRoute, planning HA/failover, or migrating to Managed HSM, and other Azure Dedicated HSM related development tasks. Not for Azure Cloud Hsm (use azure-cloud-hsm), Azure Payment Hsm (use azure-payment-hsm), Azure Key Vault (use azure-key-vault), Azure Confidential Computing (use azure-confidential-computing).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Dedicated HSM Skill

This skill provides expert guidance for Azure Dedicated HSM. Covers troubleshooting, decision making, architecture & design patterns, and security. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L32-L37 | Diagnosing and fixing Azure Dedicated HSM deployment, configuration, usage, and support issues, including common errors and steps to resolve failed or misconfigured HSM instances. |
| Decision Making | L38-L44 | Guidance on Dedicated HSM retirement, choosing successors (Managed/Cloud HSM), and planning/migrating ExpressRoute IPs and HSM workloads to new SKUs or services. |
| Architecture & Design Patterns | L45-L51 | Guidance on designing Dedicated HSM deployments: sizing and topology, high availability and failover patterns, and secure networking (VNet, subnets, routing, and connectivity). |
| Security | L52-L56 | Physical security controls for Dedicated HSM devices and recommended security configurations, policies, and operational best practices for protecting keys and access. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure Dedicated HSM usage and support questions | https://learn.microsoft.com/en-us/azure/dedicated-hsm/faq |
| Troubleshoot Azure Dedicated HSM deployment and configuration issues | https://learn.microsoft.com/en-us/azure/dedicated-hsm/troubleshoot |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate Dedicated HSM ExpressRoute Basic IP to Standard SKU | https://learn.microsoft.com/en-us/azure/dedicated-hsm/migration-basic-standard |
| Plan migration from Azure Dedicated HSM to Managed or Cloud HSM | https://learn.microsoft.com/en-us/azure/dedicated-hsm/migration-guide |
| Understand Azure Dedicated HSM retirement and successors | https://learn.microsoft.com/en-us/azure/dedicated-hsm/overview |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design deployment architecture for Azure Dedicated HSM | https://learn.microsoft.com/en-us/azure/dedicated-hsm/deployment-architecture |
| Design high availability for Azure Dedicated HSM | https://learn.microsoft.com/en-us/azure/dedicated-hsm/high-availability |
| Plan networking architecture for Azure Dedicated HSM | https://learn.microsoft.com/en-us/azure/dedicated-hsm/networking |

### Security
| Topic | URL |
|-------|-----|
| Understand physical security of Azure Dedicated HSM devices | https://learn.microsoft.com/en-us/azure/dedicated-hsm/physical-security |
| Apply security best practices for Azure Dedicated HSM | https://learn.microsoft.com/en-us/azure/dedicated-hsm/secure-dedicated-hsm |