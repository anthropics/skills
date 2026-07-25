---
name: azure-extended-zones
description: Expert knowledge for Azure Extended Zones development including decision making, limits & quotas, security, and configuration. Use when setting up Extended Zones access, Azure Policy, Firewall, CMK disk encryption, or quota increase workflows, and other Azure Extended Zones related development tasks. Not for Azure Reliability (use azure-reliability), Azure Resiliency (use azure-resiliency), Azure Virtual Network (use azure-virtual-network), Azure Virtual WAN (use azure-virtual-wan).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-14"
  generator: "docs2skills/1.0.0"
---
# Azure Extended Zones Skill

This skill provides expert guidance for Azure Extended Zones. Covers decision making, limits & quotas, security, and configuration. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Decision Making | L32-L36 | Guidance on cost optimization for Azure Extended Zones, including when and how to buy reservations or savings plans, pricing tradeoffs, and purchase workflows. |
| Limits & Quotas | L37-L41 | How to view current Azure Extended Zones quotas and request quota increases using the Azure portal, including required steps and limits considerations. |
| Security | L42-L46 | How to encrypt Extended Zone VM disks using customer-managed keys, including setup steps, key vault integration, and security configuration details. |
| Configuration | L47-L52 | Configuring Extended Zones access and governance: registering subscriptions, creating custom Azure Policy, and deploying Azure Firewall within Extended Zones. |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose and purchase reservations or savings plans for Azure Extended Zones | https://learn.microsoft.com/en-us/azure/extended-zones/purchase-reservations-savings-plans |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Request Azure Extended Zones quota increases in portal | https://learn.microsoft.com/en-us/azure/extended-zones/request-quota-increase |

### Security
| Topic | URL |
|-------|-----|
| Encrypt Extended Zone VM disks with customer-managed keys | https://learn.microsoft.com/en-us/azure/extended-zones/key-vault-encrypt-azure-extended-zone-disk |

### Configuration
| Topic | URL |
|-------|-----|
| Create custom Azure Policy definitions for Extended Zones | https://learn.microsoft.com/en-us/azure/extended-zones/create-azure-policy |
| Configure Azure Firewall deployment in Extended Zones | https://learn.microsoft.com/en-us/azure/extended-zones/deploy-azure-firewall |
| Register subscriptions to access Azure Extended Zones | https://learn.microsoft.com/en-us/azure/extended-zones/request-access |