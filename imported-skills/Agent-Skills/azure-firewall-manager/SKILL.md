---
name: azure-firewall-manager
description: Expert knowledge for Azure Firewall Manager development including best practices, decision making, security, and configuration. Use when managing DDoS plans, WAF policies, DNS proxy/FQDN rules, IP Groups, or secured virtual hub vs VNet, and other Azure Firewall Manager related development tasks. Not for Azure Firewall (use azure-firewall), Azure Virtual Network Manager (use azure-virtual-network-manager), Azure Network Function Manager (use azure-network-function-manager), Azure Networking (use azure-networking).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure Firewall Manager Skill

This skill provides expert guidance for Azure Firewall Manager. Covers best practices, decision making, security, and configuration. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Best Practices | L32-L36 | Details on how Azure Firewall evaluates and processes rules, rule collection groups, and policies, including priority, matching logic, and traffic filtering behavior |
| Decision Making | L37-L41 | Guidance on choosing between a secured virtual hub and a hub virtual network in Azure Firewall Manager, including architecture, security, routing, and management trade-offs. |
| Security | L42-L48 | Configuring Azure Firewall Manager for security: DDoS Protection plans, centralized WAF policy management, and threat intelligence-based traffic filtering. |
| Configuration | L49-L57 | Configuring Azure Firewall policies: DNS/DNS proxy, FQDN filtering, IP Groups, rule migration, rule hierarchy/inheritance, and securing private endpoint traffic in Virtual WAN. |

### Best Practices
| Topic | URL |
|-------|-----|
| Understand Azure Firewall rule processing order and logic | https://learn.microsoft.com/en-us/azure/firewall-manager/rule-processing |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose between secured virtual hub and hub virtual network | https://learn.microsoft.com/en-us/azure/firewall-manager/vhubs-and-vnets |

### Security
| Topic | URL |
|-------|-----|
| Configure Azure DDoS Protection plans via Firewall Manager | https://learn.microsoft.com/en-us/azure/firewall-manager/configure-ddos |
| Centrally manage WAF policies with Azure Firewall Manager | https://learn.microsoft.com/en-us/azure/firewall-manager/manage-web-application-firewall-policies |
| Configure threat intelligence-based filtering in Azure Firewall policy | https://learn.microsoft.com/en-us/azure/firewall-manager/threat-intelligence-settings |

### Configuration
| Topic | URL |
|-------|-----|
| Configure DNS servers and DNS proxy in Azure Firewall policy | https://learn.microsoft.com/en-us/azure/firewall-manager/dns-settings |
| Use FQDN filtering in Azure Firewall network rules | https://learn.microsoft.com/en-us/azure/firewall-manager/fqdn-filtering-network-rules |
| Configure and reuse IP Groups in Azure Firewall policy | https://learn.microsoft.com/en-us/azure/firewall-manager/ip-groups |
| Migrate Azure Firewall rules to Firewall policy with PowerShell | https://learn.microsoft.com/en-us/azure/firewall-manager/migrate-to-policy |
| Secure private endpoint traffic in Azure Virtual WAN with Firewall rules | https://learn.microsoft.com/en-us/azure/firewall-manager/private-link-inspection-secure-virtual-hub |
| Define rule hierarchy and inheritance with Azure Firewall policy | https://learn.microsoft.com/en-us/azure/firewall-manager/rule-hierarchy |