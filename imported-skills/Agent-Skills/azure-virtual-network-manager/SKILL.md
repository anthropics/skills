---
name: azure-virtual-network-manager
description: Expert knowledge for Azure Virtual Network Manager development including troubleshooting, limits & quotas, security, configuration, and integrations & coding patterns. Use when managing IPAM pools, network groups, hub-spoke routing, security admin rules, or Resource Graph queries, and other Azure Virtual Network Manager related development tasks. Not for Azure Virtual Network (use azure-virtual-network), Azure Virtual WAN (use azure-virtual-wan), Azure Network Watcher (use azure-network-watcher), Azure Networking (use azure-networking).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Virtual Network Manager Skill

This skill provides expert guidance for Azure Virtual Network Manager. Covers troubleshooting, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L38 | Diagnosing and fixing common Azure Virtual Network Manager issues, including deployment/configuration errors and verifying that AVNM-applied network configurations work as intended. |
| Limits & Quotas | L39-L43 | IPAM features, supported regions, and key Azure Virtual Network Manager limits (scale, resources, configurations) that affect design and deployment decisions. |
| Security | L44-L56 | Configuring and enforcing AVNM security admin rules to block or restrict traffic (including high‑risk ports), using network groups, simulating rule impact, and securing hub‑and‑spoke virtual networks. |
| Configuration | L57-L70 | Configuring AVNM: IPAM pools, network groups, cross-tenant connections, event logs, UDRs/hub-spoke routing, and reachability analysis with CLI, portal, Bicep, and Azure Policy. |
| Integrations & Coding Patterns | L71-L74 | Using Azure Resource Graph to query, filter, and report on Azure Virtual Network Manager resources, configurations, and deployments at scale across subscriptions |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot common Azure Virtual Network Manager issues | https://learn.microsoft.com/en-us/azure/virtual-network-manager/common-issues |
| Verify and troubleshoot AVNM-applied configurations | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-view-applied-configurations |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure Virtual Network Manager limitations | https://learn.microsoft.com/en-us/azure/virtual-network-manager/concept-limitations |

### Security
| Topic | URL |
|-------|-----|
| Enforce virtual network security with AVNM admin rules | https://learn.microsoft.com/en-us/azure/virtual-network-manager/concept-enforcement |
| Apply AVNM security admin rules using network groups | https://learn.microsoft.com/en-us/azure/virtual-network-manager/concept-security-admin-rules-network-group |
| Use security admin rules in Azure Virtual Network Manager | https://learn.microsoft.com/en-us/azure/virtual-network-manager/concept-security-admins |
| Secure high-risk ports with AVNM admin rules | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-block-high-risk-ports |
| Block network traffic with AVNM security admin rules (portal) | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-block-network-traffic-portal |
| Block outbound traffic with AVNM security rules (PowerShell) | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-block-network-traffic-powershell |
| Create AVNM security admin rules using network groups | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-create-security-admin-rule-network-group |
| Simulate Azure Virtual Network Manager security admin rules | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-simulate-security-admin-rules |
| Secure Azure hub-and-spoke networks with AVNM | https://learn.microsoft.com/en-us/azure/virtual-network-manager/tutorial-create-secured-hub-and-spoke |

### Configuration
| Topic | URL |
|-------|-----|
| Automate VNet IP address management with AVNM IPAM pools | https://learn.microsoft.com/en-us/azure/virtual-network-manager/automate-ip-address-management-ipam-sample |
| Configure AVNM network groups with Azure Policy | https://learn.microsoft.com/en-us/azure/virtual-network-manager/concept-azure-policy-integration |
| Deploy Azure Virtual Network Manager IPAM pools with Bicep | https://learn.microsoft.com/en-us/azure/virtual-network-manager/deploy-ip-address-management-pools-bicep |
| Configure cross-tenant connections with Azure CLI | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-configure-cross-tenant-cli |
| Configure cross-tenant connections in AVNM via portal | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-configure-cross-tenant-portal |
| Configure Azure Virtual Network Manager event logs and destinations | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-configure-event-logs |
| Configure user-defined routes with Azure Virtual Network Manager | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-create-user-defined-route |
| Define dynamic AVNM network groups using Azure Policy | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-define-network-group-membership-azure-policy |
| Manage UDRs across multiple AVNM hub-and-spoke topologies | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-manage-user-defined-routes-multiple-hub-spoke-topologies |
| Use Virtual Network Verifier to analyze VM reachability in AVNM | https://learn.microsoft.com/en-us/azure/virtual-network-manager/how-to-verify-reachability-with-virtual-network-verifier |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Query Azure Virtual Network Manager with Azure Resource Graph | https://learn.microsoft.com/en-us/azure/virtual-network-manager/query-azure-resource-graph |