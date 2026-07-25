---
name: azure-networking
description: Expert knowledge for Azure Networking development including troubleshooting, decision making, architecture & design patterns, limits & quotas, security, and configuration. Use when designing hub-spoke/VWAN VNets, planning IP ranges, securing with firewalls/NSGs, or using VNet Manager, and other Azure Networking related development tasks. Not for Azure Virtual Network (use azure-virtual-network), Azure Virtual Network Manager (use azure-virtual-network-manager), Azure Virtual WAN (use azure-virtual-wan), Azure Network Watcher (use azure-network-watcher).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Networking Skill

This skill provides expert guidance for Azure Networking. Covers troubleshooting, decision making, architecture & design patterns, limits & quotas, security, and configuration. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L34-L38 | Monitoring tools and step-by-step guidance to diagnose, troubleshoot, and resolve issues with Azure virtual networks, connectivity, performance, and other network resources. |
| Decision Making | L39-L54 | Guidance on choosing Azure network designs and services: load balancing, hybrid/multicloud connectivity, secure topologies, private access, and controlling internet ingress/egress. |
| Architecture & Design Patterns | L55-L67 | Designing secure Azure network topologies (hub-spoke, flat, multi-region, Virtual WAN), planning IP ranges/subnets, and applying common workload-specific network patterns. |
| Limits & Quotas | L68-L72 | Using Azure region round-trip latency stats to compare network performance between regions, plan deployments, and optimize app responsiveness based on measured latency. |
| Security | L73-L83 | Designing secure Azure networks: firewall and DDoS tiers, VM access, DNS/private name resolution, NSG/ASG rules, WAF protection, and policy-based compliance for network resources. |
| Configuration | L84-L87 | Configuring and centrally managing multiple VNets using Azure Virtual Network Manager, including network groups, connectivity, security rules, and governance at scale. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Monitor and troubleshoot Azure network resources | https://learn.microsoft.com/en-us/azure/networking/design-guide/monitor |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose Azure load balancing and app delivery options | https://learn.microsoft.com/en-us/azure/networking/design-guide/app-delivery |
| Plan cross-cloud connectivity with Azure networking | https://learn.microsoft.com/en-us/azure/networking/design-guide/cross-cloud |
| Plan cross-region and multicloud connectivity in Azure | https://learn.microsoft.com/en-us/azure/networking/design-guide/cross-region |
| Choose hybrid connectivity: VPN vs ExpressRoute | https://learn.microsoft.com/en-us/azure/networking/design-guide/hybrid-connectivity |
| Select Azure services for internet ingress | https://learn.microsoft.com/en-us/azure/networking/design-guide/internet-ingress |
| Plan lift-and-shift Azure network designs | https://learn.microsoft.com/en-us/azure/networking/design-guide/lift-and-shift |
| Design networks for migrate-and-modernize workloads | https://learn.microsoft.com/en-us/azure/networking/design-guide/migrate-modernize |
| Control outbound internet egress from Azure VNets | https://learn.microsoft.com/en-us/azure/networking/design-guide/outbound-egress |
| Select private access options for Azure PaaS | https://learn.microsoft.com/en-us/azure/networking/design-guide/private-platform-as-a-service |
| Decide when to use core Azure network foundation services | https://learn.microsoft.com/en-us/azure/networking/foundations/network-foundations-overview |
| Choose a secure Azure application delivery service | https://learn.microsoft.com/en-us/azure/networking/secure-application-delivery |
| Select a secure Azure network topology | https://learn.microsoft.com/en-us/azure/networking/secure-network-topology |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Deploy a Zero Trust virtual network for web apps | https://learn.microsoft.com/en-us/azure/networking/create-zero-trust-network-web-apps |
| Design a secure hub-spoke network for Azure web apps | https://learn.microsoft.com/en-us/azure/networking/cross-service-scenarios/design-secure-hub-spoke-network |
| Implement a single-workload flat VNet topology | https://learn.microsoft.com/en-us/azure/networking/design-guide/flat-network |
| Design hub-and-spoke network topology in Azure | https://learn.microsoft.com/en-us/azure/networking/design-guide/hub-spoke |
| Plan IP addressing for Azure virtual networks | https://learn.microsoft.com/en-us/azure/networking/design-guide/ip-planning |
| Design multi-region Azure network architectures | https://learn.microsoft.com/en-us/azure/networking/design-guide/multi-region |
| Architect global transit networks with Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/networking/design-guide/virtual-wan |
| Design Azure virtual networks and subnet layouts | https://learn.microsoft.com/en-us/azure/networking/design-guide/vnets-subnets |
| Apply common Azure networking workload patterns | https://learn.microsoft.com/en-us/azure/networking/design-guide/workload-patterns |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use Azure region round-trip latency statistics | https://learn.microsoft.com/en-us/azure/networking/azure-network-latency |

### Security
| Topic | URL |
|-------|-----|
| Design Azure Firewall tiers and traffic inspection | https://learn.microsoft.com/en-us/azure/networking/design-guide/azure-firewall |
| Select Azure DDoS protection tiers for networks | https://learn.microsoft.com/en-us/azure/networking/design-guide/ddos |
| Secure developer and admin access to Azure VMs | https://learn.microsoft.com/en-us/azure/networking/design-guide/developer-admin-access |
| Design secure DNS and private name resolution in Azure | https://learn.microsoft.com/en-us/azure/networking/design-guide/dns-security |
| Secure Azure VNets with NSGs and ASGs | https://learn.microsoft.com/en-us/azure/networking/design-guide/network-application-security-groups |
| Protect web apps with Azure Web Application Firewall | https://learn.microsoft.com/en-us/azure/networking/design-guide/web-application-firewall |
| Apply Azure Policy compliance controls to networking | https://learn.microsoft.com/en-us/azure/networking/security-controls-policy |

### Configuration
| Topic | URL |
|-------|-----|
| Manage Azure VNets centrally with Virtual Network Manager | https://learn.microsoft.com/en-us/azure/networking/design-guide/azure-virtual-network-manager |