---
name: azure-expressroute
description: Expert knowledge for Azure ExpressRoute development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring ExpressRoute circuits/gateways, BGP/NAT routing, Global Reach, IPsec/MACsec, or automation via CLI/PowerShell, and other Azure ExpressRoute related development tasks. Not for Azure Internet Peering (use azure-internet-peering), Azure Peering Service (use azure-peering-service), Azure Virtual WAN (use azure-virtual-wan), Azure VPN Gateway (use azure-vpn-gateway).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure ExpressRoute Skill

This skill provides expert guidance for Azure ExpressRoute. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L42 | Troubleshooting ExpressRoute resiliency and asymmetric routing issues, plus FAQs on connectivity models, supported services, bandwidth, and pricing to resolve design or outage-related questions. |
| Best Practices | L43-L50 | Best practices for ExpressRoute: upgrading circuit bandwidth, using BGP communities in complex topologies, QoS for Skype voice, and migrating to new gateway hardware. |
| Decision Making | L51-L59 | Guidance on choosing ExpressRoute connectivity models, VNets and gateways, planning gateway SKU changes, and estimating/managing ExpressRoute costs. |
| Architecture & Design Patterns | L60-L71 | Designing resilient, highly available ExpressRoute architectures, including DR patterns, multi-circuit routing/Global Reach, VPN coexistence and failover, and using Microsoft peering for PSTN. |
| Limits & Quotas | L72-L80 | ExpressRoute limits on FastPath, gateways, routes, and provider circuits, including rate limiting, quotas, monitoring advertised routes, and FAQs on connectivity scale and constraints. |
| Security | L81-L90 | Encryption (IPsec, MACsec), NAT rules, RBAC roles, and security best practices for protecting ExpressRoute circuits and traffic |
| Configuration | L91-L125 | Configuring and managing ExpressRoute circuits, gateways, peering, routing, NAT/BGP, IPv6, Global Reach, monitoring, resiliency, and coexistence with VPN using portal, PowerShell, and CLI. |
| Integrations & Coding Patterns | L126-L132 | Automating ExpressRoute circuit creation/management with PowerShell or Azure CLI, and configuring a site-to-site VPN that runs over ExpressRoute Microsoft peering. |
| Deployment | L133-L140 | Guides for deploying and migrating ExpressRoute circuits/gateways, including ARM/Terraform provisioning, Direct SKUs, and moving to zone-redundant or new production circuits. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Test and validate resiliency of redundant ExpressRoute circuits | https://learn.microsoft.com/en-us/azure/expressroute/evaluate-circuit-resiliency |
| Diagnose and resolve asymmetric routing with ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-asymmetric-routing |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply best practices for upgrading ExpressRoute circuit bandwidth | https://learn.microsoft.com/en-us/azure/expressroute/about-upgrade-circuit-bandwidth |
| Manage complex ExpressRoute networks using BGP communities | https://learn.microsoft.com/en-us/azure/expressroute/bgp-communities |
| Apply QoS requirements for Skype voice over ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-qos |
| Migrate legacy ExpressRoute gateway connections to new hardware | https://learn.microsoft.com/en-us/azure/expressroute/howto-recreate-connections |

### Decision Making
| Topic | URL |
|-------|-----|
| Select and configure ExpressRoute virtual network gateways | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-about-virtual-network-gateways |
| Choose the right Azure ExpressRoute connectivity model | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-connectivity-models |
| Plan and execute ExpressRoute gateway SKU migration | https://learn.microsoft.com/en-us/azure/expressroute/gateway-migration |
| Plan and manage Azure ExpressRoute costs | https://learn.microsoft.com/en-us/azure/expressroute/plan-manage-cost |
| Choose VNet connectivity options over ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/virtual-network-connectivity-guidance |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design resilient Azure ExpressRoute network architectures | https://learn.microsoft.com/en-us/azure/expressroute/design-architecture-for-resiliency |
| Design disaster recovery with Azure ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/designing-for-disaster-recovery-with-expressroute-privatepeering |
| Architect high availability for Azure ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/designing-for-high-availability-with-expressroute |
| Connect multiple ExpressRoute circuits with Global Reach | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-global-reach |
| Optimize routing across multiple ExpressRoute circuits | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-optimize-routing |
| Architect coexisting ExpressRoute and S2S VPN connections | https://learn.microsoft.com/en-us/azure/expressroute/how-to-configure-coexisting-gateway-portal |
| Design S2S VPN backup for ExpressRoute private peering | https://learn.microsoft.com/en-us/azure/expressroute/use-s2s-vpn-as-backup-for-expressroute-privatepeering |
| Use ExpressRoute Microsoft peering for PSTN services | https://learn.microsoft.com/en-us/azure/expressroute/using-expressroute-for-microsoft-pstn |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Evaluate ExpressRoute FastPath features and limits | https://learn.microsoft.com/en-us/azure/expressroute/about-fastpath |
| Azure ExpressRoute FAQs on limits and connectivity details | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-faqs |
| Monitor ExpressRoute advertised routes to avoid limits | https://learn.microsoft.com/en-us/azure/expressroute/how-to-custom-route-alert |
| Understand rate limiting on provider-based ExpressRoute circuits | https://learn.microsoft.com/en-us/azure/expressroute/provider-rate-limit |
| ExpressRoute scalable gateway features and limits | https://learn.microsoft.com/en-us/azure/expressroute/scalable-gateway |

### Security
| Topic | URL |
|-------|-----|
| Use encryption options with Azure ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-about-encryption |
| Configure IPsec transport mode over ExpressRoute for Windows | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-ipsec-transport-private-windows |
| Configure MACsec security for Azure ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-macsec |
| Apply NAT requirements for Azure ExpressRoute circuits | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-nat |
| Roles and permissions for ExpressRoute resources | https://learn.microsoft.com/en-us/azure/expressroute/roles-permissions |
| Apply security best practices to Azure ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/secure-expressroute |

### Configuration
| Topic | URL |
|-------|-----|
| Establish private ExpressRoute peering to an Azure VNet | https://learn.microsoft.com/en-us/azure/expressroute/configure-expressroute-private-peering |
| Configure customer-controlled maintenance windows for ExpressRoute gateways | https://learn.microsoft.com/en-us/azure/expressroute/customer-controlled-gateway-maintenance |
| Configure BFD settings for Azure ExpressRoute private peering | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-bfd |
| Configure NAT on Cisco and Juniper for ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-config-samples-nat |
| Router interface and BGP configuration samples for ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-config-samples-routing |
| Configure Azure ExpressRoute virtual network gateways in portal | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-add-gateway-portal-resource-manager |
| Manage ExpressRoute virtual network gateways with PowerShell | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-add-gateway-resource-manager |
| Add IPv6 support to ExpressRoute private peering | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-add-ipv6 |
| Configure coexisting ExpressRoute and S2S VPN connections (classic) | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-coexist-classic |
| Configure coexisting ExpressRoute and S2S VPN gateways | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-coexist-resource-manager |
| Connect VNets to ExpressRoute circuits with PowerShell | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-linkvnet-arm |
| Link Azure VNets to ExpressRoute circuits via CLI | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-linkvnet-cli |
| Reset ExpressRoute circuit peerings with PowerShell | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-reset-peering |
| Reset ExpressRoute circuit peerings in Azure portal | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-reset-peering-portal |
| Configure ExpressRoute routing and peering with PowerShell | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-routing-arm |
| Configure ExpressRoute peering in Azure portal | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-routing-portal-resource-manager |
| Configure a scalable ExpressRoute gateway in portal | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-scalable-portal |
| Configure ExpressRoute Global Reach with PowerShell | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-set-global-reach |
| Configure ExpressRoute Global Reach in Azure portal | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-set-global-reach-portal |
| Configure routing requirements for Azure ExpressRoute circuits | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-routing |
| Configure Connection Monitor for ExpressRoute connectivity | https://learn.microsoft.com/en-us/azure/expressroute/how-to-configure-connection-monitor |
| Configure custom BGP communities for ExpressRoute private peering | https://learn.microsoft.com/en-us/azure/expressroute/how-to-configure-custom-bgp-communities |
| Configure custom BGP community values for ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/how-to-configure-custom-bgp-communities-portal |
| Configure ExpressRoute Traffic Collector and Log Analytics | https://learn.microsoft.com/en-us/azure/expressroute/how-to-configure-traffic-collector |
| Configure Azure ExpressRoute Direct resources | https://learn.microsoft.com/en-us/azure/expressroute/how-to-expressroute-direct-portal |
| Configure route filters for ExpressRoute Microsoft peering | https://learn.microsoft.com/en-us/azure/expressroute/how-to-routefilter-portal |
| Configure ExpressRoute peering using Azure CLI | https://learn.microsoft.com/en-us/azure/expressroute/howto-routing-cli |
| Use Azure Monitor metrics and logs for ExpressRoute | https://learn.microsoft.com/en-us/azure/expressroute/monitor-expressroute-reference |
| Configure rate limiting on ExpressRoute Direct circuits | https://learn.microsoft.com/en-us/azure/expressroute/rate-limit |
| Use Resiliency Insights for ExpressRoute gateways | https://learn.microsoft.com/en-us/azure/expressroute/resiliency-insights |
| Validate ExpressRoute gateway resiliency and failover | https://learn.microsoft.com/en-us/azure/expressroute/resiliency-validation |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Programmatically manage ExpressRoute circuits using Azure CLI | https://learn.microsoft.com/en-us/azure/expressroute/howto-circuit-cli |
| Create and manage ExpressRoute circuits using Azure CLI | https://learn.microsoft.com/en-us/azure/expressroute/howto-circuit-cli |
| Configure S2S VPN over ExpressRoute Microsoft peering | https://learn.microsoft.com/en-us/azure/expressroute/site-to-site-vpn-over-microsoft-peering |

### Deployment
| Topic | URL |
|-------|-----|
| Migrate production workloads to a new ExpressRoute circuit | https://learn.microsoft.com/en-us/azure/expressroute/circuit-migration |
| Understand ExpressRoute Direct SKUs and technical requirements | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-erdirect-about |
| Deploy an Azure ExpressRoute circuit via ARM template | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-circuit-resource-manager-template |
| Migrate to zone-redundant ExpressRoute gateway SKUs | https://learn.microsoft.com/en-us/azure/expressroute/expressroute-howto-gateway-migration-portal |
| Provision ExpressRoute circuit and gateway using Terraform | https://learn.microsoft.com/en-us/azure/expressroute/quickstart-create-expressroute-vnet-terraform |