---
name: azure-virtual-wan
description: Expert knowledge for Azure Virtual WAN development including troubleshooting, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when designing VWAN hubs, P2S/Always On VPN, BGP/IPsec routing, NVAs/firewalls, or ExpressRoute/SD-WAN integration, and other Azure Virtual WAN related development tasks. Not for Azure Virtual Network (use azure-virtual-network), Azure Virtual Network Manager (use azure-virtual-network-manager), Azure VPN Gateway (use azure-vpn-gateway), Azure ExpressRoute (use azure-expressroute).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Virtual WAN Skill

This skill provides expert guidance for Azure Virtual WAN. Covers troubleshooting, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L41 | Diagnosing and fixing Virtual WAN issues, including P2S VPN client prerequisite checks, connectivity problems, and using built-in tools and diagnostics for troubleshooting. |
| Decision Making | L42-L50 | Guidance on planning and choosing Virtual WAN designs: NVAs in hubs, VPN client migrations, upgrading Basic→Standard, and selecting partners and hub locations. |
| Architecture & Design Patterns | L51-L78 | Designing and troubleshooting Azure Virtual WAN architectures: routing patterns, hub-and-spoke and global transit designs, security/firewall integration, SD-WAN, isolation, DR, and Microsoft 365 connectivity. |
| Limits & Quotas | L79-L85 | Limits and design guidance for Virtual WAN: P2S client pool sizing, hub routing/throughput caps, and using Private Link endpoints within scale and quota constraints. |
| Security | L86-L95 | Configuring secure P2S VPN access in Virtual WAN using Microsoft Entra ID (MFA, OpenVPN, custom app IDs), Azure VPN Client setup/migration, and hub roles/permissions. |
| Configuration | L96-L150 | Configuring Virtual WAN hubs, routing, BGP/NAT/IPsec, NVAs/Firewalls, and P2S/Always On VPN (certs, Entra ID, client profiles, user groups, IP pools) plus monitoring and path selection. |
| Integrations & Coding Patterns | L151-L157 | PowerShell and automation patterns for integrating Virtual WAN with ExpressRoute, SD-WAN/VPN CPEs, RADIUS user groups, and sharing services via Azure Private Link |
| Deployment | L158-L162 | PowerShell-based deployment of cross-tenant VNet connections to Virtual WAN hubs and step-by-step setup of integrated NVAs inside Virtual WAN hubs. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Use Azure VPN Client prerequisites check for P2S | https://learn.microsoft.com/en-us/azure/virtual-wan/azure-vpn-client-prerequisites-check |
| Troubleshooting tools and diagnostics for Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-troubleshooting-overview |

### Decision Making
| Topic | URL |
|-------|-----|
| Use Network Virtual Appliances in a Virtual WAN hub | https://learn.microsoft.com/en-us/azure/virtual-wan/about-nva-hub |
| Plan migration from Azure VPN Client for Linux | https://learn.microsoft.com/en-us/azure/virtual-wan/azure-vpn-client-linux-retirement |
| Migrate P2S VPN clients to Microsoft-registered Entra app | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-entra-gateway-update |
| Decide and perform upgrade from Basic to Standard Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/upgrade-virtual-wan |
| Select Azure Virtual WAN partners and hub locations | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-locations-partners |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Routing intent patterns to secure internet access | https://learn.microsoft.com/en-us/azure/virtual-wan/about-internet-routing |
| Choose routing preference in Azure Virtual WAN hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/about-virtual-hub-routing-preference |
| Design disaster recovery architecture for Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/disaster-recovery-design |
| Design selective Azure Firewall bypass in secure hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/firewall-custom-bypass |
| Combine Azure Firewall and spoke NVAs with static routing | https://learn.microsoft.com/en-us/azure/virtual-wan/hybrid-firewall-spoke-static |
| Route traffic to indirect spokes with Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/indirect-spoke-architecture |
| Architect China interconnect using Virtual WAN secured hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/interconnect-china |
| Migrate hub-and-spoke networks to Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/migrate-from-hub-spoke-topology |
| Deep dive into Azure Virtual WAN routing behavior | https://learn.microsoft.com/en-us/azure/virtual-wan/routing-deep-dive |
| Use routing intent with static routes in Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/routing-intent-static-route |
| Connect Microsoft 365 via ExpressRoute private peering in Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/scenario-365-expressroute-private |
| Implement any-to-any routing with Virtual WAN hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/scenario-any-to-any |
| Configure BGP peering with Azure Virtual WAN hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/scenario-bgp-peering-hub |
| Design Virtual WAN routing to isolate VNets | https://learn.microsoft.com/en-us/azure/virtual-wan/scenario-isolate-vnets |
| Configure custom VNet isolation with Virtual WAN routing | https://learn.microsoft.com/en-us/azure/virtual-wan/scenario-isolate-vnets-custom |
| Secure Application Gateway traffic via Virtual WAN secured hub | https://learn.microsoft.com/en-us/azure/virtual-wan/scenario-secured-hub-app-gateway |
| Route to shared services VNets using Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/scenario-shared-services-vnet |
| Integrate private SD-WAN with Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/sd-wan-connectivity-architecture |
| Inspect north-south traffic with spoke NVAs in Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/spoke-inspection-north-south |
| Design static routing patterns in Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/static-routes |
| Route Virtual WAN traffic through Azure Firewall | https://learn.microsoft.com/en-us/azure/virtual-wan/static-routes-firewall-basic |
| Select third-party integrations in Virtual WAN hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/third-party-integrations |
| Choose connectivity options between Azure Virtual WANs | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-connectivity |
| Design global transit network architecture with Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-global-transit-network-architecture |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Plan P2S client address pools and scale for Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/about-client-address-pools |
| Virtual hub routing capabilities and throughput limits | https://learn.microsoft.com/en-us/azure/virtual-wan/about-virtual-hub-routing |
| Configure Azure Virtual WAN Private Link endpoints | https://learn.microsoft.com/en-us/azure/virtual-wan/howto-private-link |

### Security
| Topic | URL |
|-------|-----|
| Secure P2S client access to spoke VNets with Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/manage-secure-access-resources-spoke-p2s |
| Enable Microsoft Entra multifactor authentication for VPN users | https://learn.microsoft.com/en-us/azure/virtual-wan/openvpn-azure-ad-mfa |
| Configure a Microsoft Entra tenant for Virtual WAN P2S OpenVPN | https://learn.microsoft.com/en-us/azure/virtual-wan/openvpn-azure-ad-tenant |
| Configure Entra-based OpenVPN auth with multiple apps | https://learn.microsoft.com/en-us/azure/virtual-wan/openvpn-azure-ad-tenant-multi-app |
| Configure Azure VPN Client for P2S with Microsoft Entra ID | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-entra-vpn-client-windows |
| Assign roles and permissions for Azure Virtual WAN hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/roles-permissions |

### Configuration
| Topic | URL |
|-------|-----|
| Work with Azure Virtual WAN User VPN client profiles | https://learn.microsoft.com/en-us/azure/virtual-wan/about-vpn-profile-download |
| Configure optional Azure VPN Client OpenVPN settings | https://learn.microsoft.com/en-us/azure/virtual-wan/azure-vpn-client-optional-configurations |
| Generate P2S User VPN certificates using PowerShell | https://learn.microsoft.com/en-us/azure/virtual-wan/certificates-point-to-site |
| Generate P2S User VPN certificates using MakeCert | https://learn.microsoft.com/en-us/azure/virtual-wan/certificates-point-to-site-makecert |
| Configure BGP peering to NVA in Virtual WAN hub | https://learn.microsoft.com/en-us/azure/virtual-wan/create-bgp-peering-hub-portal |
| Configure BGP peering from Virtual WAN hub to NVA (PowerShell) | https://learn.microsoft.com/en-us/azure/virtual-wan/create-bgp-peering-hub-powershell |
| View effective routes for a Virtual WAN hub | https://learn.microsoft.com/en-us/azure/virtual-wan/effective-routes-virtual-hub |
| Configure and understand Virtual WAN gateway settings | https://learn.microsoft.com/en-us/azure/virtual-wan/gateway-settings |
| Configure forced tunneling for Virtual WAN P2S VPN | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-forced-tunnel |
| Manage IP configurations for NVAs in Virtual WAN hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-network-virtual-appliance-add-ip-configurations |
| Configure DNAT for Virtual WAN integrated NVAs | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-network-virtual-appliance-inbound |
| Configure Palo Alto Cloud NGFW in Azure Virtual WAN hub | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-palo-alto-cloud-ngfw |
| Configure Virtual WAN hub routing policies (intent) | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-routing-policies |
| Configure Azure Virtual WAN virtual hub routing | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-virtual-hub-routing |
| Configure virtual hub routing with Azure PowerShell | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-virtual-hub-routing-powershell |
| Set virtual hub routing preference with PowerShell | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-virtual-hub-routing-preference-powershell |
| Configure Always On VPN device tunnel for Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/howto-always-on-device-tunnel |
| Configure Always On VPN user tunnel for Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/howto-always-on-user-tunnel |
| Configure Azure Firewall in a Virtual WAN secured hub | https://learn.microsoft.com/en-us/azure/virtual-wan/howto-firewall |
| Set virtual hub routing preference in Azure portal | https://learn.microsoft.com/en-us/azure/virtual-wan/howto-virtual-hub-routing-preference |
| Configure Azure Virtual WAN hub settings and scale units | https://learn.microsoft.com/en-us/azure/virtual-wan/hub-settings |
| Reference monitoring metrics and logs for Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/monitor-virtual-wan-reference |
| Configure VPN NAT rules on Azure Virtual WAN gateways | https://learn.microsoft.com/en-us/azure/virtual-wan/nat-rules-vpn-gateway |
| Configure VPN NAT rules for Virtual WAN using PowerShell | https://learn.microsoft.com/en-us/azure/virtual-wan/nat-rules-vpn-gateway-powershell |
| Use next hop IP and BGP peering in Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/next-hop-ip |
| Configure Azure path selection across multiple WAN links | https://learn.microsoft.com/en-us/azure/virtual-wan/path-selection-multiple-links |
| Manage Virtual WAN VPN gateway root certificate migration | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-about-gateway-certificate-migration |
| Generate P2S User VPN certificates on Linux with OpenSSL | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-certificates-linux-openssl |
| Generate P2S User VPN certificates on Linux with strongSwan | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-certificates-linux-strongswan |
| Configure Virtual WAN P2S VPN with Entra ID and registered client | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-entra-gateway |
| Configure custom Entra app ID for P2S VPN authentication | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-entra-register-custom-app |
| Configure Azure VPN Client with Entra ID on Linux | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-entra-vpn-client-linux |
| Configure Azure VPN Client with Entra ID on macOS | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-entra-vpn-client-mac |
| Reference IPsec policy combinations for Virtual WAN P2S | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-ipsec |
| Configure P2S VPN address pools with PowerShell in Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/point-to-site-user-groups-powershell |
| Understand and configure Virtual WAN Route-maps | https://learn.microsoft.com/en-us/azure/virtual-wan/route-maps-about |
| Drop inbound branch routes with Virtual WAN Route-maps | https://learn.microsoft.com/en-us/azure/virtual-wan/route-maps-drop-inbound-branch-sites |
| Configure Route-maps for Azure Virtual WAN hubs | https://learn.microsoft.com/en-us/azure/virtual-wan/route-maps-how-to |
| Summarize routes leaving Virtual WAN using Route-maps | https://learn.microsoft.com/en-us/azure/virtual-wan/route-maps-how-to-summarize-routes-leaving-your-virtual-wan |
| Prepend routes using Virtual WAN Route-maps | https://learn.microsoft.com/en-us/azure/virtual-wan/route-maps-prepend-routes |
| Summarize NVA spoke routes with Virtual WAN Route-maps | https://learn.microsoft.com/en-us/azure/virtual-wan/route-maps-summarize-from-device-spoke-vnet-nva |
| Tag routes using Virtual WAN Route-maps | https://learn.microsoft.com/en-us/azure/virtual-wan/route-maps-tag-routes |
| Understand user groups and IP pools for P2S VPN | https://learn.microsoft.com/en-us/azure/virtual-wan/user-groups-about |
| Configure P2S VPN user groups and IP pools in Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/user-groups-create |
| Configure custom IPsec policies for Virtual WAN in the portal | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-custom-ipsec-portal |
| Reference IPsec policy combinations for Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-ipsec |
| Configure Virtual WAN P2S with Entra ID auth | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-point-to-site-azure-ad |
| Create virtual hub route tables to NVAs via PowerShell | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-route-table-nva |
| Create virtual hub route tables to NVAs via portal | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-route-table-nva-portal |
| Configure IPsec over ExpressRoute in Azure Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/vpn-over-expressroute |
| Create Intune custom profiles for Azure VPN clients | https://learn.microsoft.com/en-us/azure/virtual-wan/vpn-profile-intune |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Create ExpressRoute associations to Virtual WAN via PowerShell | https://learn.microsoft.com/en-us/azure/virtual-wan/expressroute-powershell |
| Configure RADIUS VSAs for Virtual WAN user groups | https://learn.microsoft.com/en-us/azure/virtual-wan/user-groups-radius |
| Automate SD-WAN and VPN CPE integration with Virtual WAN | https://learn.microsoft.com/en-us/azure/virtual-wan/virtual-wan-configure-automation-providers |

### Deployment
| Topic | URL |
|-------|-----|
| Connect cross-tenant VNets to Virtual WAN hubs with PowerShell | https://learn.microsoft.com/en-us/azure/virtual-wan/cross-tenant-vnet |
| Deploy an integrated NVA in an Azure Virtual WAN hub | https://learn.microsoft.com/en-us/azure/virtual-wan/how-to-nva-hub |