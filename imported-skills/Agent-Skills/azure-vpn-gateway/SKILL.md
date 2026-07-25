---
name: azure-vpn-gateway
description: Expert knowledge for Azure VPN Gateway development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring P2S/S2S tunnels, IPsec/IKE policies, BGP routing, NAT, or active-active VPN gateways, and other Azure VPN Gateway related development tasks. Not for Azure Virtual Network (use azure-virtual-network), Azure Virtual WAN (use azure-virtual-wan), Azure ExpressRoute (use azure-expressroute), Azure NAT Gateway (use azure-nat-gateway).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure VPN Gateway Skill

This skill provides expert guidance for Azure VPN Gateway. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L44 | Diagnosing and fixing Azure VPN Gateway issues: client prerequisites, packet captures, tunnel resets, connection health checks, and answers to common troubleshooting FAQs. |
| Best Practices | L45-L49 | Guidance on using network virtual appliances (NVAs) in Azure as VPN endpoints for remote access, including design, routing, security, and integration with Azure VPN Gateway. |
| Decision Making | L50-L60 | Guidance on choosing VPN Gateway SKUs and planning/migrating configurations: IP SKUs, SKUs mapping, P2S protocols/clients, Linux client migration, Classic-to-ARM, and remote work P2S setups. |
| Architecture & Design Patterns | L61-L67 | Design patterns and guidance for choosing VPN Gateway topologies, configuring active-active gateways, and building highly available, resilient site-to-site connectivity. |
| Limits & Quotas | L68-L72 | VPN Gateway client version history, SKU comparisons, and FAQs about gateway limits, scale, performance, and connection behavior |
| Security | L73-L94 | Security configuration for Azure VPN Gateway: IPsec/IKE policies, cert/RADIUS/Entra auth, MFA, P2S/S2S access control, crypto requirements, and security best practices. |
| Configuration | L95-L155 | Configuring Azure VPN Gateway and clients: P2S/S2S setup, auth (cert, Entra, RADIUS), BGP, IPsec/NAT/routing, dual-stack, monitoring, VNet-to-VNet, and Always-On VPN. |
| Integrations & Coding Patterns | L156-L163 | Configuring Azure VPN Gateway with on-prem devices and services: NPS/RADIUS VSAs for P2S, S2S over ExpressRoute, Cisco ASA samples, and BGP VPN connectivity with AWS. |
| Deployment | L164-L177 | Deploying and configuring Azure VPN Gateways: creating gateways/S2S VPNs via PowerShell/CLI, migrating Basic→Standard IP/SKU, active-active changes, zone redundancy, and client profile deployment. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Run Azure VPN Client prerequisites check and fix issues | https://learn.microsoft.com/en-us/azure/vpn-gateway/azure-vpn-client-prerequisites-check |
| Use packet capture on VPN Gateway for diagnostics | https://learn.microsoft.com/en-us/azure/vpn-gateway/packet-capture |
| Reset VPN Gateway or connection to restore IPsec tunnels | https://learn.microsoft.com/en-us/azure/vpn-gateway/reset-gateway |
| Verify Azure VPN Gateway connection health | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-verify-connection-resource-manager |

### Best Practices
| Topic | URL |
|-------|-----|
| Use NVAs in Azure for remote access scenarios | https://learn.microsoft.com/en-us/azure/vpn-gateway/nva-work-remotely-support |

### Decision Making
| Topic | URL |
|-------|-----|
| Select appropriate Azure VPN Gateway SKU | https://learn.microsoft.com/en-us/azure/vpn-gateway/about-gateway-skus |
| Plan migration from Azure VPN Client for Linux | https://learn.microsoft.com/en-us/azure/vpn-gateway/azure-vpn-client-linux-retirement |
| Map and migrate Azure VPN Gateway SKUs | https://learn.microsoft.com/en-us/azure/vpn-gateway/gateway-sku-consolidation |
| Migrate Azure P2S VPN connections from SSTP to IKEv2/OpenVPN | https://learn.microsoft.com/en-us/azure/vpn-gateway/ikev2-openvpn-from-sstp |
| Migrate P2S VPN from manual to Microsoft-registered client | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-entra-gateway-update |
| Migrate VPN Gateways from Classic to Resource Manager | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-classic-resource-manager-migration |
| Plan remote work using P2S VPN Gateways | https://learn.microsoft.com/en-us/azure/vpn-gateway/work-remotely-support |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design and configure active-active VPN Gateways | https://learn.microsoft.com/en-us/azure/vpn-gateway/about-active-active-gateways |
| Select Azure VPN Gateway topologies and designs | https://learn.microsoft.com/en-us/azure/vpn-gateway/design |
| Design highly available Azure VPN Gateway connectivity | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-highlyavailable |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Compare Azure VPN Gateway legacy SKUs and limits | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-about-skus-legacy |

### Security
| Topic | URL |
|-------|-----|
| Implement forced tunneling for S2S VPN connections | https://learn.microsoft.com/en-us/azure/vpn-gateway/about-site-to-site-tunneling |
| Configure custom IPsec/IKE policies in Azure portal | https://learn.microsoft.com/en-us/azure/vpn-gateway/ipsec-ike-policy-howto |
| Enable multifactor authentication for P2S VPN users | https://learn.microsoft.com/en-us/azure/vpn-gateway/openvpn-azure-ad-mfa |
| Configure P2S VPN with Entra ID and manual client app | https://learn.microsoft.com/en-us/azure/vpn-gateway/openvpn-azure-ad-tenant |
| View and disconnect Azure P2S VPN sessions securely | https://learn.microsoft.com/en-us/azure/vpn-gateway/p2s-session-management |
| Manage VPN gateway root certificate migration for P2S | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-about-gateway-certificate-migration |
| Create custom audience app ID for P2S Entra VPN | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-entra-register-custom-app |
| Configure P2S access control by Entra users and groups | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-entra-users-access |
| Configure macOS Azure VPN Client for Entra ID P2S auth | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-entra-vpn-client-mac |
| Configure Device SSO with Azure VPN Client on Windows | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-entra-vpn-client-windows-device-sso |
| Set up P2S RADIUS VPN with PowerShell for Azure | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-how-to-radius-ps |
| Configure P2S RADIUS authentication in Azure VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-radius-gateway |
| Understand roles and permissions for VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/roles-permissions |
| Apply security best practices to Azure VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/secure-vpn-gateway |
| Use certificate authentication for S2S VPN connections | https://learn.microsoft.com/en-us/azure/vpn-gateway/site-to-site-certificate-authentication-gateway-about |
| Configure S2S certificate authentication using PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/site-to-site-certificate-authentication-gateway-powershell |
| Meet cryptographic requirements for Azure VPN gateways | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-about-compliance-crypto |
| Integrate Azure P2S RADIUS with NPS for MFA | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-radius-mfa-nsp |

### Configuration
| Topic | URL |
|-------|-----|
| Generate P2S VPN client profiles for Entra authentication | https://learn.microsoft.com/en-us/azure/vpn-gateway/about-vpn-profile-download |
| Add or remove S2S connections on a VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/add-remove-site-to-site-connections |
| Configure optional Azure VPN Client settings for P2S | https://learn.microsoft.com/en-us/azure/vpn-gateway/azure-vpn-client-optional-configurations |
| Configure BGP for VPN Gateway using Azure CLI | https://learn.microsoft.com/en-us/azure/vpn-gateway/bgp-how-to-cli |
| Enable and configure BGP for Azure VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/bgp-howto |
| Create custom IPsec policies for P2S VPN | https://learn.microsoft.com/en-us/azure/vpn-gateway/create-custom-policies-p2s-ps |
| Configure custom traffic selectors for VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/custom-traffic-selectors |
| Configure customer-controlled maintenance windows for VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/customer-controlled-gateway-maintenance |
| Configure IPv6 dual-stack for Azure VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/ipv6-configuration |
| Configure monitoring for Azure VPN Gateway with Azure Monitor | https://learn.microsoft.com/en-us/azure/vpn-gateway/monitor-vpn-gateway |
| Reference for Azure VPN Gateway monitoring data | https://learn.microsoft.com/en-us/azure/vpn-gateway/monitor-vpn-gateway-reference |
| Configure NAT rules on Azure VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/nat-howto |
| Configure Azure VPN Client for Linux with P2S certificates | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-certificate-client-linux-azure-vpn-client |
| Configure P2S certificate authentication on VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-certificate-gateway |
| Generate P2S VPN certificates on Linux with OpenSSL | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-certificates-linux-openssl |
| Configure P2S VPN gateway with Entra ID client | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-entra-gateway |
| Configure Azure VPN Client on Linux with Entra ID | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-entra-vpn-client-linux |
| Configure Azure VPN Client with Entra ID on Windows | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-entra-vpn-client-windows |
| Install P2S client certificates on Windows, macOS, Linux | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-how-to-vpn-client-install-azure-cert |
| Configure P2S VPN user groups and IP pools | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-user-groups-about |
| Generate and update P2S VPN client profiles in Azure | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-user-vpn-profile-update |
| Configure macOS native VPN client for P2S certificates | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-cert-mac |
| Configure Linux strongSwan IKEv2 client for P2S certificates | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-certificate-ike-linux |
| Configure iOS OpenVPN client for P2S certificate VPN | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-certificate-openvpn-ios |
| Configure Linux OpenVPN client for P2S certificate VPN | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-certificate-openvpn-linux |
| Configure macOS OpenVPN client for P2S certificate VPN | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-certificate-openvpn-mac |
| Configure Azure VPN Client on Windows for P2S certificates | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-certificate-windows-azure-vpn-client |
| Configure Windows native client for P2S certificate VPN | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-certificate-windows-native |
| Configure OpenVPN 2.x Windows client for P2S certificates | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-certificate-windows-openvpn-client |
| Configure OpenVPN 3.x Windows client for P2S certificates | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-certificate-windows-openvpn-client-version-3 |
| Configure VPN client for P2S RADIUS certificate auth | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-configuration-radius-certificate |
| Configure VPN client for other P2S RADIUS methods | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-configuration-radius-other |
| Configure VPN client for P2S RADIUS password auth | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-vpn-client-configuration-radius-password |
| Configure high-bandwidth S2S tunnels via ExpressRoute | https://learn.microsoft.com/en-us/azure/vpn-gateway/site-to-site-high-bandwidth-tunnel |
| Set up dual-stack site-to-site VPN with Azure CLI | https://learn.microsoft.com/en-us/azure/vpn-gateway/site-to-site-ipv6-azure-cli |
| Configure forced tunneling for S2S VPN in Azure | https://learn.microsoft.com/en-us/azure/vpn-gateway/site-to-site-tunneling |
| Understand Point-to-Site VPN routing behavior in Azure | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-about-point-to-site-routing |
| Supported VPN devices and IPsec parameters for Azure | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-about-vpn-devices |
| Azure VPN Gateway resource and connection settings | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-about-vpn-gateway-settings |
| Configure BGP for VPN Gateway using PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-bgp-resource-manager-ps |
| Generate P2S VPN certificates using Windows PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-certificates-point-to-site |
| Generate P2S VPN certificates on Linux with strongSwan | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-certificates-point-to-site-linux |
| Generate P2S VPN certificates using MakeCert | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-certificates-point-to-site-makecert |
| Connect classic VNets to ARM VNets via VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-connect-different-deployment-models-portal |
| Connect classic VNets to ARM VNets with PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-connect-different-deployment-models-powershell |
| Configure route-based VPN to multiple policy-based devices | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-connect-multiple-policybased-rm-ps |
| Configure Windows Always-On VPN device tunnel to Azure | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-howto-always-on-device-tunnel |
| Configure macOS Always-On VPN device tunnel to Azure | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-howto-always-on-device-tunnel-macos |
| Configure Windows Always-On VPN user tunnel to Azure | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-howto-always-on-user-tunnel |
| Configure certificate-based Point-to-Site VPN with PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-howto-point-to-site-rm-ps |
| Configure VNet-to-VNet VPN connections using Azure CLI | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-howto-vnet-vnet-cli |
| Configure VNet-to-VNet VPN connection in portal | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-howto-vnet-vnet-resource-manager-portal |
| Configure custom IPsec/IKE policies with PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-ipsecikepolicy-rm-powershell |
| Advertise custom routes to P2S VPN clients | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-p2s-advertise-custom-routes |
| Configure VPN gateway transit for VNet peering | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-peering-gateway-transit |
| Create VNet-to-VNet VPN connections with PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-vnet-vnet-rm-ps |
| Configure and troubleshoot Azure VPN Gateway connections | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-vpn-faq |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Configure NPS RADIUS VSAs for P2S user groups | https://learn.microsoft.com/en-us/azure/vpn-gateway/point-to-site-user-groups-radius |
| Configure S2S VPN over ExpressRoute private peering | https://learn.microsoft.com/en-us/azure/vpn-gateway/site-to-site-vpn-private-peering |
| Sample Cisco ASA configuration for Azure VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-3rdparty-device-config-cisco-asa |
| Configure BGP VPN connection between Azure and AWS | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-howto-aws-bgp |

### Deployment
| Topic | URL |
|-------|-----|
| Migrate VPN Gateway Basic public IP to Standard | https://learn.microsoft.com/en-us/azure/vpn-gateway/basic-public-ip-migrate-about |
| Execute Basic-to-Standard public IP migration for VPN Gateway | https://learn.microsoft.com/en-us/azure/vpn-gateway/basic-public-ip-migrate-howto |
| Create a Basic SKU VPN Gateway via PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/create-gateway-basic-sku-powershell |
| Deploy a VPN Gateway using PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/create-gateway-powershell |
| Deploy a VPN Gateway using Azure CLI | https://learn.microsoft.com/en-us/azure/vpn-gateway/create-routebased-vpn-gateway-cli |
| Deploy zone-redundant VPN and ExpressRoute gateways | https://learn.microsoft.com/en-us/azure/vpn-gateway/create-zone-redundant-vnet-gateway |
| Change Azure VPN Gateway between active and active-active | https://learn.microsoft.com/en-us/azure/vpn-gateway/gateway-change-active-active |
| Upgrade Azure VPN Gateway SKU with minimal downtime | https://learn.microsoft.com/en-us/azure/vpn-gateway/gateway-sku-upgrade |
| Create S2S VPN with shared key using PowerShell | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-create-site-to-site-rm-powershell |
| Create S2S VPN with shared key using Azure CLI | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-gateway-howto-site-to-site-resource-manager-cli |
| Deploy Azure VPN client profiles using Intune | https://learn.microsoft.com/en-us/azure/vpn-gateway/vpn-profile-intune |