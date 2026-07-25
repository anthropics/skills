---
name: azure-firewall
description: Expert knowledge for Azure Firewall development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when designing Azure Firewall SKUs, policies/rules, TLS inspection, DNAT/SNAT, logging/Sentinel, or hub‑and‑spoke, and other Azure Firewall related development tasks. Not for Azure Firewall Manager (use azure-firewall-manager), Azure Virtual Network (use azure-virtual-network), Azure Virtual Network Manager (use azure-virtual-network-manager), Azure Web Application Firewall (use azure-web-application-firewall).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Firewall Skill

This skill provides expert guidance for Azure Firewall. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L42 | Diagnosing Azure Firewall issues using known limitations, packet captures, and Sentinel log analysis for malware detection and traffic investigation. |
| Best Practices | L43-L50 | Best practices for Azure Firewall DNS proxy/caching, rule and SNAT tuning, using Policy Analytics to refine rules, and hardening firewall security and configuration |
| Decision Making | L51-L59 | Guidance on choosing Azure Firewall SKUs (Basic/Standard/Premium), comparing features and performance, and planning or changing deployments based on throughput and requirements. |
| Architecture & Design Patterns | L60-L71 | Designing Azure Firewall network architectures: hub-and-spoke, forced tunneling, load balancer integration, hybrid/AVD/M365 protection, and DNAT for overlapping/private IP networks. |
| Limits & Quotas | L72-L81 | Azure Firewall capacity, IP and SNAT port limits, prescaling options, TCP idle timeouts, and how to scale/extend outbound connectivity (including via NAT Gateway V2). |
| Security | L82-L95 | Azure Firewall security setup: compliance, RBAC/permissions, Azure Policy, TLS inspection and CA chains, threat intel, DNAT, AKS and hybrid network protection, and portal deployment. |
| Configuration | L96-L118 | Configuring Azure Firewall policies, rules (DNAT/SNAT/app), IP groups, DNS/proxy, Premium features, logging/monitoring, automation via PowerShell, and tracking rule changes. |
| Integrations & Coding Patterns | L119-L123 | Configuring Azure Firewall to securely access Azure Storage via SFTP, including required rules, network paths, and integration patterns for SFTP traffic. |
| Deployment | L124-L131 | How to deploy Azure Firewall (including Premium) with IP Groups using Bicep/ARM/Terraform, and integrate with Azure DDoS Protection, including basic configuration steps |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Detect and investigate malware using Sentinel with Azure Firewall logs | https://learn.microsoft.com/en-us/azure/firewall/detect-malware-with-sentinel |
| Troubleshoot Azure Firewall using packet capture | https://learn.microsoft.com/en-us/azure/firewall/packet-capture |

### Best Practices
| Topic | URL |
|-------|-----|
| Understand Azure Firewall DNS proxy behavior and caching | https://learn.microsoft.com/en-us/azure/firewall/dns-details |
| Optimize Azure Firewall performance with rule and SNAT tuning | https://learn.microsoft.com/en-us/azure/firewall/firewall-best-practices |
| Optimize Azure Firewall rules with Policy Analytics | https://learn.microsoft.com/en-us/azure/firewall/policy-analytics |
| Apply security best practices to Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/secure-firewall |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose and change Azure Firewall Standard vs Premium SKU | https://learn.microsoft.com/en-us/azure/firewall/change-sku |
| Select the appropriate Azure Firewall SKU | https://learn.microsoft.com/en-us/azure/firewall/choose-firewall-sku |
| Deploy Azure Firewall Basic with portal and policy | https://learn.microsoft.com/en-us/azure/firewall/deploy-firewall-basic-portal-policy |
| Compare Azure Firewall features across SKUs | https://learn.microsoft.com/en-us/azure/firewall/features-by-sku |
| Plan Azure Firewall performance and SKU throughput | https://learn.microsoft.com/en-us/azure/firewall/firewall-performance |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Architect multi-hub and spoke routing with Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/firewall-multi-hub-spoke |
| Design Azure Firewall forced tunneling architectures | https://learn.microsoft.com/en-us/azure/firewall/forced-tunneling |
| Integrate Azure Firewall with Standard Load Balancer | https://learn.microsoft.com/en-us/azure/firewall/integrate-lb |
| Use Azure Firewall Management NIC for control traffic | https://learn.microsoft.com/en-us/azure/firewall/management-nic |
| Architect Azure Firewall protection for Azure Virtual Desktop | https://learn.microsoft.com/en-us/azure/firewall/protect-azure-virtual-desktop |
| Design Azure Firewall protection for Microsoft 365 traffic | https://learn.microsoft.com/en-us/azure/firewall/protect-office-365 |
| Architect Azure Firewall in hybrid network topologies | https://learn.microsoft.com/en-us/azure/firewall/tutorial-hybrid-ps |
| Use private IP DNAT for overlapped Azure networks | https://learn.microsoft.com/en-us/azure/firewall/tutorial-private-ip-dnat |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Deploy Azure Firewall with multiple public IPs and limits | https://learn.microsoft.com/en-us/azure/firewall/deploy-multi-public-ip-powershell |
| Azure Firewall FAQ limits, features, and behaviors | https://learn.microsoft.com/en-us/azure/firewall/firewall-faq |
| Scale Azure Firewall SNAT ports and IP limits | https://learn.microsoft.com/en-us/azure/firewall/integrate-with-nat-gateway |
| Integrate Azure Firewall with NAT Gateway V2 for SNAT scaling | https://learn.microsoft.com/en-us/azure/firewall/integrate-with-nat-gateway-v2 |
| Configure Azure Firewall prescaling capacity ranges | https://learn.microsoft.com/en-us/azure/firewall/prescaling |
| Configure Azure Firewall TCP session idle timeouts | https://learn.microsoft.com/en-us/azure/firewall/tcp-session-behavior |

### Security
| Topic | URL |
|-------|-----|
| Understand Azure Firewall compliance certifications | https://learn.microsoft.com/en-us/azure/firewall/compliance-certifications |
| Enforce Azure Firewall security using Azure Policy | https://learn.microsoft.com/en-us/azure/firewall/firewall-azure-policy |
| Configure TLS inspection certificates for Firewall Premium | https://learn.microsoft.com/en-us/azure/firewall/premium-certificates |
| Deploy Enterprise CA chain for Azure Firewall Premium | https://learn.microsoft.com/en-us/azure/firewall/premium-deploy-certificates-enterprise-ca |
| Protect AKS clusters using Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/protect-azure-kubernetes-service |
| Azure Firewall roles, permissions, and required access | https://learn.microsoft.com/en-us/azure/firewall/roles-permissions |
| Configure Azure Firewall threat intelligence filtering | https://learn.microsoft.com/en-us/azure/firewall/threat-intel |
| Deploy and configure Azure Firewall in portal | https://learn.microsoft.com/en-us/azure/firewall/tutorial-firewall-deploy-portal |
| Configure Azure Firewall DNAT for inbound filtering | https://learn.microsoft.com/en-us/azure/firewall/tutorial-firewall-dnat |
| Configure Azure Firewall for hybrid network security | https://learn.microsoft.com/en-us/azure/firewall/tutorial-hybrid-portal |

### Configuration
| Topic | URL |
|-------|-----|
| Create and manage Azure Firewall IP Groups | https://learn.microsoft.com/en-us/azure/firewall/create-ip-group |
| Set customer-controlled maintenance windows for Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/customer-controlled-maintenance |
| Deploy and configure Azure Firewall policy via PowerShell | https://learn.microsoft.com/en-us/azure/firewall/deploy-ps-policy |
| Bulk manage Azure Firewall rules with PowerShell | https://learn.microsoft.com/en-us/azure/firewall/deploy-rules-powershell |
| Configure and monitor Azure Firewall DNAT rules | https://learn.microsoft.com/en-us/azure/firewall/destination-nat-rules |
| Configure DNS servers and DNS proxy for Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/dns-settings |
| Use Azure Firewall Policy Draft and Deployment | https://learn.microsoft.com/en-us/azure/firewall/draft-deploy |
| Configure Azure Firewall explicit proxy mode | https://learn.microsoft.com/en-us/azure/firewall/explicit-proxy |
| Analyze Azure Firewall data using workbooks | https://learn.microsoft.com/en-us/azure/firewall/firewall-workbook |
| Use Azure Firewall FQDN tags in application rules | https://learn.microsoft.com/en-us/azure/firewall/fqdn-tags |
| Configure FTP modes and security on Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/ftp-support |
| Configure and use IP Groups in Azure Firewall rules | https://learn.microsoft.com/en-us/azure/firewall/ip-groups |
| Configure monitoring and logging for Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/monitor-firewall |
| Use Azure Firewall monitoring logs and metrics reference | https://learn.microsoft.com/en-us/azure/firewall/monitor-firewall-reference |
| Implement Azure Firewall Premium advanced features | https://learn.microsoft.com/en-us/azure/firewall/premium-features |
| Track Azure Firewall rule changes with Resource Graph | https://learn.microsoft.com/en-us/azure/firewall/rule-set-change-tracking |
| Configure SNAT private IP ranges in Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/snat-private-range |
| Configure Azure Firewall application rules with SQL FQDNs | https://learn.microsoft.com/en-us/azure/firewall/sql-fqdn-filtering |
| Configure Azure Firewall DNAT policy for inbound traffic | https://learn.microsoft.com/en-us/azure/firewall/tutorial-firewall-dnat-policy |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Access Azure Storage via SFTP through Azure Firewall | https://learn.microsoft.com/en-us/azure/firewall/firewall-sftp |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy and configure Azure Firewall Premium environments | https://learn.microsoft.com/en-us/azure/firewall/premium-deploy |
| Deploy Azure Firewall and IP Groups using Bicep | https://learn.microsoft.com/en-us/azure/firewall/quick-create-ipgroup-bicep |
| Deploy Azure Firewall and IP Groups via ARM template | https://learn.microsoft.com/en-us/azure/firewall/quick-create-ipgroup-template |
| Deploy Azure Firewall and IP Groups using Terraform | https://learn.microsoft.com/en-us/azure/firewall/quick-create-ipgroup-terraform |
| Deploy Azure Firewall with Azure DDoS Protection | https://learn.microsoft.com/en-us/azure/firewall/tutorial-protect-firewall-ddos |