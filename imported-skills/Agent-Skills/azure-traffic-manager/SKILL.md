---
name: azure-traffic-manager
description: Expert knowledge for Azure Traffic Manager development including troubleshooting, best practices, decision making, architecture & design patterns, security, configuration, and integrations & coding patterns. Use when configuring profiles/endpoints, routing methods, RUM scripts, nested profiles, or Traffic View analytics, and other Azure Traffic Manager related development tasks. Not for Azure Front Door (use azure-front-door), Azure Load Balancer (use azure-load-balancer), Azure Virtual Network (use azure-virtual-network), Azure Virtual WAN (use azure-virtual-wan).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-07"
  generator: "docs2skills/1.0.0"
---
# Azure Traffic Manager Skill

This skill provides expert guidance for Azure Traffic Manager. Covers troubleshooting, best practices, decision making, architecture & design patterns, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L39 | Testing Traffic Manager routing behavior, verifying endpoint health, and diagnosing/fixing degraded profiles, misconfigurations, and routing issues. |
| Best Practices | L40-L44 | Guidance on optimizing Traffic Manager profiles, endpoint configuration, monitoring, and routing settings for high performance, reliability, and low-latency global traffic distribution |
| Decision Making | L45-L50 | Guidance on choosing the right Traffic Manager routing method and using Traffic View analytics to optimize routing decisions and traffic distribution |
| Architecture & Design Patterns | L51-L58 | Architectural patterns for combining Traffic Manager with other Azure load balancers, nested profiles, App Service integration, and Traffic Manager + Application Gateway designs. |
| Security | L59-L63 | Best practices for securely configuring Traffic Manager profiles, endpoints, access controls, and monitoring to protect traffic routing and DNS-based load balancing. |
| Configuration | L64-L85 | Configuring Traffic Manager profiles, endpoints, routing methods (weighted, geographic, subnet, multivalue), DNS/IPv6, monitoring/logs, and using ARM, Bicep, Terraform, CLI, and PowerShell. |
| Integrations & Coding Patterns | L86-L90 | Using Traffic Manager Real User Measurements (RUM) in apps and web pages, including integrating with Visual Studio App Center and adding the RUM JavaScript to collect user latency data. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Verify and test Azure Traffic Manager routing configuration | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-testing-settings |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply performance best practices for Azure Traffic Manager | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-performance-considerations |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose appropriate Azure Traffic Manager routing methods | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-routing-methods |
| Use Traffic View insights for Traffic Manager optimization | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-traffic-view-overview |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design solutions using Azure load-balancing portfolio | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-load-balancing-azure |
| Design nested Traffic Manager profile architectures | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-nested-profiles |
| Integrate Azure App Service with Traffic Manager routing | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-use-azure-app-service |
| Architect solutions combining Traffic Manager and Application Gateway | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-use-with-application-gateway |

### Security
| Topic | URL |
|-------|-----|
| Secure configuration practices for Azure Traffic Manager | https://learn.microsoft.com/en-us/azure/traffic-manager/secure-traffic-manager |

### Configuration
| Topic | URL |
|-------|-----|
| Define nested Multivalue routing with ARM templates | https://learn.microsoft.com/en-us/azure/traffic-manager/configure-multivalue-routing-method-template |
| Configure DNS record types and IPv6 in Traffic Manager | https://learn.microsoft.com/en-us/azure/traffic-manager/dns-record-types |
| Add external endpoints to Traffic Manager via ARM templates | https://learn.microsoft.com/en-us/azure/traffic-manager/how-to-add-endpoint-existing-profile-template |
| Define Traffic Manager profiles using Bicep | https://learn.microsoft.com/en-us/azure/traffic-manager/quickstart-create-traffic-manager-profile-bicep |
| Configure Traffic Manager profiles with ARM templates | https://learn.microsoft.com/en-us/azure/traffic-manager/quickstart-create-traffic-manager-profile-template |
| Provision Traffic Manager profiles using Terraform | https://learn.microsoft.com/en-us/azure/traffic-manager/quickstart-create-traffic-manager-profile-terraform |
| Configure MultiValue routing profiles in Traffic Manager | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-configure-multivalue-routing-method |
| Configure subnet-based routing rules in Traffic Manager | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-configure-subnet-routing-method |
| Enable and use Traffic Manager diagnostic resource logs | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-diagnostic-logs |
| Configure geographic routing regions for Traffic Manager | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-geographic-regions |
| Manage Traffic Manager endpoints across regions | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-manage-endpoints |
| Create and manage Azure Traffic Manager profiles | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-manage-profiles |
| Use Traffic Manager metrics and alerts for monitoring | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-metrics-alerts |
| Configure endpoint monitoring and health checks in Traffic Manager | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-monitoring |
| Manage Azure Traffic Manager with PowerShell (ARM) | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-powershell-arm |
| Configure Traffic Manager subnet override via Azure CLI | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-subnet-override-cli |
| Configure Traffic Manager subnet override via PowerShell | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-subnet-override-powershell |
| Configure weighted endpoint routing in Traffic Manager | https://learn.microsoft.com/en-us/azure/traffic-manager/tutorial-traffic-manager-weighted-endpoint-routing |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Visual Studio App Center apps with Traffic Manager RUM | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-create-rum-visual-studio |
| Instrument web pages for Traffic Manager Real User Measurements | https://learn.microsoft.com/en-us/azure/traffic-manager/traffic-manager-create-rum-web-pages |