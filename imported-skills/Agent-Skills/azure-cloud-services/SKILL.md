---
name: azure-cloud-services
description: Expert knowledge for Azure Cloud Services development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. Use when configuring Cloud Services roles, Key Vault certs, autoscale rules, guest OS upgrades, or PowerShell automation, and other Azure Cloud Services related development tasks. Not for Azure Networking (use azure-networking), Azure Virtual Machines (use azure-virtual-machines), Azure Resource Manager (use azure-resource-manager), Azure Portal (use azure-portal).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Cloud Services Skill

This skill provides expert guidance for Azure Cloud Services. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L39 | Diagnosing and fixing common migration errors when moving classic Cloud Services to Cloud Services (extended support), including deployment, configuration, and compatibility issues. |
| Best Practices | L40-L44 | Guidance on designing and configuring autoscale rules for Cloud Services, including metrics, thresholds, and patterns to optimize performance, reliability, and cost. |
| Decision Making | L45-L53 | Guidance on planning Cloud Services guest OS upgrades, comparing Cloud Services vs VM Scale Sets, and migrating classic/non-VNet Cloud Services to extended support and VNets. |
| Limits & Quotas | L54-L60 | VM instance size limits/capacities and timelines, impacts, and constraints related to Guest OS family retirements for Azure Cloud Services. |
| Security | L61-L66 | Using Key Vault for certificates in Cloud Services and understanding Azure Guest OS security updates, support lifecycle, and retirement policies |
| Configuration | L67-L85 | Configuring Cloud Services roles and deployments: .csdef/.cscfg schemas, network/load balancer settings, diagnostics, RDP, Key Vault, extensions, alerts, and scaling/SKU overrides. |
| Integrations & Coding Patterns | L86-L91 | Automating Azure Cloud Services (extended support) with PowerShell: creating deployments, retrieving service details, and resetting or redeploying cloud service instances. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common errors when migrating to Cloud Services extended support | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/in-place-migration-common-errors |

### Best Practices
| Topic | URL |
|-------|-----|
| Configure autoscaling rules for Cloud Services deployments | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/configure-scaling |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan Azure Cloud Services Guest OS upgrade path | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/cloud-services-guestos-update-matrix |
| Compare Cloud Services and Virtual Machine Scale Sets features | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/feature-support-analysis |
| Plan migration from Cloud Services classic to extended support | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/in-place-migration-overview |
| Understand technical requirements for Cloud Services migration | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/in-place-migration-technical-details |
| Plan migration of non-VNet Cloud Services into VNets | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/non-vnet-migration |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| VM size options and capacities for Cloud Services instances | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/available-sizes |
| Guest OS Family 1 retirement dates and deployment impact | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/cloud-services-guestos-family-1-retirement |
| Guest OS Families 2–4 retirement timelines and impact | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/cloud-services-guestos-family-2-3-4-retirement |

### Security
| Topic | URL |
|-------|-----|
| Securely store and use certificates with Key Vault in Cloud Services | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/certificates-and-key-vault |
| Understand support and retirement policy for Azure Guest OS | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/cloud-services-guestos-retirement-policy |

### Configuration
| Topic | URL |
|-------|-----|
| Understand Cloud Services model, config, and package files | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/cloud-services-model-and-package |
| Configure monitoring alerts for Cloud Services instances | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/enable-alerts |
| Enable Key Vault VM extension for Cloud Services roles | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/enable-key-vault-virtual-machine |
| Configure Remote Desktop extension for Cloud Services | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/enable-rdp |
| Configure Azure diagnostics extension for Cloud Services | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/enable-wad |
| Configure and manage extensions for Cloud Services roles | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/extensions |
| Override Cloud Services SKU and instance count via allowModelOverride | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/override-sku |
| Reference schema for Cloud Services configuration (.cscfg) | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/schema-cscfg-file |
| Configure NetworkConfiguration for Cloud Services deployments | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/schema-cscfg-networkconfiguration |
| Configure role settings in Cloud Services .cscfg | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/schema-cscfg-role |
| Reference schema for Cloud Services definition (.csdef) | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/schema-csdef-file |
| Configure LoadBalancerProbe in Cloud Services definitions | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/schema-csdef-loadbalancerprobe |
| Configure NetworkTrafficRules in Cloud Services definitions | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/schema-csdef-networktrafficrules |
| Define and configure WebRole schema for Cloud Services | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/schema-csdef-webrole |
| Define and configure WorkerRole schema for Cloud Services | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/schema-csdef-workerrole |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use PowerShell to create Cloud Services (extended support) | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/sample-create-cloud-service |
| Use PowerShell to retrieve Cloud Service details | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/sample-get-cloud-service |
| Use PowerShell to reset Cloud Services deployments | https://learn.microsoft.com/en-us/azure/cloud-services-extended-support/sample-reset-cloud-service |