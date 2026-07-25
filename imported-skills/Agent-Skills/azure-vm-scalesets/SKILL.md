---
name: azure-vm-scalesets
description: Expert knowledge for Azure Virtual Machine Scale Sets development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring VMSS autoscale/standby pools, disk encryption with Key Vault, PPGs, Log Analytics, or rolling upgrades, and other Azure Virtual Machine Scale Sets related development tasks. Not for Azure Virtual Machines (use azure-virtual-machines), Azure Kubernetes Service (AKS) (use azure-kubernetes-service), Azure Container Instances (use azure-container-instances), Azure App Service (use azure-app-service).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Virtual Machine Scale Sets Skill

This skill provides expert guidance for Azure Virtual Machine Scale Sets. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L43 | Diagnosing and fixing issues with VMSS instance mix, standby pools behavior, and autoscale (rules, scaling delays, capacity mismatches, and common error scenarios). |
| Best Practices | L44-L49 | Configuring rolling upgrades for VM scale sets, tuning MaxSurge settings, and strategies to minimize downtime and maintain high availability during production updates. |
| Decision Making | L50-L66 | Guidance on choosing VMSS orchestration/upgrade modes, autoscale, Spot vs standard/priority mix, fault domains, standby pools, and cost-optimized configurations for different workload patterns. |
| Architecture & Design Patterns | L67-L71 | Designing scale sets with proximity placement groups to minimize latency, improve performance, and ensure VMs are co-located for tightly coupled or high-performance workloads |
| Limits & Quotas | L72-L77 | Scale set capacity, instance, and resource limits; placement group behavior; scaling constraints; and how limits affect deployment, availability, and distribution of VMs. |
| Security | L78-L89 | Encrypting VMSS disks (CLI, PowerShell, ARM), configuring Azure Disk Encryption with Key Vault and extensions, and securing scale sets via Azure Policy and RBAC for standby pools. |
| Configuration | L90-L133 | Configuring VM Scale Sets: templates, networking, disks, images, zones, upgrades, autoscale, repairs, standby pools, instance mix/protection, maintenance, and CLI/PowerShell/API management. |
| Integrations & Coding Patterns | L134-L139 | Configuring VM scale set standby pools with Log Analytics for monitoring and integrating scale sets with Azure DSC extension for automated configuration management. |
| Deployment | L140-L146 | Creating VM scale sets from generalized/specialized Shared Image Gallery images, migrating flexible sets to zonal, and deploying apps onto scale set instances. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| FAQ and troubleshooting for VM scale set instance mix | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/instance-mix-faq-troubleshooting |
| FAQ and troubleshooting for VM scale set standby pools | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-faq |
| Troubleshoot autoscale issues in Azure VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-troubleshoot |

### Best Practices
| Topic | URL |
|-------|-----|
| Configure rolling upgrades for production scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-configure-rolling-upgrades |
| Use MaxSurge rolling upgrades to improve uptime | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-maxsurge |

### Decision Making
| Topic | URL |
|-------|-----|
| Apply Azure Hybrid Benefit to Linux scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/azure-hybrid-benefit-linux |
| Migrate workloads to Flexible orchestration scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/flexible-virtual-machine-scale-sets-migration-resources |
| Decide when to use instance mix in VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/instance-mix-overview |
| Compare Uniform and Flexible VMSS APIs | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/orchestration-modes-api-comparison |
| Use Spot Placement Score to plan deployments | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/spot-placement-score |
| Balance Spot and standard VMs with Priority Mix | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/spot-priority-mix |
| Use standby pools to reduce VM scale set latency | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-overview |
| Use Spot VMs in scale sets for cost savings | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/use-spot |
| Select autoscale options for Azure VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-autoscale-overview |
| Design and choose features for VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-design-overview |
| Choose and configure fault domains for scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-manage-fault-domains |
| Choose VM scale set orchestration mode in Azure | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-orchestration-modes |
| Choose upgrade policy modes for VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-upgrade-policy |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Use proximity placement groups with scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/proximity-placement-groups |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Reference limits and behaviors for VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-faq |
| Understand placement groups and scale set capacity limits | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-placement-groups |

### Security
| Topic | URL |
|-------|-----|
| Create and encrypt VM Scale Sets via ARM | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/disk-encryption-azure-resource-manager |
| Encrypt VM Scale Set disks with Azure CLI | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/disk-encryption-cli |
| Sequence extensions for VMSS disk encryption | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/disk-encryption-extension-sequencing |
| Configure Key Vault for VMSS disk encryption | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/disk-encryption-key-vault |
| Enable Azure Disk Encryption for VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/disk-encryption-overview |
| Encrypt VM Scale Set disks with PowerShell | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/disk-encryption-powershell |
| Apply built-in Azure Policy to VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/policy-reference |
| Configure RBAC permissions for VM scale set standby pools | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-configure-permissions |

### Configuration
| Topic | URL |
|-------|-----|
| Alert on Automatic Instance Repairs ServiceState changes | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/alert-rules-automatic-repairs-service-state |
| Enable Automatic Zone Balance on scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/auto-zone-balance-enable |
| Use Automatic Zone Balance for VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/auto-zone-balance-overview |
| Define VM scale set configuration with ARM templates | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/flexible-virtual-machine-scale-sets-rest-api |
| Configure instance mix for Azure VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/instance-mix-create |
| Update instance mix settings on Azure VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/instance-mix-update |
| Inspect instance mix configuration on VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/instance-mix-view |
| Enable resilient create and delete for scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/resilient-vm-create-delete |
| Create and configure standby pools for VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-create |
| Retrieve standby pool and instance details for VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-get-details |
| Understand and query standby pool health state in VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-health-state |
| Get prediction results to size VM scale set standby pools | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-prediction-results |
| Configure Spot instances in VM scale set standby pools | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-spot-instances |
| Update or delete standby pools for Azure VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-update-delete |
| Configure attached data disks for VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-attached-disks |
| Configure automatic instance repairs for scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-automatic-instance-repairs |
| Configure automatic OS image upgrades for VMSS | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-automatic-upgrade |
| Change upgrade policy mode on existing scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-change-upgrade-policy |
| Sequence VM extensions in Azure scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-extension-sequencing |
| Configure Application Health extension for scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-health-extension |
| Understand and use instance IDs in scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-instance-ids |
| Configure instance protection on VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-instance-protection |
| Handle maintenance notifications for VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-maintenance-notifications |
| Manage VM Scale Sets using Azure CLI commands | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-manage-cli |
| Manage VM Scale Sets with Azure PowerShell | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-manage-powershell |
| Reference custom images in scale set templates | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-mvss-custom-image |
| Use existing virtual networks in VMSS templates | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-mvss-existing-vnet |
| Configure guest-metric autoscale for Linux VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-mvss-guest-based-autoscale-linux |
| Author basic ARM templates for VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-mvss-start |
| Configure networking for Azure VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-networking |
| Perform manual instance upgrades in VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-perform-manual-upgrades |
| Reimage virtual machines in a scale set | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-reimage-virtual-machine |
| Configure custom metrics for rolling upgrades | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-rolling-upgrade-custom-metrics |
| Configure scale-in policies for Azure VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-scale-in-policy |
| Define scaling profiles for Azure VM scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-scaling-profile |
| Set upgrade policy mode on VM Scale Sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-set-upgrade-policy |
| Enable terminate notifications for scale set instances | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-terminate-notification |
| Modify VM Scale Set model and configuration via APIs | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-upgrade-scale-set |
| Configure VM Scale Sets with availability zones | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-use-availability-zones |
| Configure and manage zone balancing in scale sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-zone-balancing |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate VM scale set standby pools with Azure Log Analytics | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/standby-pools-monitor-pool-events |
| Integrate VM Scale Sets with Azure DSC extension | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-dsc |

### Deployment
| Topic | URL |
|-------|-----|
| Create scale sets from generalized gallery images | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/instance-generalized-image-version |
| Create scale sets from specialized gallery images | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/instance-specialized-image-version |
| Migrate regional flexible scale sets to zonal sets | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/migrate-scale-set-flex-to-availability-zones |
| Deploy applications to VM Scale Set instances | https://learn.microsoft.com/en-us/azure/virtual-machine-scale-sets/virtual-machine-scale-sets-deploy-app |