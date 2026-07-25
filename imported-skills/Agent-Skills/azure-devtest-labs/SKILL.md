---
name: azure-devtest-labs
description: Expert knowledge for Azure DevTest Labs development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when managing DevTest Labs images, artifacts, ARM/REST automation, VM start/stop, or hub-spoke lab networks, and other Azure DevTest Labs related development tasks. Not for Azure Lab Services (use azure-lab-services), Azure Dev Box (use azure-dev-box), Azure Virtual Machines (use azure-virtual-machines), Azure Virtual Desktop (use azure-virtual-desktop).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure DevTest Labs Skill

This skill provides expert guidance for Azure DevTest Labs. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L44 | Diagnosing and fixing DevTest Labs VM and environment creation/deployment issues, artifact application failures, connectivity problems, and handling Defender for Cloud security alerts. |
| Best Practices | L45-L49 | Guidance on organizing and collaborating on DevTest Labs infrastructure as code across teams, including branching, environments, and distributed resource development workflows |
| Decision Making | L50-L58 | Guidance on planning PoCs and enterprise-scale deployments, choosing images and Gen1 vs Gen2 VMs, and setting governance for organization-wide DevTest Labs use. |
| Architecture & Design Patterns | L59-L63 | Enterprise-scale DevTest Labs architectures: hub-spoke design, network/security layout, governance, cost management, and best practices for large org lab deployments. |
| Limits & Quotas | L64-L68 | Managing DevTest Labs limits and quotas, viewing current usage, and requesting or configuring quota increases for labs, VMs, and related resources. |
| Security | L69-L86 | Securing DevTest Labs: identities, RBAC and granular policy permissions, secrets/Key Vault, disk/storage encryption, secure VM access (RDP Gateway, Bastion, browser), Trusted Launch, and security alerts. |
| Configuration | L87-L109 | Configuring DevTest Labs environments and VMs: images, networks, policies, costs, tags, ARM templates, artifacts, activity logs, alerts, IPs, and resource groups. |
| Integrations & Coding Patterns | L110-L128 | Automating DevTest Labs with ARM, PowerShell, CLI, REST, and Functions: user/VM management, VHD/custom image workflows, cross-lab import, reporting, and VM start/stop/start-order control. |
| Deployment | L129-L135 | Guides for deploying and migrating DevTest Labs: ARM templates, CI/CD and Azure Pipelines integration, region moves, and handling Azure Basic Load Balancer retirement. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Fix DevTest Labs VM connectivity by redeploying | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-redeploy-vm |
| Troubleshoot DevTest Labs artifact application failures | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-troubleshoot-apply-artifacts |
| Troubleshoot DevTest Labs VM deployment failures | https://learn.microsoft.com/en-us/azure/devtest-labs/troubleshoot-vm-deployment-failures |
| Troubleshoot DevTest Labs VM and environment creation failures | https://learn.microsoft.com/en-us/azure/devtest-labs/troubleshoot-vm-environment-creation-failures |

### Best Practices
| Topic | URL |
|-------|-----|
| Set up distributed DevTest Labs resource development | https://learn.microsoft.com/en-us/azure/devtest-labs/best-practices-distributive-collaborative-development-environment |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan and execute a DevTest Labs proof of concept | https://learn.microsoft.com/en-us/azure/devtest-labs/deliver-proof-concept |
| Choose between custom images and formulas in DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-comparing-vm-base-image-types |
| Choose and use Gen1 vs Gen2 VMs in DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-gen2-vm |
| Govern Azure DevTest Labs resources across an organization | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-guidance-governance-resources |
| Plan DevTest Labs deployment at enterprise scale | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-guidance-scale |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Enterprise reference architecture for Azure DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-reference-architecture |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| View and increase Azure DevTest Labs quotas and limits | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-scale-lab |

### Security
| Topic | URL |
|-------|-----|
| Configure managed identity for Azure DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/configure-lab-identity |
| Secure DevTest Labs access with Remote Desktop Gateway | https://learn.microsoft.com/en-us/azure/devtest-labs/configure-lab-remote-desktop-gateway |
| Secure DevTest Labs VM access via Azure Bastion | https://learn.microsoft.com/en-us/azure/devtest-labs/connect-virtual-machine-through-browser |
| Configure DevTest Labs RBAC roles and user access | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-add-devtest-user |
| Configure DevTest Labs lab-level secrets securely | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-configure-lab-secrets |
| Grant granular permissions to DevTest Labs policies | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-grant-user-permissions-to-specific-lab-policies |
| Use Azure Key Vault secrets in DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-store-secrets-in-key-vault |
| Enable Trusted Launch for DevTest Labs Gen2 VMs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-trusted-launch |
| Enable secure browser-based access to DevTest Labs VMs | https://learn.microsoft.com/en-us/azure/devtest-labs/enable-browser-connection-lab-virtual-machines |
| Enable user-assigned managed identities on DevTest Labs VMs | https://learn.microsoft.com/en-us/azure/devtest-labs/enable-managed-identities-lab-vms |
| Configure customer-managed key disk encryption in DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/encrypt-disks-customer-managed-keys |
| Manage DevTest Labs storage accounts and encryption settings | https://learn.microsoft.com/en-us/azure/devtest-labs/encrypt-storage |
| View and respond to DevTest Labs environment security alerts | https://learn.microsoft.com/en-us/azure/devtest-labs/environment-security-alerts |
| Configure managed identities for DevTest Labs environments | https://learn.microsoft.com/en-us/azure/devtest-labs/use-managed-identities-environments |

### Configuration
| Topic | URL |
|-------|-----|
| View and interpret DevTest Labs activity logs | https://learn.microsoft.com/en-us/azure/devtest-labs/activity-logs |
| Add and configure artifacts on DevTest Labs VMs | https://learn.microsoft.com/en-us/azure/devtest-labs/add-artifact-vm |
| Configure Azure Compute Gallery for DevTest Labs images | https://learn.microsoft.com/en-us/azure/devtest-labs/configure-shared-image-gallery |
| Configure activity log alerts for DevTest Labs events | https://learn.microsoft.com/en-us/azure/devtest-labs/create-alerts |
| Add and manage tags on Azure DevTest Labs resources | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-add-tag |
| Author custom DevTest Labs VM artifact definitions | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-artifact-author |
| Configure autoshutdown policies for DevTest Labs VMs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-auto-shutdown |
| Configure autostart policies for DevTest Labs virtual machines | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-auto-startup-vm |
| Configure cost tracking for Azure DevTest Labs with tags | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-configure-cost-management |
| Configure allowed Azure Marketplace images in DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-configure-marketplace-images |
| Add and configure virtual networks for DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-configure-vnet |
| Create DevTest Labs environments from ARM templates | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-create-environment-from-arm |
| Enable and manage licensed images in DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-enable-licensed-images |
| Configure and use formulas for DevTest Labs VMs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-manage-formulas |
| Configure Azure DevTest Labs policies for cost control | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-set-lab-policy |
| Configure shared public IP addresses for DevTest Labs VMs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-shared-ip |
| Define DevTest Labs VMs with ARM templates | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-use-resource-manager-template |
| Configure network isolation for Azure DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/network-isolation |
| Configure resource groups for DevTest Labs virtual machines | https://learn.microsoft.com/en-us/azure/devtest-labs/resource-group-control |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Automate adding DevTest Labs users via ARM, PowerShell, and CLI | https://learn.microsoft.com/en-us/azure/devtest-labs/automate-add-lab-user |
| Create DevTest Labs custom images from VHD with PowerShell | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-create-custom-image-from-vhd-using-powershell |
| Upload VHDs to DevTest Labs storage using AzCopy | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-upload-vhd-using-azcopy |
| Upload VHDs to DevTest Labs with PowerShell | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-upload-vhd-using-powershell |
| Upload VHDs to DevTest Labs via Storage Explorer | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-upload-vhd-using-storage-explorer |
| Automate DevTest Labs VM creation with PowerShell | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-vm-powershell |
| Manage DevTest Labs VMs using Azure CLI | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-vmcli |
| Extend DevTest Labs automation using Azure Functions | https://learn.microsoft.com/en-us/azure/devtest-labs/extend-devtest-labs-azure-functions |
| Import DevTest Labs VMs between labs via REST/PowerShell | https://learn.microsoft.com/en-us/azure/devtest-labs/import-virtual-machines-from-another-lab |
| Report DevTest Labs usage across labs and subscriptions | https://learn.microsoft.com/en-us/azure/devtest-labs/report-usage-across-multiple-labs-subscriptions |
| Automate DevTest Labs with Azure CLI scripts | https://learn.microsoft.com/en-us/azure/devtest-labs/samples-cli |
| Use Azure PowerShell scripts for DevTest Labs automation | https://learn.microsoft.com/en-us/azure/devtest-labs/samples-powershell |
| Control DevTest Labs VM start order with Automation | https://learn.microsoft.com/en-us/azure/devtest-labs/start-machines-use-automation-runbooks |
| Publish Visual Studio apps to DevTest Labs VMs | https://learn.microsoft.com/en-us/azure/devtest-labs/test-app-azure |
| Script DevTest Labs VM start/stop with CLI and PowerShell | https://learn.microsoft.com/en-us/azure/devtest-labs/use-command-line-start-stop-virtual-machines |

### Deployment
| Topic | URL |
|-------|-----|
| Integrate DevTest Labs with enterprise CI/CD pipelines | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-dev-ops |
| Handle Azure Basic Load Balancer retirement in DevTest Labs | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-standard-load-balancer |
| Deploy DevTest Labs resources with ARM templates | https://learn.microsoft.com/en-us/azure/devtest-labs/devtest-lab-use-arm-and-powershell-for-lab-resources |
| Move Azure DevTest Labs to another region | https://learn.microsoft.com/en-us/azure/devtest-labs/how-to-move-labs |