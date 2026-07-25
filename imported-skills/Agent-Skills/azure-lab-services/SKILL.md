---
name: azure-lab-services
description: Expert knowledge for Azure Lab Services development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring lab plans, VM templates/schedules, VNet-integrated labs, GPU/nested virtualization, or Canvas/Teams integration, and other Azure Lab Services related development tasks. Not for Azure DevTest Labs (use azure-devtest-labs), Azure Virtual Machines (use azure-virtual-machines), Azure Virtual Desktop (use azure-virtual-desktop).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure Lab Services Skill

This skill provides expert guidance for Azure Lab Services. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L44 | Diagnosing and fixing VM access, connectivity, deployment, and lab-creation issues in Azure Lab Services, including when to redeploy or reimage VMs. |
| Best Practices | L45-L53 | Governance and setup guidance for lab plans, custom images, nested virtualization, Linux graphical RDP, and preparing optimized Windows template VMs in Azure Lab Services |
| Decision Making | L54-L65 | Guidance on when and how to use Azure Lab Services: choosing lab types, planning migrations (physical or to other services), cost estimation, GPU sizing, and running training or hackathon scenarios. |
| Architecture & Design Patterns | L66-L72 | Core Azure Lab Services architecture, supported networking topologies, and design patterns for building reliable, resilient lab environments and lab plans |
| Limits & Quotas | L73-L80 | VM capacity and core quotas for labs, how to view usage, request quota increases, and timelines for automatic VM deletion and cleanup. |
| Security | L81-L95 | RBAC roles, lab creator/owner assignment, Azure Policy for compliance and VM size limits, firewall and public IP setup, and educator/student VM password management. |
| Configuration | L96-L126 | Configuring Azure Lab Services: lab plans, regions, images, networking, VM templates, schedules (start/stop/shutdown), capacity, GPU/nested virtualization, and user/educator access. |
| Integrations & Coding Patterns | L127-L140 | Integrating Lab Services with Canvas and Teams, automating lab creation via Bicep/PowerShell/Python, connecting labs to VNets, and remote access to Linux VMs with X2Go. |
| Deployment | L141-L150 | Creating and importing Windows/Linux lab VM images (from Azure VMs, physical labs, or compute galleries), rapidly setting up/publishing labs, and migrating lab accounts to lab plans. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Lab Services VMs by redeploying or reimaging | https://learn.microsoft.com/en-us/azure/lab-services/how-to-reset-and-redeploy-vm |
| Troubleshoot access problems for Azure Lab Services VMs | https://learn.microsoft.com/en-us/azure/lab-services/troubleshoot-access-lab-vm |
| Troubleshoot connectivity issues in Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/troubleshoot-connect-lab-vm |
| Troubleshoot Azure Lab Services lab creation issues | https://learn.microsoft.com/en-us/azure/lab-services/troubleshoot-lab-creation |

### Best Practices
| Topic | URL |
|-------|-----|
| Administer lab plans and governance for Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/administrator-guide |
| Recommended approaches for Azure Lab custom images | https://learn.microsoft.com/en-us/azure/lab-services/approaches-for-custom-image-creation |
| Configure nested virtualization in Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/concept-nested-virtualization-template-vm |
| Enable graphical remote desktop for Linux labs with optimal performance | https://learn.microsoft.com/en-us/azure/lab-services/how-to-enable-remote-desktop-linux |
| Best practices for preparing Windows lab templates | https://learn.microsoft.com/en-us/azure/lab-services/how-to-prepare-windows-template |

### Decision Making
| Topic | URL |
|-------|-----|
| Use Azure Lab Services for training scenarios | https://learn.microsoft.com/en-us/azure/lab-services/classroom-labs-scenarios |
| Choose between lab accounts and lab plans | https://learn.microsoft.com/en-us/azure/lab-services/concept-lab-accounts-versus-lab-plans |
| Plan migration from physical labs to Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/concept-migrating-physical-labs |
| Estimate and analyze Azure Lab Services costs | https://learn.microsoft.com/en-us/azure/lab-services/cost-management-guide |
| Run hackathons using Azure Lab Services environments | https://learn.microsoft.com/en-us/azure/lab-services/hackathon-labs |
| Choose and configure GPU VM sizes for Azure labs | https://learn.microsoft.com/en-us/azure/lab-services/how-to-setup-lab-gpu |
| Plan migration before Azure Lab Services retirement | https://learn.microsoft.com/en-us/azure/lab-services/retirement-guide |
| Decide when to transition from Azure Lab Services to DevTest Labs | https://learn.microsoft.com/en-us/azure/lab-services/transition-devtest-labs-guidance |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Understand Azure Lab Services architecture fundamentals | https://learn.microsoft.com/en-us/azure/lab-services/classroom-labs-fundamentals |
| Select supported networking architectures for lab plans | https://learn.microsoft.com/en-us/azure/lab-services/concept-lab-services-supported-networking-scenarios |
| Understand reliability and resiliency in Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/reliability-in-azure-lab-services |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review VM capacity limits and quotas for labs | https://learn.microsoft.com/en-us/azure/lab-services/capacity-limits |
| Determine Azure Lab Services quota and core usage | https://learn.microsoft.com/en-us/azure/lab-services/how-to-determine-your-quota-usage |
| Request Azure Lab Services core quota increases | https://learn.microsoft.com/en-us/azure/lab-services/how-to-request-capacity-increase |
| Understand automatic VM deletion policy timelines | https://learn.microsoft.com/en-us/azure/lab-services/vm-deletion-policy |

### Security
| Topic | URL |
|-------|-----|
| Assign Lab Creator role in Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/add-lab-creator |
| Enforce Azure Lab Services compliance with Azure Policy | https://learn.microsoft.com/en-us/azure/lab-services/azure-polices-for-lab-services |
| Use Azure RBAC roles with Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/concept-lab-services-role-based-access-control |
| Map role assignments from lab accounts to lab plans | https://learn.microsoft.com/en-us/azure/lab-services/concept-migrate-from-lab-accounts-roles |
| Assign Lab Creator role for Azure Lab Services accounts | https://learn.microsoft.com/en-us/azure/lab-services/how-to-add-lab-creator |
| Add additional lab owners in Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/how-to-add-user-lab-owner |
| Determine lab VM public IPs for firewall configuration | https://learn.microsoft.com/en-us/azure/lab-services/how-to-configure-firewall-settings |
| Configure firewall rules for Azure Lab Services lab VMs | https://learn.microsoft.com/en-us/azure/lab-services/how-to-configure-firewall-settings-1 |
| Set and reset lab VM passwords as an educator | https://learn.microsoft.com/en-us/azure/lab-services/how-to-set-virtual-machine-passwords |
| Students resetting passwords for Azure Lab Services VMs | https://learn.microsoft.com/en-us/azure/lab-services/how-to-set-virtual-machine-passwords-student |
| Restrict Azure Lab VM sizes using Azure Policy | https://learn.microsoft.com/en-us/azure/lab-services/how-to-use-restrict-allowed-virtual-machine-sku-sizes-policy |

### Configuration
| Topic | URL |
|-------|-----|
| Allow lab creators to choose lab locations in Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/allow-lab-creator-pick-lab-location |
| Configure allowed regions for Azure Lab Services labs | https://learn.microsoft.com/en-us/azure/lab-services/create-and-configure-labs-admin |
| Attach or detach Azure compute galleries to lab plans | https://learn.microsoft.com/en-us/azure/lab-services/how-to-attach-detach-shared-image-gallery |
| Attach or detach Shared Image Gallery to Azure Lab Services accounts | https://learn.microsoft.com/en-us/azure/lab-services/how-to-attach-detach-shared-image-gallery-1 |
| Configure auto-shutdown policies for Azure Lab plans | https://learn.microsoft.com/en-us/azure/lab-services/how-to-configure-auto-shutdown-lab-plans |
| Configure automatic VM shutdown for Azure Lab Services accounts | https://learn.microsoft.com/en-us/azure/lab-services/how-to-configure-lab-accounts |
| Connect lab plans to virtual networks with VNET injection | https://learn.microsoft.com/en-us/azure/lab-services/how-to-connect-vnet-injection |
| Create Azure Lab Services labs with shared resources | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-a-lab-with-shared-resource-1 |
| Define lab plans with Bicep or ARM templates | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-lab-plan-bicep |
| Create a lab plan using Azure PowerShell | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-lab-plan-powershell |
| Programmatically create lab plans using Python SDK | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-lab-plan-python |
| Create and manage Azure Lab Services VM templates | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-manage-template |
| Configure automatic start/stop schedules for lab VMs | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-schedules |
| Enable nested virtualization in Azure Lab Services templates | https://learn.microsoft.com/en-us/azure/lab-services/how-to-enable-nested-virtualization-template-vm-using-script |
| Configure automatic shutdown on user disconnect for labs | https://learn.microsoft.com/en-us/azure/lab-services/how-to-enable-shutdown-disconnect |
| Create, view, and delete Azure Lab Services lab plans | https://learn.microsoft.com/en-us/azure/lab-services/how-to-manage-lab-plans |
| Configure and manage Azure Lab Services users and usage hours | https://learn.microsoft.com/en-us/azure/lab-services/how-to-manage-lab-users |
| Manage Azure Lab Services VM pool capacity and states | https://learn.microsoft.com/en-us/azure/lab-services/how-to-manage-vm-pool |
| Set up GPU-based labs in Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/how-to-setup-lab-gpu-1 |
| Configure Windows lab VMs to prevent OS-level shutdown | https://learn.microsoft.com/en-us/azure/lab-services/how-to-windows-shutdown |
| Allow educators to access student VMs in Azure labs | https://learn.microsoft.com/en-us/azure/lab-services/instructor-access-virtual-machines |
| Configure support contact information for Azure lab accounts | https://learn.microsoft.com/en-us/azure/lab-services/lab-account-owner-support-information |
| Quickly configure a lab plan for your school | https://learn.microsoft.com/en-us/azure/lab-services/lab-plan-setup-guide |
| Azure Policy built-in definitions for Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/policy-reference |
| Configure allowed Azure Marketplace images for labs | https://learn.microsoft.com/en-us/azure/lab-services/specify-marketplace-images |
| Specify allowed Marketplace images for Azure Lab Services labs | https://learn.microsoft.com/en-us/azure/lab-services/specify-marketplace-images-1 |
| Configure advanced networking for Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/tutorial-create-lab-with-advanced-networking |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect to Linux lab VMs using X2Go | https://learn.microsoft.com/en-us/azure/lab-services/connect-virtual-machine-linux-x2go |
| Configure Canvas LMS integration with Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/how-to-configure-canvas-for-lab-plans |
| Configure Microsoft Teams integration with Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/how-to-configure-teams-for-lab-plans |
| Connect Azure Lab Services labs to peer virtual networks | https://learn.microsoft.com/en-us/azure/lab-services/how-to-connect-peer-virtual-network |
| Provision Azure Lab Services labs with Bicep templates | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-lab-bicep |
| Create Azure Lab Services labs using PowerShell Az module | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-lab-powershell |
| Create Azure Lab Services labs using the Python SDK | https://learn.microsoft.com/en-us/azure/lab-services/how-to-create-lab-python |
| Integrate Azure Lab Services with Canvas LMS | https://learn.microsoft.com/en-us/azure/lab-services/lab-services-within-canvas-overview |
| Integrate Azure Lab Services with Microsoft Teams | https://learn.microsoft.com/en-us/azure/lab-services/lab-services-within-teams-overview |
| Use the Az.LabServices PowerShell module for Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/reference-powershell-module |

### Deployment
| Topic | URL |
|-------|-----|
| Import Linux custom images from Azure VMs into labs | https://learn.microsoft.com/en-us/azure/lab-services/how-to-bring-custom-linux-image-azure-vm |
| Import Linux images from physical labs into Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/how-to-bring-custom-linux-image-vhd |
| Create Azure Lab Services labs from Windows VM images | https://learn.microsoft.com/en-us/azure/lab-services/how-to-bring-custom-windows-image-azure-vm |
| Migrate Azure Lab Services accounts to lab plans | https://learn.microsoft.com/en-us/azure/lab-services/how-to-migrate-lab-acounts-to-lab-plans |
| Use Azure compute galleries to provide lab VM images | https://learn.microsoft.com/en-us/azure/lab-services/how-to-use-shared-image-gallery |
| Rapidly create and publish a lab for students | https://learn.microsoft.com/en-us/azure/lab-services/setup-guide |
| Import Windows images from physical labs into Azure Lab Services | https://learn.microsoft.com/en-us/azure/lab-services/upload-custom-image-shared-image-gallery |