---
name: azure-dev-box
description: Expert knowledge for Azure Dev Box development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when designing Dev Box images, catalogs/pools, RBAC/SSO access, region moves, or VS Code dev tunnels, and other Azure Dev Box related development tasks. Not for Azure DevTest Labs (use azure-devtest-labs), Azure Virtual Machines (use azure-virtual-machines), Azure Virtual Desktop (use azure-virtual-desktop), Azure Lab Services (use azure-lab-services).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Dev Box Skill

This skill provides expert guidance for Azure Dev Box. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L45 | Diagnosing and fixing Dev Box connectivity issues, image validation errors, stale/inaccessible boxes, using Troubleshoot & Repair, and monitoring via Azure Monitor logs. |
| Best Practices | L46-L51 | Guidance on building efficient Dev Box images, including structuring image definitions and pre-warming Visual Studio caches to speed up developer environments. |
| Decision Making | L52-L57 | Guidance on planning Dev Box deployments (networking, images, capacity) and deciding or preparing to move from Dev Box to Windows 365, including design and transition considerations. |
| Limits & Quotas | L58-L63 | Managing Dev Box capacity: requesting quota/core limit increases and configuring per-user Dev Box limits to control usage and costs. |
| Security | L64-L75 | Securing Dev Box access and sessions: RBAC roles, guest access, SSO, API auth, Key Vault/service principals, Intune Conditional Access and Endpoint Privilege Management. |
| Configuration | L76-L102 | Configuring Dev Box infrastructure: networking, images, catalogs, policies, schedules (stop/hibernate/autodelete), pools/projects/dev centers, and monitoring/log schemas. |
| Integrations & Coding Patterns | L103-L107 | Using VS Code dev tunnels to securely connect to Azure Dev Box, including setup, authentication, and remote development workflow configuration. |
| Deployment | L108-L111 | Planning and rolling out Dev Box environments, including architecture and configuration, plus guidance for moving Dev Box pools and individual boxes between Azure regions. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose and fix Microsoft Dev Box connectivity | https://learn.microsoft.com/en-us/azure/dev-box/how-to-resolve-dev-box-connectivity-issues |
| Troubleshoot Dev Box custom image validation failures | https://learn.microsoft.com/en-us/azure/dev-box/how-to-troubleshoot-custom-image-validation |
| Fix stale or inaccessible Dev Boxes in Task view | https://learn.microsoft.com/en-us/azure/dev-box/how-to-troubleshoot-dev-box-task-view |
| Troubleshoot known Dev Box connectivity problems | https://learn.microsoft.com/en-us/azure/dev-box/how-to-troubleshoot-remote-desktop-connectivity |
| Use Dev Box Troubleshoot & Repair for connectivity | https://learn.microsoft.com/en-us/azure/dev-box/how-to-troubleshoot-repair-dev-box |
| Monitor Dev Box with Azure Monitor diagnostic logs | https://learn.microsoft.com/en-us/azure/dev-box/monitor-dev-box |

### Best Practices
| Topic | URL |
|-------|-----|
| Best practices for authoring Dev Box image definitions | https://learn.microsoft.com/en-us/azure/dev-box/concept-authoring-troubleshooting-guide-team-customizations |
| Pre-generate Visual Studio caches in Dev Box images | https://learn.microsoft.com/en-us/azure/dev-box/how-to-generate-visual-studio-caches |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan and design a Microsoft Dev Box deployment | https://learn.microsoft.com/en-us/azure/dev-box/concept-dev-box-deployment-guide |
| Plan transition from Dev Box to Windows 365 | https://learn.microsoft.com/en-us/azure/dev-box/dev-box-roadmap |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Request Dev Box quota and core limit increases | https://learn.microsoft.com/en-us/azure/dev-box/how-to-request-quota-increase |
| Set per-user Dev Box limits to control costs | https://learn.microsoft.com/en-us/azure/dev-box/tutorial-dev-box-limits |

### Security
| Topic | URL |
|-------|-----|
| Plan Azure RBAC roles for Dev Box deployments | https://learn.microsoft.com/en-us/azure/dev-box/concept-dev-box-role-based-access-control |
| Authenticate to Dev Box REST APIs with Azure CLI | https://learn.microsoft.com/en-us/azure/dev-box/how-to-authenticate |
| Secure Dev Box tunnels with conditional access policies | https://learn.microsoft.com/en-us/azure/dev-box/how-to-conditional-access-dev-tunnels-service |
| Configure Intune Conditional Access for Dev Box | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-intune-conditional-access-policies |
| Secure Dev Box customizations with Key Vault and service principals | https://learn.microsoft.com/en-us/azure/dev-box/how-to-customizations-connect-resource-repository |
| Set up Intune Endpoint Privilege Management for Dev Box | https://learn.microsoft.com/en-us/azure/dev-box/how-to-elevate-privilege-dev-box |
| Enable single sign-on to Windows on Dev Boxes | https://learn.microsoft.com/en-us/azure/dev-box/how-to-enable-single-sign-on |
| Assign Dev Box RBAC roles for project access | https://learn.microsoft.com/en-us/azure/dev-box/how-to-manage-dev-box-access |

### Configuration
| Topic | URL |
|-------|-----|
| Configure networking requirements for Microsoft Dev Box | https://learn.microsoft.com/en-us/azure/dev-box/concept-dev-box-network-requirements |
| Configure Dev Box auto-delete for unused environments | https://learn.microsoft.com/en-us/azure/dev-box/how-to-auto-delete-dev-box |
| Attach and configure Azure Compute Gallery for Dev Box | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-azure-compute-gallery |
| Add and manage Dev Box catalogs for image definitions | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-catalog |
| Configure Dev Box customization task catalogs | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-customization-tasks |
| Configure Dev Box hibernation and schedules | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-dev-box-hibernation |
| Configure imaging pipeline for Dev Box team customizations | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-dev-center-imaging |
| Configure Dev Box network connections and VNets | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-network-connections |
| Configure Dev Box project policies for governance | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-project-policy |
| Configure Dev Box pool autostop schedules | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-stop-schedule |
| Author Dev Box image definition files for team customizations | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-team-customizations |
| Create and upload Dev Box user customization files | https://learn.microsoft.com/en-us/azure/dev-box/how-to-configure-user-customizations |
| Configure virtual switches and networking in Dev Box | https://learn.microsoft.com/en-us/azure/dev-box/how-to-connect-dev-box-virtual-switch |
| Build custom Dev Box images with Azure VM Image Builder | https://learn.microsoft.com/en-us/azure/dev-box/how-to-customize-devbox-azure-image-builder |
| Define and manage Dev Box definitions | https://learn.microsoft.com/en-us/azure/dev-box/how-to-manage-dev-box-definitions |
| Configure and manage Dev Box pools | https://learn.microsoft.com/en-us/azure/dev-box/how-to-manage-dev-box-pools |
| Manage Microsoft Dev Box projects and pools | https://learn.microsoft.com/en-us/azure/dev-box/how-to-manage-dev-box-projects |
| Create and manage Dev Box dev centers | https://learn.microsoft.com/en-us/azure/dev-box/how-to-manage-dev-center |
| Configure custom Windows images for Microsoft Dev Box | https://learn.microsoft.com/en-us/azure/dev-box/how-to-prepare-custom-image-dev-box |
| Reference for Dev Box monitoring logs and metrics | https://learn.microsoft.com/en-us/azure/dev-box/monitor-dev-box-reference |
| Configure core Microsoft Dev Box resources | https://learn.microsoft.com/en-us/azure/dev-box/quickstart-configure-dev-box-service |
| Configure Dev Box resources with Get Started template | https://learn.microsoft.com/en-us/azure/dev-box/quickstart-get-started-template |
| Configure Dev Box imagedefinition.yaml and task.yaml schemas | https://learn.microsoft.com/en-us/azure/dev-box/reference-dev-box-customizations |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect to Dev Box from VS Code using dev tunnels | https://learn.microsoft.com/en-us/azure/dev-box/how-to-set-up-dev-tunnels |

### Deployment
| Topic | URL |
|-------|-----|
| Move Dev Box pools and boxes between regions | https://learn.microsoft.com/en-us/azure/dev-box/how-to-move-dev-box-pool-region |