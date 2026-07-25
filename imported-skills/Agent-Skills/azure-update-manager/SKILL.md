---
name: azure-update-manager
description: Expert knowledge for Azure Update Manager development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when onboarding VMs/Arc servers, configuring patch schedules/ESU, using Change Tracking, or calling Update Manager APIs, and other Azure Update Manager related development tasks. Not for Azure Automation (use azure-automation), Azure Policy (use azure-policy), Azure Monitor (use azure-monitor).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Update Manager Skill

This skill provides expert guidance for Azure Update Manager. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L42 | Diagnosing and fixing onboarding failures, extension/agent issues, and common errors when using Azure Update Manager, Automanage, and Change Tracking. |
| Best Practices | L43-L53 | Best practices for configuring Automanage and guest patching on Windows/Linux/Arc VMs, handling SQL Server and Ubuntu/Ubuntu Pro updates, and managing SMB over QUIC in Update Manager. |
| Decision Making | L54-L59 | Planning patch strategies across subscriptions and guidance for migrating patch management from Configuration Manager to Azure Update Manager |
| Limits & Quotas | L60-L68 | OS, region, image, and workload support limits for Update Manager, including supported update sources/types, change tracking matrix, and unsupported scenarios. |
| Security | L69-L74 | Configuring disk encryption for Automanaged VMs and setting up RBAC roles/permissions to securely manage and control access to Azure Update Manager. |
| Configuration | L75-L94 | Configuring Update Manager behavior: update schedules, scopes, alerts, ESU, Automanage profiles, Change Tracking, Resource Graph queries, and policy-based or cross-subscription patching. |
| Integrations & Coding Patterns | L95-L107 | Using SDKs (Go/Java/JS/Python) and REST APIs to assign Automanage profiles, manage VM/Arc server updates, and implement pre/post maintenance with Functions, webhooks, and runbooks |
| Deployment | L108-L120 | Deploying and managing Automanage/Update Manager at scale: onboarding VMs and Arc servers, moving/repairing configs across regions/tenants, policies, extension versions, and supported OS/features. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Automanage onboarding failures and errors | https://learn.microsoft.com/en-us/azure/automanage/common-errors |
| Resolve Azure Change Tracking extension issues | https://learn.microsoft.com/en-us/azure/azure-change-tracking-inventory/extension-version-details |
| Troubleshoot errors and issues in Azure Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/troubleshoot |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply Automanage best practices to Azure Arc-enabled servers | https://learn.microsoft.com/en-us/azure/automanage/automanage-arc |
| Apply Automanage best practices to Linux VMs | https://learn.microsoft.com/en-us/azure/automanage/automanage-linux |
| Manage SMB over QUIC using Automanage best practices | https://learn.microsoft.com/en-us/azure/automanage/automanage-smb-over-quic |
| Apply Automanage best practices to Windows Server VMs | https://learn.microsoft.com/en-us/azure/automanage/automanage-windows-server |
| Apply patching best practices for SQL Server on Azure VMs | https://learn.microsoft.com/en-us/azure/update-manager/guidance-patching-sql-server-azure-vm |
| Handle Ubuntu security and Ubuntu Pro in Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/security-awareness-ubuntu-support |
| Configure automatic guest patching for Azure VMs | https://learn.microsoft.com/en-us/azure/update-manager/support-matrix-automatic-guest-patching |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan cross-subscription patching with Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/cross-subscription-patching |
| Plan migration from Configuration Manager to Azure Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/guidance-migration-azure |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Change Tracking support matrix and limitations | https://learn.microsoft.com/en-us/azure/azure-change-tracking-inventory/change-tracking-inventory-support-matrix |
| Manage customized images in Azure Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/manage-updates-customized-images |
| Understand supported update sources and types | https://learn.microsoft.com/en-us/azure/update-manager/support-matrix |
| Check supported Azure regions for Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/supported-regions |
| Identify unsupported workloads in Azure Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/unsupported-workloads |

### Security
| Topic | URL |
|-------|-----|
| Configure Azure disk encryption for Automanaged VMs | https://learn.microsoft.com/en-us/azure/automanage/overview-azure-disk-encryption |
| Assign RBAC roles for Azure Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/roles-permissions |

### Configuration
| Topic | URL |
|-------|-----|
| Create and configure custom Automanage profiles for VMs | https://learn.microsoft.com/en-us/azure/automanage/virtual-machines-custom-profile |
| Create data collection rules for Azure Change Tracking | https://learn.microsoft.com/en-us/azure/azure-change-tracking-inventory/create-data-collection-rule |
| Configure workspaces and data collection rules for Change Tracking | https://learn.microsoft.com/en-us/azure/azure-change-tracking-inventory/tutorial-change-workspace-configure-data-collection-rule |
| Configure Windows Update client for Azure Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/configure-wu-agent |
| Set up cross-subscription patching in Azure | https://learn.microsoft.com/en-us/azure/update-manager/enable-cross-subscription-patching |
| Enroll Windows Server ESU with Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/extended-security-updates |
| Enable and configure alerts in Azure Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/manage-alerts |
| Configure and manage dynamic scopes for patching | https://learn.microsoft.com/en-us/azure/update-manager/manage-dynamic-scoping |
| Manage existing pre and post maintenance events | https://learn.microsoft.com/en-us/azure/update-manager/manage-pre-post-events |
| Manage update configuration settings in Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/manage-update-settings |
| Create custom Update Manager reports with workbooks | https://learn.microsoft.com/en-us/azure/update-manager/manage-workbooks |
| Enable periodic assessment via Azure Policy | https://learn.microsoft.com/en-us/azure/update-manager/periodic-assessment-at-scale |
| Create pre and post maintenance events in Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/pre-post-events-schedule-maintenance-configuration |
| Access Update Manager data via Azure Resource Graph | https://learn.microsoft.com/en-us/azure/update-manager/query-logs |
| Use sample Resource Graph queries for Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/sample-query-logs |
| Configure recurring update schedules in Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/scheduled-patching |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Go SDK to assign Automanage configuration profiles | https://learn.microsoft.com/en-us/azure/automanage/quick-go-sdk |
| Use Java SDK to assign Automanage configuration profiles | https://learn.microsoft.com/en-us/azure/automanage/quick-java-sdk |
| Use JavaScript SDK to assign Automanage configuration profiles | https://learn.microsoft.com/en-us/azure/automanage/quick-javascript-sdk |
| Use Python SDK to assign Automanage configuration profiles | https://learn.microsoft.com/en-us/azure/automanage/quick-python-sdk |
| Choose and use Automanage SDKs across languages | https://learn.microsoft.com/en-us/azure/automanage/reference-sdk |
| Use REST API for Arc-enabled server updates | https://learn.microsoft.com/en-us/azure/update-manager/manage-arc-enabled-servers-programmatically |
| Use Azure REST API to manage VM updates | https://learn.microsoft.com/en-us/azure/update-manager/manage-vms-programmatically |
| Implement pre/post maintenance using Azure Functions | https://learn.microsoft.com/en-us/azure/update-manager/tutorial-using-functions |
| Trigger pre/post maintenance via webhooks and runbooks | https://learn.microsoft.com/en-us/azure/update-manager/tutorial-webhooks-using-runbooks |

### Deployment
| Topic | URL |
|-------|-----|
| Onboard VMs to Automanage with ARM templates | https://learn.microsoft.com/en-us/azure/automanage/arm-deploy |
| Onboard Arc-enabled servers to Automanage with ARM templates | https://learn.microsoft.com/en-us/azure/automanage/arm-deploy-arc |
| Upgrade existing Automanage machines to the latest version | https://learn.microsoft.com/en-us/azure/automanage/automanage-upgrade |
| Move Automanage configuration profiles between Azure regions | https://learn.microsoft.com/en-us/azure/automanage/move-automanaged-configuration-profile |
| Move Automanaged virtual machines across Azure regions | https://learn.microsoft.com/en-us/azure/automanage/move-automanaged-vms |
| Repair Automanage accounts after subscription tenant moves | https://learn.microsoft.com/en-us/azure/automanage/repair-automanage-account |
| Enable Automanage for VMs using Azure Policy | https://learn.microsoft.com/en-us/azure/automanage/virtual-machines-policy-enable |
| Deploy Change Tracking at scale using Azure Policy | https://learn.microsoft.com/en-us/azure/azure-change-tracking-inventory/enable-change-tracking-at-scale-policy |
| Track Arc-enabled VM extension releases and issues for Update Manager | https://learn.microsoft.com/en-us/azure/update-manager/overview-arc-enabled-vm-extensions |
| Azure Update Manager OS and feature support matrix | https://learn.microsoft.com/en-us/azure/update-manager/support-matrix-updates |