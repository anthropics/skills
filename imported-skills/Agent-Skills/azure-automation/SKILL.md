---
name: azure-automation
description: Expert knowledge for Azure Automation development including troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building Azure Automation runbooks, DSC/State Configuration, Hybrid Runbook Workers, Private Link, or AMA-based Change Tracking, and other Azure Automation related development tasks. Not for Azure Functions (use azure-functions), Azure Logic Apps (use azure-logic-apps), Azure Scheduler (use azure-scheduler), Azure Update Manager (use azure-update-manager).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Automation Skill

This skill provides expert guidance for Azure Automation. Covers troubleshooting, best practices, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L46 | Diagnosing and fixing Azure Automation issues: runbook failures, DSC/State Configuration, Hybrid Runbook Workers, managed identities, shared resources, and collecting logs for support. |
| Best Practices | L47-L56 | Best practices for structuring and running Automation runbooks: modular parent-child design, execution patterns, error handling, stream/output usage, and avoiding context/locking issues. |
| Decision Making | L57-L65 | Guidance for planning and migrating Azure Automation: runbook types, Orchestrator/runbook/agent/Hybrid Worker migrations, Run As → managed identity, and module/AzureRM to Az updates. |
| Limits & Quotas | L66-L72 | Azure Automation capacity limits, quotas, and supported configurations, plus Change Tracking & Inventory support details when using the Azure Monitor Agent (AMA). |
| Security | L73-L93 | Securing Automation accounts: identities (system/user-assigned), RBAC, auth methods, encryption, certificates/credentials, Private Link, Azure Policy, and Terraform-based secure provisioning. |
| Configuration | L94-L137 | Configuring Azure Automation runbooks, DSC/State Configuration, Hybrid Runbook Workers, schedules, modules/packages, alerts, policies, and integrations (VS Code, source control, ARM, Azure Monitor). |
| Integrations & Coding Patterns | L138-L150 | Patterns for integrating runbooks with AWS, ARM/SQL/Office 365, webhooks, email (SendGrid), Azure Monitor logging, and using the graphical runbook SDK with managed identities |
| Deployment | L151-L159 | Guides for deploying resilient Automation accounts, setting up disaster recovery, and installing/configuring Hybrid Runbook Workers (Windows/Linux, agent- and extension-based) plus DSC/Chocolatey CI/CD. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Collect diagnostic data for Azure Automation support cases | https://learn.microsoft.com/en-us/azure/automation/troubleshoot/collect-data-microsoft-azure-automation-case |
| Troubleshoot Azure Automation State Configuration problems | https://learn.microsoft.com/en-us/azure/automation/troubleshoot/desired-state-configuration |
| Troubleshoot extension-based Hybrid Runbook Worker failures | https://learn.microsoft.com/en-us/azure/automation/troubleshoot/extension-based-hybrid-runbook-worker |
| Troubleshoot agent-based Hybrid Runbook Worker issues | https://learn.microsoft.com/en-us/azure/automation/troubleshoot/hybrid-runbook-worker |
| Troubleshoot managed identity issues in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/troubleshoot/managed-identity |
| Diagnose and fix Azure Automation runbook issues | https://learn.microsoft.com/en-us/azure/automation/troubleshoot/runbooks |
| Troubleshoot Azure Automation shared resource problems | https://learn.microsoft.com/en-us/azure/automation/troubleshoot/shared-resources |

### Best Practices
| Topic | URL |
|-------|-----|
| Design modular parent-child runbooks in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-child-runbooks |
| Design and manage Azure Automation runbook execution | https://learn.microsoft.com/en-us/azure/automation/automation-runbook-execution |
| Implement error handling in Azure Automation graphical runbooks | https://learn.microsoft.com/en-us/azure/automation/automation-runbook-graphical-error-handling |
| Configure output and message streams in Automation runbooks | https://learn.microsoft.com/en-us/azure/automation/automation-runbook-output-and-messages |
| Avoid context switching issues in Azure Automation runbooks | https://learn.microsoft.com/en-us/azure/automation/context-switching |
| Manage Azure Automation runbooks with recommended design patterns | https://learn.microsoft.com/en-us/azure/automation/manage-runbooks |

### Decision Making
| Topic | URL |
|-------|-----|
| Migrate System Center Orchestrator runbooks to Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-orchestrator-migration |
| Choose appropriate Azure Automation runbook types | https://learn.microsoft.com/en-us/azure/automation/automation-runbook-types |
| Migrate Change Tracking from Log Analytics agent to AMA | https://learn.microsoft.com/en-us/azure/automation/change-tracking/guidance-migration-log-analytics-monitoring-agent |
| Migrate agent-based Hybrid Workers to extension-based workers | https://learn.microsoft.com/en-us/azure/automation/migrate-existing-agent-based-hybrid-worker-to-extension-based-workers |
| Plan and execute migration from Run As to managed identities | https://learn.microsoft.com/en-us/azure/automation/migrate-run-as-accounts-managed-identity |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| View and manage Azure Automation limits and quotas | https://learn.microsoft.com/en-us/azure/automation/automation-limits-quotas |
| Azure Automation subscription limits and quotas reference | https://learn.microsoft.com/en-us/azure/automation/automation-subscription-limits-faq |
| Support matrix for Change Tracking and Inventory with AMA | https://learn.microsoft.com/en-us/azure/azure-change-tracking-inventory/change-tracking-inventory-support-matrix |

### Security
| Topic | URL |
|-------|-----|
| Configure user-assigned managed identity for Azure Automation | https://learn.microsoft.com/en-us/azure/automation/add-user-assigned-identity |
| Understand and configure Azure Automation data security | https://learn.microsoft.com/en-us/azure/automation/automation-managing-data |
| Assign Azure RBAC roles and permissions for Automation accounts | https://learn.microsoft.com/en-us/azure/automation/automation-role-based-access-control |
| Configure encryption for secure assets in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-secure-asset-encryption |
| Apply security best practices for Azure Automation accounts | https://learn.microsoft.com/en-us/azure/automation/automation-security-guidelines |
| Configure authentication methods for Azure Automation accounts | https://learn.microsoft.com/en-us/azure/automation/automation-security-overview |
| Configure Microsoft Entra ID authentication for Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-use-azure-ad |
| Disable local authentication for Azure Automation securely | https://learn.microsoft.com/en-us/azure/automation/disable-local-authentication |
| Disable system-assigned managed identity in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/disable-managed-identity-for-automation |
| Enable system-assigned managed identity for Azure Automation | https://learn.microsoft.com/en-us/azure/automation/enable-managed-identity-for-automation |
| Secure Azure Automation access with Private Link and private endpoints | https://learn.microsoft.com/en-us/azure/automation/how-to/private-link-security |
| Use managed identity in Azure Automation PowerShell runbooks | https://learn.microsoft.com/en-us/azure/automation/learn/powershell-runbook-managed-identity |
| Provision Automation account and Reader role via Terraform | https://learn.microsoft.com/en-us/azure/automation/quickstarts/create-azure-automation-account-terraform |
| Enable managed identities for Azure Automation accounts | https://learn.microsoft.com/en-us/azure/automation/quickstarts/enable-managed-identity |
| Apply Azure Policy compliance controls to Automation | https://learn.microsoft.com/en-us/azure/automation/security-controls-policy |
| Securely manage certificates for Azure Automation runbooks and DSC | https://learn.microsoft.com/en-us/azure/automation/shared-resources/certificates |
| Create and use credential assets securely in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/shared-resources/credentials |

### Configuration
| Topic | URL |
|-------|-----|
| Configure metric alerts for Azure Automation runbooks | https://learn.microsoft.com/en-us/azure/automation/automation-alert-metric |
| Configure and use connection assets in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-connections |
| Trigger Azure Automation runbooks from Azure Monitor alerts | https://learn.microsoft.com/en-us/azure/automation/automation-create-alert-triggered-runbook |
| Compile DSC configurations in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-compile |
| Configure DSC data at scale in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-config-data-at-scale |
| Generate DSC configurations from existing servers | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-config-from-server |
| Configure STIG-based DSC data in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-configuration-based-on-stig |
| Convert DSC configurations to composite resources | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-create-composite |
| Send State Configuration data to Azure Monitor Logs | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-diagnostics |
| Use Azure DSC extension versions and capabilities | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-extension-history |
| Configure core Azure Automation State Configuration tasks | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-getting-started |
| Enable and onboard machines to State Configuration | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-onboarding |
| Remediate noncompliant servers with State Configuration | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-remediate |
| Use the Azure Automation textual editor for PowerShell runbooks | https://learn.microsoft.com/en-us/azure/automation/automation-edit-textual-runbook |
| Author and configure graphical runbooks in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/automation-graphical-authoring-intro |
| Configure and run runbooks on Hybrid Runbook Workers | https://learn.microsoft.com/en-us/azure/automation/automation-hrw-run-runbooks |
| Configure and use Azure Automation Hybrid Runbook Worker | https://learn.microsoft.com/en-us/azure/automation/automation-hybrid-runbook-worker |
| Configure network requirements for Azure Automation components | https://learn.microsoft.com/en-us/azure/automation/automation-network-configuration |
| Author and manage Automation runbooks using VS Code | https://learn.microsoft.com/en-us/azure/automation/automation-runbook-authoring |
| Create watcher tasks to track file updates in Automation | https://learn.microsoft.com/en-us/azure/automation/automation-scenario-using-watcher-task |
| Configure and update Azure PowerShell modules in Automation | https://learn.microsoft.com/en-us/azure/automation/automation-update-azure-modules |
| Compose DSC configurations using composite resources | https://learn.microsoft.com/en-us/azure/automation/compose-configurationwithcompositeresources |
| Enforce Hybrid Runbook Worker job execution via policy | https://learn.microsoft.com/en-us/azure/automation/enforce-job-execution-hybrid-worker |
| Configure Azure Automation regional DNS records for firewalled networks | https://learn.microsoft.com/en-us/azure/automation/how-to/automation-region-dns-records |
| Configure runtime environments and associated runbooks in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/manage-runtime-environment |
| Use built-in Azure Policy definitions for Automation | https://learn.microsoft.com/en-us/azure/automation/policy-reference |
| Import and manage Python 3 packages in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/python-3-packages |
| Import and manage Python 2 packages in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/python-packages |
| Deploy Azure Automation account via ARM template | https://learn.microsoft.com/en-us/azure/automation/quickstart-create-automation-account-template |
| Configure input parameters for Azure Automation runbooks | https://learn.microsoft.com/en-us/azure/automation/runbook-input-parameters |
| Understand and configure Azure Automation runtime environments | https://learn.microsoft.com/en-us/azure/automation/runtime-environment-overview |
| Configure and manage PowerShell modules in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/shared-resources/modules |
| Configure schedules for Azure Automation runbooks | https://learn.microsoft.com/en-us/azure/automation/shared-resources/schedules |
| Define and use variable assets in Azure Automation | https://learn.microsoft.com/en-us/azure/automation/shared-resources/variables |
| Configure Azure Automation source control integration | https://learn.microsoft.com/en-us/azure/automation/source-control-integration |
| Choose methods to start Azure Automation runbooks | https://learn.microsoft.com/en-us/azure/automation/start-runbooks |
| Remove DSC configuration and unregister Automation node | https://learn.microsoft.com/en-us/azure/automation/state-configuration/remove-node-and-configuration-package |
| Configure machines to desired state with State Configuration | https://learn.microsoft.com/en-us/azure/automation/tutorial-configure-servers-desired-state |
| Enable Change Tracking and Inventory at scale via Machines pane | https://learn.microsoft.com/en-us/azure/azure-change-tracking-inventory/enable-change-tracking-at-scale-machines-blade |
| Enable Change Tracking and Inventory at scale with Azure Policy | https://learn.microsoft.com/en-us/azure/azure-change-tracking-inventory/enable-change-tracking-at-scale-policy |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Configure Azure Automation runbooks to authenticate with AWS | https://learn.microsoft.com/en-us/azure/automation/automation-config-aws-account |
| Deploy ARM templates from Azure Automation PowerShell runbooks | https://learn.microsoft.com/en-us/azure/automation/automation-deploy-template-runbook |
| Forward Azure Automation job logs to Azure Monitor | https://learn.microsoft.com/en-us/azure/automation/automation-manage-send-joblogs-log-analytics |
| Provision AWS virtual machines using Azure Automation runbooks | https://learn.microsoft.com/en-us/azure/automation/automation-scenario-aws-deployment |
| Send email from Azure Automation runbook using SendGrid | https://learn.microsoft.com/en-us/azure/automation/automation-send-email |
| Trigger Azure Automation runbooks using webhooks | https://learn.microsoft.com/en-us/azure/automation/automation-webhooks |
| Use the Azure Automation graphical runbook SDK | https://learn.microsoft.com/en-us/azure/automation/graphical-runbook-sdk |
| Manage Office 365 services with Azure Automation | https://learn.microsoft.com/en-us/azure/automation/manage-office-365 |
| Manage Azure SQL databases using Automation managed identity | https://learn.microsoft.com/en-us/azure/automation/manage-sql-server-in-automation |

### Deployment
| Topic | URL |
|-------|-----|
| Use availability zones for resilient Azure Automation deployments | https://learn.microsoft.com/en-us/azure/automation/automation-availability-zones |
| Plan disaster recovery for Azure Automation accounts | https://learn.microsoft.com/en-us/azure/automation/automation-disaster-recovery |
| Set up continuous deployment with DSC and Chocolatey | https://learn.microsoft.com/en-us/azure/automation/automation-dsc-cd-chocolatey |
| Deploy Linux Hybrid Runbook Worker agent | https://learn.microsoft.com/en-us/azure/automation/automation-linux-hrw-install |
| Deploy agent-based Windows Hybrid Runbook Workers in Automation | https://learn.microsoft.com/en-us/azure/automation/automation-windows-hrw-install |
| Deploy extension-based Hybrid Runbook Workers on Windows and Linux | https://learn.microsoft.com/en-us/azure/automation/extension-based-hybrid-runbook-worker-install |