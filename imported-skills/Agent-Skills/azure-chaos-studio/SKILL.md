---
name: azure-chaos-studio
description: Expert knowledge for Chaos Studio development including troubleshooting, limits & quotas, security, configuration, and integrations & coding patterns. Use when designing Chaos experiments, configuring agents/targets, securing access, using REST/CLI, or wiring telemetry, and other Chaos Studio related development tasks. Not for Azure Monitor (use azure-monitor), Azure Resiliency (use azure-resiliency), Azure Reliability (use azure-reliability), Azure Site Recovery (use azure-site-recovery).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Chaos Studio Skill

This skill provides expert guidance for Chaos Studio. Covers troubleshooting, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L40 | Diagnosing Chaos Agent install/health issues, checking VM agent status, and troubleshooting common Chaos Studio experiment failures and known issues. |
| Limits & Quotas | L41-L49 | Chaos Studio limits, throttling, regional/HA behavior, agent OS/fault compatibility, and supported versions/compatibility matrix |
| Security | L50-L64 | Securing Chaos Studio: identity/RBAC, workspace roles, CMK encryption, network/VNet setup, AKS auth and IP allowlists, Relay Bridge/agent security, and mapping faults to required Azure roles. |
| Configuration | L65-L75 | Authoring and deploying Chaos Studio experiments and agents with ARM/Bicep, configuring targets/capabilities, parameters, Private Link, and Azure Policy-based auto-onboarding. |
| Integrations & Coding Patterns | L76-L82 | Using REST/CLI to create/run Chaos Studio experiments and wiring their telemetry into Azure Monitor and Application Insights for tracking, correlation, and analysis |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Review known issues and workarounds for Chaos Agent | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-agent-known-issues |
| Troubleshoot Azure Chaos Agent installation and health | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-agent-troubleshooting |
| Verify and interpret Chaos Agent status on VMs | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-agent-verify-status |
| Troubleshoot common Azure Chaos Studio experiment issues | https://learn.microsoft.com/en-us/azure/chaos-studio/troubleshooting |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Check OS and fault compatibility for Chaos Agent | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-agent-os-support |
| Review Chaos Studio limitations and known issues | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-limitations |
| Understand Chaos Studio regional and HA model | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-region-availability |
| Azure Chaos Studio throttling and usage limits | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-service-limits |
| Azure Chaos Studio version and compatibility matrix | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-versions |

### Security
| Topic | URL |
|-------|-----|
| Use Chaos Studio Relay Bridge Host container image securely | https://learn.microsoft.com/en-us/azure/chaos-studio/azure-container-instance-details |
| Understand Chaos Agent networking, identity, and dependencies | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-agent-concepts |
| Configure Entra authentication for Chaos Studio AKS faults | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-aks-authentication |
| Authorize Chaos Studio IP ranges for AKS clusters | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-aks-ip-ranges |
| Assign experiment permissions and roles in Azure Chaos Studio | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-assign-experiment-permissions |
| Configure customer-managed keys for Chaos Studio experiments | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-configure-customer-managed-keys |
| Map Chaos Studio fault targets to required Azure roles | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-fault-providers |
| Configure permissions and security for Azure Chaos Studio | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-permissions-security |
| Secure Chaos Studio with virtual network injection | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-private-networking |
| Control Chaos Studio targets and capabilities securely | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-targets-capabilities |
| Configure Chaos Studio Workspace identities and RBAC permissions | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-workspace-permissions |

### Configuration
| Topic | URL |
|-------|-----|
| Deploy and configure Chaos Agent via ARM templates | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-agent-arm-template |
| Author Chaos Studio experiments with Bicep templates | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-bicep |
| Use Chaos Studio fault and action parameters | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-fault-library |
| Set up Private Link for Chaos Studio agent experiments | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-private-link-agent-service |
| Configure Azure Policy to auto-add Chaos Studio targets | https://learn.microsoft.com/en-us/azure/chaos-studio/sample-policy-targets |
| Define Chaos Studio experiments with ARM templates | https://learn.microsoft.com/en-us/azure/chaos-studio/sample-template-experiment |
| Use ARM templates to configure Chaos Studio targets and capabilities | https://learn.microsoft.com/en-us/azure/chaos-studio/sample-template-targets |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Call Azure Chaos Studio REST APIs with CLI samples | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-samples-rest-api |
| Send Chaos Agent experiment telemetry to App Insights | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-set-up-app-insights |
| Integrate Azure Monitor telemetry with Chaos Studio experiments | https://learn.microsoft.com/en-us/azure/chaos-studio/chaos-studio-set-up-azure-monitor |
| Create Chaos Studio experiments via CLI and portal | https://learn.microsoft.com/en-us/azure/chaos-studio/experiment-examples |