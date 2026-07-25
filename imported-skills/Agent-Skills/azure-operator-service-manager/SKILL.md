---
name: azure-operator-service-manager
description: Expert knowledge for Azure Operator Service Manager development including troubleshooting, best practices, security, configuration, and integrations & coding patterns. Use when onboarding CNFs/VNFs, designing config groups, managing ACR artifacts, using ARM/CLI, or securing with Private Link, and other Azure Operator Service Manager related development tasks. Not for Azure Operator Nexus (use azure-operator-nexus), Azure Operator Insights (use azure-operator-insights), Azure Network Function Manager (use azure-network-function-manager), Azure Networking (use azure-networking).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Operator Service Manager Skill

This skill provides expert guidance for Azure Operator Service Manager. Covers troubleshooting, best practices, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L38 | Diagnosing and fixing AOSM onboarding issues with the Azure CLI extension and troubleshooting Helm chart installation failures in AOSM CNF deployments. |
| Best Practices | L39-L47 | Best practices for AOSM onboarding, config group design, Helm charts, artifact cleanup, and controlling CNF upgrade failure behavior. |
| Security | L48-L55 | Securing AOSM with Private Link, custom RBAC/roles, and User Assigned Managed Identities for controlled, least-privilege access and secure SNS/service operator deployments. |
| Configuration | L56-L65 | Configuring AOSM deployment behavior: cluster registry for edge resiliency, pausing/resuming site services, Helm cleanup/tests, NFO extension settings, and artifact store geo-replication. |
| Integrations & Coding Patterns | L66-L75 | Using CLI/ARM/Helm with AOSM to onboard CNFs/VNFs, manage images and artifacts (ACR/storage-backed stores), and add ARM resources to network service designs |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure CLI AOSM extension onboarding issues | https://learn.microsoft.com/en-us/azure/operator-service-manager/troubleshoot-cli-common-issues |
| Diagnose Helm install failures in AOSM CNF deployments | https://learn.microsoft.com/en-us/azure/operator-service-manager/troubleshoot-helm-install-failures |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply onboarding and deployment best practices for AOSM | https://learn.microsoft.com/en-us/azure/operator-service-manager/best-practices-onboard-deploy |
| Design configuration groups effectively in Azure Operator Service Manager | https://learn.microsoft.com/en-us/azure/operator-service-manager/configuration-guide |
| Apply Helm chart best practices for Azure Operator Service Manager | https://learn.microsoft.com/en-us/azure/operator-service-manager/helm-requirements |
| Manage AOSM publisher artifact cleanup efficiently | https://learn.microsoft.com/en-us/azure/operator-service-manager/resource-cleanup-management |
| Control CNF upgrade failure behavior in AOSM | https://learn.microsoft.com/en-us/azure/operator-service-manager/safe-upgrades-nf-level-rollback |

### Security
| Topic | URL |
|-------|-----|
| Configure AOSM Private Link for secure backhaul | https://learn.microsoft.com/en-us/azure/operator-service-manager/get-started-with-private-link |
| Assign custom AOSM roles for secure SNS deployment | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-assign-custom-role |
| Create custom RBAC roles for AOSM service operators | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-create-custom-role |
| Configure and use User Assigned Managed Identity with AOSM | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-create-user-assigned-managed-identity |

### Configuration
| Topic | URL |
|-------|-----|
| Set up AOSM cluster registry for edge resiliency | https://learn.microsoft.com/en-us/azure/operator-service-manager/get-started-with-cluster-registry |
| Interrupt and resume AOSM site network service deployments | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-cancel-service-deployments |
| Override Helm failure cleanup behavior in AOSM deployments | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-use-helm-option-parameters |
| Use CLI commands to configure NFO cluster extension | https://learn.microsoft.com/en-us/azure/operator-service-manager/manage-network-function-operator |
| Configure geo-replication for AOSM artifact stores | https://learn.microsoft.com/en-us/azure/operator-service-manager/publisher-artifact-store-resiliency |
| Configure Helm test integration for AOSM upgrades | https://learn.microsoft.com/en-us/azure/operator-service-manager/safe-upgrades-helm-test |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use AOSM CLI to discover and upload CNF images | https://learn.microsoft.com/en-us/azure/operator-service-manager/concepts-cli-containerized-network-function-image-upload |
| Map Helm and ARM parameters to AOSM configuration | https://learn.microsoft.com/en-us/azure/operator-service-manager/concepts-expose-parameters-configuration-group-schema |
| Push and pull artifacts with ACR-backed AOSM artifact stores | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-manage-artifacts-nexus |
| Push and pull artifacts with AOSM storage-backed stores | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-manage-artifacts-virtualized-network-function-cloud |
| Add ARM resources to AOSM Network Service Designs via CLI | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-onboard-azure-resource-manager-resources-cli |
| Onboard CNFs to AOSM using the CLI extension | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-onboard-containerized-network-function-cli |
| Onboard VNFs to AOSM for deployment on Nexus | https://learn.microsoft.com/en-us/azure/operator-service-manager/how-to-onboard-virtualized-network-function-cli |