---
name: azure-microsoft-discovery
description: Expert knowledge for Azure Microsoft Discovery development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when building Discovery workspaces, shared sessions, supercomputer jobs, ACR tool images, or Log Analytics queries, and other Azure Microsoft Discovery related development tasks. Not for Azure Resource Graph (use azure-resource-graph), Azure Portal (use azure-portal), Azure Monitor (use azure-monitor), Azure Policy (use azure-policy).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Microsoft Discovery Skill

This skill provides expert guidance for Azure Microsoft Discovery. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L41 | Diagnosing and fixing Discovery Engine task execution failures, including common error patterns, configuration issues, and steps to restore successful task runs. |
| Best Practices | L42-L49 | Best practices for structuring projects and shared sessions, applying responsible AI, calibrating trust and safety patterns, and planning tool capabilities and compute for Discovery. |
| Decision Making | L50-L57 | Guidance on selecting ACR setup, agent types, pricing/billing, and suitable AI models to design and configure Microsoft Discovery agents effectively. |
| Architecture & Design Patterns | L58-L62 | Designing and implementing advanced shared session patterns in Discovery Engine, including multi-user session management, data sharing, and scalable architecture best practices. |
| Limits & Quotas | L63-L68 | Planning capacity and Azure quotas for Microsoft Discovery deployments, plus required naming conventions and rules for Discovery resources. |
| Security | L69-L82 | Security, access control, and compliance: code of conduct, encryption at rest/CMK, managed identities, RBAC roles, network/private access, and audit logging for Discovery resources. |
| Configuration | L83-L103 | Configuring Discovery workspaces, supercomputers, storage, tools, data handling, and querying operational/indexing logs via Log Analytics, Kusto, and Azure activity logs |
| Integrations & Coding Patterns | L104-L111 | Patterns and APIs for integrating tools/models into Discovery workflows, containerizing tools with Docker, writing action scripts, and submitting/monitoring Supercomputer jobs via REST |
| Deployment | L112-L118 | Deploying Microsoft Discovery: secure stack setup, provisioning supercomputer infra via REST, registering tools, and publishing tool images to Azure Container Registry. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Discovery Engine task execution issues | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-debug-task-execution |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply projects and shared session best practices in Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-projects-investigations |
| Apply responsible AI practices in Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-responsible-ai |
| Calibrate trust and basic shared session patterns in Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-trust-basic-investigation-patterns |
| Plan tool functionality and compute for Discovery tools | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-plan-tool-requirements |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose and configure Azure Container Registry for Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-azure-container-registry |
| Choose the right Microsoft Discovery agent type | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-discovery-agent-types |
| Understand Microsoft Discovery billing and charges | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-discovery-billing |
| Choose appropriate models for Microsoft Discovery agents | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-select-models-for-agents |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Apply advanced shared session patterns with Discovery Engine | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-advanced-investigation-patterns |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Plan Azure quotas and capacity for Microsoft Discovery deployments | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-quota-reservation |
| Apply Microsoft Discovery resource naming rules | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-resource-naming |

### Security
| Topic | URL |
|-------|-----|
| Understand Microsoft Discovery code of conduct and acceptable use | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-code-of-conduct |
| Manage data encryption at rest in Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-data-encryption-at-rest |
| Configure managed identities for Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-managed-identities |
| Configure network security for Microsoft Discovery workspaces | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-network-security |
| Configure RBAC role assignments for Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-role-assignments |
| Assign Microsoft Discovery persona RBAC roles via PowerShell | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-assign-persona-roles |
| Configure user-assigned managed identities for Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-configure-managed-identity |
| Configure network security and private access for Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-configure-network-security |
| Enable and export audit logs for Discovery resources | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-enable-audit-logging |
| Configure customer-managed keys for Discovery resources | https://learn.microsoft.com/en-us/azure/microsoft-discovery/howto-data-encryption-at-rest |

### Configuration
| Topic | URL |
|-------|-----|
| Manage files and storage assets in Microsoft Discovery shared sessions | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-files-storage-assets |
| Register Microsoft Discovery resource provider in Azure | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-resource-provider-registration |
| Configure Azure Blob Storage for Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-storage-account |
| Configure storage containers and assets for Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-storage-containers-assets |
| Access Log Analytics workspaces for Discovery resources | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-access-resource-logs |
| Author tool definition YAML for Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-create-tool-definition |
| Configure data handling for tools and agents in Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-data-handling-with-tools-agents |
| Configure Bookshelf and index knowledgebases in Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-index-bookshelf-knowledgebase |
| Configure storage containers and assets in Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-manage-storage-containers |
| Create and manage Discovery Supercomputers and node pools | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-manage-supercomputers |
| Create and manage Microsoft Discovery workspaces | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-manage-workspaces |
| Query bookshelf indexing logs in Discovery supercomputers | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-query-bookshelf-indexing-logs |
| Query bookshelf knowledgebase query logs in Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-query-bookshelf-logs |
| Query CogLoop orchestration logs for Discovery investigations | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-query-cognitive-loop-logs |
| Query supercomputer platform and tool logs in Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-query-supercomputer-logs |
| Query Discovery workspace logs with Kusto and correlation IDs | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-query-workspace-logs |
| View Azure activity logs for Discovery control plane | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-view-activity-logs |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate tools and models into Microsoft Discovery workflows | https://learn.microsoft.com/en-us/azure/microsoft-discovery/concept-tools-model-integration |
| Create Dockerfiles to containerize Discovery tools | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-create-tool-docker-file |
| Submit and monitor Discovery Supercomputer jobs with REST APIs | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-run-jobs-supercomputer-rest-api |
| Implement action scripts for Discovery action-based tools | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-write-tool-action-scripts |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy a fully network-hardened Microsoft Discovery stack | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-deploy-network-hardened-stack |
| Deploy and register tools to Microsoft Discovery | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-deploy-tool-to-discovery |
| Provision Discovery Supercomputer infrastructure via REST API | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-manage-supercomputers-rest-api |
| Publish Discovery tool images to Azure Container Registry | https://learn.microsoft.com/en-us/azure/microsoft-discovery/how-to-publish-tool-to-acr |