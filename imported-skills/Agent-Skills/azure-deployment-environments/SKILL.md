---
name: azure-deployment-environments
description: Expert knowledge for Azure Deployment Environments development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring ADE catalogs, RBAC/managed identities, Git/ARM catalogs, custom images, or CI/CD environment automation, and other Azure Deployment Environments related development tasks. Not for Azure DevTest Labs (use azure-devtest-labs), Azure Dev Box (use azure-dev-box), Azure Integration Environments (use azure-integration-environments), Azure Managed Applications (use azure-managed-applications).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-14"
  generator: "docs2skills/1.0.0"
---
# Azure Deployment Environments Skill

This skill provides expert guidance for Azure Deployment Environments. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L41 | Diagnosing and resolving custom image deployment failures in Azure Deployment Environments, including common error patterns, logs to inspect, and remediation steps. |
| Best Practices | L42-L46 | Guidance on organizing and structuring Azure Deployment Environments catalogs, including repo layout, template grouping, naming, and governance for scalable, maintainable catalogs. |
| Decision Making | L47-L51 | Guidance on planning for Azure Deployment Environments entering maintenance mode, including impact, timelines, alternatives, and migration/transition considerations. |
| Architecture & Design Patterns | L52-L56 | Guidance on designing resilient, scalable Azure Deployment Environments architectures, including fault tolerance, high availability, redundancy, and best practices for robust environment design. |
| Limits & Quotas | L57-L61 | Requesting and managing quota increases for Azure Deployment Environments resource limits, including how to handle capacity constraints and raise support requests. |
| Security | L62-L69 | RBAC and identity setup for Deployment Environments: planning and assigning roles, configuring managed identities, and authenticating to the REST APIs. |
| Configuration | L70-L81 | Defining ADE environments and types, configuring Git catalogs and ARM provisioning, using the devcenter CLI, auto-deletion, and environment variables for custom images. |
| Integrations & Coding Patterns | L82-L88 | Using Azure Developer CLI and ADE CLI to create environments, build custom container images, and manage custom image workflows for Azure Deployment Environments |
| Deployment | L89-L93 | Using Azure Deployment Environments with CI/CD tools (Azure Pipelines, GitHub Actions) to automate environment creation, updates, and deployments from templates. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Diagnose custom image deployment failures in Azure Deployment Environments | https://learn.microsoft.com/en-us/azure/deployment-environments/troubleshoot-custom-image-logs-errors |

### Best Practices
| Topic | URL |
|-------|-----|
| Structure Azure Deployment Environments catalogs efficiently | https://learn.microsoft.com/en-us/azure/deployment-environments/best-practice-catalog-structure |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan for Azure Deployment Environments maintenance mode | https://learn.microsoft.com/en-us/azure/deployment-environments/maintenance-mode |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design resilient Azure Deployment Environments architectures | https://learn.microsoft.com/en-us/azure/deployment-environments/concept-reliability-deployment-environments |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Request quota increases for ADE resource limits | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-request-quota-increase |

### Security
| Topic | URL |
|-------|-----|
| Plan Azure RBAC roles for Deployment Environments | https://learn.microsoft.com/en-us/azure/deployment-environments/concept-deployment-environments-role-based-access-control |
| Authenticate to Azure Deployment Environments REST APIs | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-authenticate |
| Configure managed identity for Azure Deployment Environments dev center | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-configure-managed-identity |
| Assign RBAC roles for Azure Deployment Environments access | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-manage-deployment-environments-access |

### Configuration
| Topic | URL |
|-------|-----|
| Define Azure Deployment Environments with environment.yaml schema | https://learn.microsoft.com/en-us/azure/deployment-environments/concept-environment-yaml |
| Configure Git-based catalogs for Azure Deployment Environments | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-configure-catalog |
| Configure dev center environment types in Azure Deployment Environments | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-configure-devcenter-environment-types |
| Configure project-level environment types in Azure Deployment Environments | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-configure-project-environment-types |
| Install and use the devcenter Azure CLI extension | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-install-devcenter-cli-extension |
| Configure automatic deletion for ADE environments | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-schedule-environment-deletion |
| Provision dev center and project via ARM template | https://learn.microsoft.com/en-us/azure/deployment-environments/quickstart-create-dev-center-project-azure-resource-manager |
| Reference ADE CLI environment variables for custom images | https://learn.microsoft.com/en-us/azure/deployment-environments/reference-deployment-environment-variables |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Create ADE environments using Azure Developer CLI | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-configure-azure-developer-cli-deployment-environments |
| Use custom container images with Azure Deployment Environments | https://learn.microsoft.com/en-us/azure/deployment-environments/how-to-configure-extensibility-model-custom-image |
| Use ADE CLI commands for custom image workflows | https://learn.microsoft.com/en-us/azure/deployment-environments/reference-deployment-environment-cli |

### Deployment
| Topic | URL |
|-------|-----|
| Integrate ADE with Azure Pipelines for CI/CD | https://learn.microsoft.com/en-us/azure/deployment-environments/tutorial-deploy-environments-in-cicd-azure-devops |
| Deploy Azure environments via GitHub CI/CD pipelines | https://learn.microsoft.com/en-us/azure/deployment-environments/tutorial-deploy-environments-in-cicd-github |