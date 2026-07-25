---
name: azure-sovereign-us
description: Expert knowledge for Azure US Government development including decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. Use when designing IL5/FedRAMP Gov envs, SACA-based architectures, ASE/DISA CAP deploys, Gov Marketplace, or Entra auth, and other Azure US Government related development tasks. Not for Azure Security (use azure-security), Azure Defender For Cloud (use azure-defender-for-cloud), Azure Policy (use azure-policy), Azure Monitor (use azure-monitor).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure US Government Skill

This skill provides expert guidance for Azure US Government. Covers decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Decision Making | L34-L46 | Guidance on choosing Azure Government vs global, FedRAMP/DoD scope and ATO, CSP reseller options, marketplace and DoD regions, and sector-specific compliance (NERC CIP, public safety, worldwide public sector). |
| Architecture & Design Patterns | L47-L51 | Guidance on applying Secure Azure Computing Architecture (SACA) patterns to design compliant, secure, and resilient solutions in Azure Sovereign Cloud environments. |
| Security | L52-L64 | Designing secure, compliant Azure Government environments: isolation/IL5, FedRAMP Rev5 & DoD scope, TIC, identity/Entra auth, resource naming, and workload security controls. |
| Configuration | L65-L73 | Guidance for configuring and operating Azure Government: app deployment, VM extensions, EA billing, marketplace images, and Azure Monitor logs in sovereign US regions. |
| Integrations & Coding Patterns | L74-L80 | Coding patterns and connection guidance for Azure Government: building Foundry Tools apps, connecting SSMS to Gov SQL, and using Azure Storage APIs in sovereign clouds. |
| Deployment | L81-L87 | Guides for deploying apps and solutions to Azure Government: CI/CD with Azure Pipelines, ASE baseline with DISA CAP, App Service deployment, and publishing to Gov Marketplace. |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose between Azure Government and global Azure | https://learn.microsoft.com/en-us/azure/azure-government/compare-azure-government-global-azure |
| Accelerate FedRAMP ATO on Azure with tooling | https://learn.microsoft.com/en-us/azure/azure-government/compliance/documentation-accelerate-compliance |
| Become an Azure Government CSP reseller | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-csp-application |
| Find authorized Azure Government CSP resellers | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-csp-list |
| Use Azure Government Marketplace solutions | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-manage-marketplace |
| Use Azure Government DoD regions for workloads | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-overview-dod |
| Run public safety and justice workloads on Azure | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-overview-jps |
| Apply NERC CIP standards to Azure cloud use | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-overview-nerc |
| Adopt Azure for worldwide public sector securely | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-overview-wwps |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Apply Secure Azure Computing Architecture (SACA) | https://learn.microsoft.com/en-us/azure/azure-government/compliance/secure-azure-computing-architecture |

### Security
| Topic | URL |
|-------|-----|
| Design secure isolation for Azure Government and multitenant | https://learn.microsoft.com/en-us/azure/azure-government/azure-secure-isolation-guidance |
| Understand FedRAMP and DoD compliance scope for Azure clouds | https://learn.microsoft.com/en-us/azure/azure-government/compliance/azure-services-in-fedramp-auditscope |
| Meet Trusted Internet Connections using Azure | https://learn.microsoft.com/en-us/azure/azure-government/compliance/compliance-tic |
| Configure Azure securely for FedRAMP Rev5 | https://learn.microsoft.com/en-us/azure/azure-government/compliance/recommended-secure-configuration |
| Integrate Microsoft Entra auth on Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-aad-auth-qs |
| Name Azure resources without exposing sensitive data | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-concept-naming-resources |
| Configure Azure Government for DoD IL5 isolation | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-impact-level-5 |
| Plan identity architecture for Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-plan-identity |
| Implement security controls for Azure Government workloads | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-plan-security |

### Configuration
| Topic | URL |
|-------|-----|
| Develop and deploy applications on Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-developer-guide |
| List and use VM extensions in Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-extension |
| Access and manage EA billing in Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-how-to-access-enterprise-agreement-billing-account |
| Use Azure Government Marketplace image gallery | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-image-gallery |
| Use Azure Monitor logs in Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-manage-oms |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Develop Foundry Tools apps on Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-cognitiveservices |
| Connect SSMS to Azure Government SQL resources | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-connect-ssms |
| Use Azure Storage APIs in Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-get-started-connect-to-storage |

### Deployment
| Topic | URL |
|-------|-----|
| Set up Azure Pipelines CI/CD to Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/connect-with-azure-pipelines |
| Baseline ASE deployment with DISA CAP in Azure Gov | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-ase-disa-cap |
| Deploy Azure App Service apps to Azure Government | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-howto-deploy-webandmobile |
| Publish solutions to Azure Government Marketplace | https://learn.microsoft.com/en-us/azure/azure-government/documentation-government-manage-marketplace-partners |