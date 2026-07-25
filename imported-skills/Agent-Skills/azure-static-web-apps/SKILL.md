---
name: azure-static-web-apps
description: Expert knowledge for Azure Static Web Apps development including troubleshooting, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when wiring SWA APIs to Azure DBs, configuring custom domains/DNS, auth/roles, CI/CD, or plan limits, and other Azure Static Web Apps related development tasks. Not for Azure App Service (use azure-app-service), Azure Functions (use azure-functions), Azure Container Apps (use azure-container-apps), Azure Web PubSub (use azure-web-pubsub).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-07"
  generator: "docs2skills/1.0.0"
---
# Azure Static Web Apps Skill

This skill provides expert guidance for Azure Static Web Apps. Covers troubleshooting, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L39 | Diagnosing and fixing common Static Web Apps deployment and runtime issues, including build failures, configuration problems, and troubleshooting tools/logs. |
| Decision Making | L40-L47 | Guidance on key architecture choices: Functions hosting model, using Front Door/CDN edge, Next.js deployment options, and comparing Free vs Standard Static Web Apps plans. |
| Limits & Quotas | L48-L54 | Details on Static Web Apps plan quotas, resource and behavior limits, supported languages/frameworks, and available runtime versions across tiers. |
| Security | L55-L66 | Configuring auth, roles, secrets, and access: Entra ID/Graph roles, auth providers, user info, deployment tokens, Key Vault/managed identity, password protection, and private endpoints. |
| Configuration | L67-L93 | Configuring domains, DNS, backends (Functions, App Service, Container Apps, APIM), build/runtime settings, local emulation (SWA CLI), monitoring, and database/network for Static Web Apps. |
| Integrations & Coding Patterns | L94-L102 | How to connect Static Web Apps APIs to Azure databases (Cosmos DB, SQL, MySQL, PostgreSQL), including Mongoose usage, connection strings, and typical integration patterns. |
| Deployment | L103-L119 | Deploying Static Web Apps via GitHub/GitLab/Bitbucket/CLI/ARM/Bicep, configuring CI/CD, preview environments, traffic splitting, and optional Azure Front Door CDN setup |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot common deployment and runtime issues in Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/troubleshooting |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose managed vs bring-your-own Azure Functions for Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/apis-functions |
| Use enterprise-grade edge for Azure Static Web Apps with Azure Front Door and CDN | https://learn.microsoft.com/en-us/azure/static-web-apps/enterprise-edge |
| Select Next.js deployment model on Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/nextjs |
| Choose Azure Static Web Apps Free vs Standard plans | https://learn.microsoft.com/en-us/azure/static-web-apps/plans |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Azure Static Web Apps limits and behavioral specifics | https://learn.microsoft.com/en-us/azure/static-web-apps/faq |
| Supported languages and runtime versions for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/languages-runtimes |
| Quotas and limits for Azure Static Web Apps plans | https://learn.microsoft.com/en-us/azure/static-web-apps/quotas |

### Security
| Topic | URL |
|-------|-----|
| Assign Static Web Apps roles using Microsoft Graph and Entra ID | https://learn.microsoft.com/en-us/azure/static-web-apps/assign-roles-microsoft-graph |
| Configure authentication and authorization for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/authentication-authorization |
| Configure custom authentication providers for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/authentication-custom |
| Manage and reset deployment tokens for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/deployment-token-management |
| Use Key Vault and managed identity for Static Web Apps auth secrets | https://learn.microsoft.com/en-us/azure/static-web-apps/key-vault-secrets |
| Enable password protection for Azure Static Web Apps environments | https://learn.microsoft.com/en-us/azure/static-web-apps/password-protection |
| Configure private endpoint access for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/private-endpoint |
| Access authenticated user information in Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/user-information |

### Configuration
| Topic | URL |
|-------|-----|
| Configure apex domains with Azure DNS for Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/apex-domain-azure-dns |
| Configure apex/root domains with external registrars for Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/apex-domain-external |
| Configure Azure API Management integration with Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/apis-api-management |
| Link Azure App Service backends to Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/apis-app-service |
| Integrate Azure Container Apps as APIs for Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/apis-container-apps |
| Set application settings for Static Web Apps backend APIs | https://learn.microsoft.com/en-us/azure/static-web-apps/application-settings |
| Configure staticwebapp.config.json for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/configuration |
| Configure custom domains for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/custom-domain |
| Set up Azure DNS custom domains for Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/custom-domain-azure-dns |
| Manage default domain routing in Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/custom-domain-default |
| Use external DNS providers for Static Web Apps custom domains | https://learn.microsoft.com/en-us/azure/static-web-apps/custom-domain-external |
| Configure database connections and firewall for Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/database-configuration |
| Configure build settings for front-end frameworks in Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/front-end-frameworks |
| Link existing Azure Functions apps to Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/functions-bring-your-own |
| Configure local development environment for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/local-development |
| Use metrics for managed Functions in Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/metrics |
| Enable Application Insights monitoring for Azure Static Web Apps APIs | https://learn.microsoft.com/en-us/azure/static-web-apps/monitor |
| Inject runtime snippets into Static Web Apps pages | https://learn.microsoft.com/en-us/azure/static-web-apps/snippets |
| Azure Static Web Apps CLI command reference | https://learn.microsoft.com/en-us/azure/static-web-apps/static-web-apps-cli |
| Run and proxy API servers with Azure Static Web Apps CLI | https://learn.microsoft.com/en-us/azure/static-web-apps/static-web-apps-cli-api-server |
| Configure Azure Static Web Apps CLI with swa-cli.config.json | https://learn.microsoft.com/en-us/azure/static-web-apps/static-web-apps-cli-configuration |
| Emulate Azure Static Web Apps locally with SWA CLI | https://learn.microsoft.com/en-us/azure/static-web-apps/static-web-apps-cli-emulator |
| Use Azure Static Web Apps CLI for local emulation and workflows | https://learn.microsoft.com/en-us/azure/static-web-apps/static-web-apps-cli-overview |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Mongoose with Azure Cosmos DB in Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/add-mongoose |
| Connect Azure Static Web Apps to Azure Cosmos DB | https://learn.microsoft.com/en-us/azure/static-web-apps/database-azure-cosmos-db |
| Connect Azure Static Web Apps to Azure SQL Database | https://learn.microsoft.com/en-us/azure/static-web-apps/database-azure-sql |
| Connect Azure Static Web Apps to Azure Database for MySQL | https://learn.microsoft.com/en-us/azure/static-web-apps/database-mysql |
| Connect Azure Static Web Apps to Azure Database for PostgreSQL | https://learn.microsoft.com/en-us/azure/static-web-apps/database-postgresql |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Bitbucket-hosted apps to Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/bitbucket |
| Create branch-based preview environments with stable URLs | https://learn.microsoft.com/en-us/azure/static-web-apps/branch-environments |
| Configure CI/CD build YAML for Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/build-configuration |
| Deploy Azure Static Web Apps with external CI/CD providers | https://learn.microsoft.com/en-us/azure/static-web-apps/external-providers |
| Manually configure Azure Front Door as CDN for Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/front-door-manual |
| Deploy GitLab-hosted apps to Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/gitlab |
| Create named preview environments in Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/named-environments |
| Use preview environments and temporary URLs in Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/preview-environments |
| Deploy Azure Static Web Apps using ARM templates | https://learn.microsoft.com/en-us/azure/static-web-apps/publish-azure-resource-manager |
| Deploy Azure Static Web Apps with Bicep templates | https://learn.microsoft.com/en-us/azure/static-web-apps/publish-bicep |
| Review pull requests using pre-production environments in Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/review-publish-pull-requests |
| Deploy static web apps using Azure Static Web Apps CLI | https://learn.microsoft.com/en-us/azure/static-web-apps/static-web-apps-cli-deploy |
| Install Azure Static Web Apps CLI with supported platforms | https://learn.microsoft.com/en-us/azure/static-web-apps/static-web-apps-cli-install |
| Configure traffic splitting between environments in Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/static-web-apps/traffic-splitting |