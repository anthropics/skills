---
name: azure-fluid-relay
description: Expert knowledge for Azure Fluid Relay development including troubleshooting, best practices, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using AzureClient, audience APIs, JWT auth tokens, container recovery, or Static Web Apps hosting, and other Azure Fluid Relay related development tasks. Not for Azure Web PubSub (use azure-web-pubsub), Azure SignalR Service (use azure-signalr-service), Azure Relay (use azure-relay), Azure Service Bus (use azure-service-bus).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure Fluid Relay Skill

This skill provides expert guidance for Azure Fluid Relay. Covers troubleshooting, best practices, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L39 | Recovering from corrupted Azure Fluid Relay container data, including detection, mitigation steps, and restoring or reconstructing data to resume collaboration. |
| Best Practices | L40-L44 | Guidance on integrating Azure Fluid Relay with test automation frameworks, setting up automated tests, and validating Fluid collaboration scenarios in CI/CD workflows. |
| Limits & Quotas | L45-L49 | Details on Azure Fluid Relay capacity limits, throttling behavior, quotas per tenant/container, and guidance to avoid or handle rate limiting and overuse scenarios. |
| Security | L50-L60 | Securing Fluid Relay apps: auth/JWT design, token providers, key rotation, CMK and data encryption, and validating container creator identity. |
| Configuration | L61-L66 | Configuring compatible Fluid Framework client/server versions with Azure Fluid Relay and deleting Fluid Relay containers via Azure CLI. |
| Integrations & Coding Patterns | L67-L73 | Building Fluid apps with AzureClient: connecting to Azure Fluid Relay, configuring local dev/test mode, and using audience APIs with React for presence and user management |
| Deployment | L74-L77 | Guidance for deploying Fluid Framework apps with Azure Fluid Relay to Azure Static Web Apps, including setup, configuration, and integration steps for hosting collaborative apps. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Recover corrupted Azure Fluid Relay container data | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/container-recovery |

### Best Practices
| Topic | URL |
|-------|-----|
| Use test automation frameworks with Azure Fluid Relay | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/test-automation |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Review Azure Fluid Relay service limits and throttling | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/reference/service-limits |

### Security
| Topic | URL |
|-------|-----|
| Implement authentication and authorization for Fluid Relay apps | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/concepts/authentication-authorization |
| Use customer-managed keys with Azure Fluid Relay | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/concepts/customer-managed-keys |
| Configure data encryption for Azure Fluid Relay | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/concepts/data-encryption |
| Implement a secure TokenProvider with Azure Functions for Fluid Relay | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/azure-function-token-provider |
| Understand and configure Azure Fluid Relay JWT token contract | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/fluid-json-web-token |
| Rotate Azure Fluid Relay tenant access keys securely | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/rotate-fluid-relay-access-keys |
| Validate container creator identity in Azure Fluid Relay | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/validate-document-creator |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Fluid Framework versions compatible with Azure Fluid Relay | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/concepts/version-compatibility |
| Delete Azure Fluid Relay containers using Azure CLI | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/container-deletion |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect applications to Azure Fluid Relay using AzureClient | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/connect-fluid-azure-service |
| Configure AzureClient local mode for Fluid app testing | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/local-mode-with-azure-client |
| Use Fluid Framework audience features with React and AzureClient | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/use-audience-in-fluid |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Fluid applications to Azure Static Web Apps | https://learn.microsoft.com/en-us/azure/azure-fluid-relay/how-tos/deploy-fluid-static-web-apps |