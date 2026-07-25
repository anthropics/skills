---
name: azure-signalr-service
description: Expert knowledge for Azure SignalR Service development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring SignalR modes, upstreams, private endpoints, autoscale, multi-region topologies, or Event Grid integration, and other Azure SignalR Service related development tasks. Not for Azure Web PubSub (use azure-web-pubsub), Azure Service Bus (use azure-service-bus), Azure Event Hubs (use azure-event-hubs).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-07"
  generator: "docs2skills/1.0.0"
---
# Azure SignalR Service Skill

This skill provides expert guidance for Azure SignalR Service. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L45 | Diagnosing and fixing SignalR issues: connectivity and message delivery problems, live trace and Azure Monitor logs, common error patterns, and best practices for reliable operation. |
| Best Practices | L46-L51 | Guidance on safely shutting down SignalR app servers and managing client lifecycle events, including detecting, handling, and recovering from client disconnects and reconnects. |
| Decision Making | L52-L56 | Guidance on choosing the right SignalR Service mode (Default/Serverless/Classic) and configuring availability zones/zone redundancy for high availability and resilience. |
| Architecture & Design Patterns | L57-L63 | Patterns for scaling and sharding SignalR, designing resilient multi-region topologies, and architecting high-availability, high-throughput ASP.NET Core SignalR apps with Azure SignalR. |
| Limits & Quotas | L64-L70 | Message/connection billing rules, capacity planning, throughput limits, and how to scale Azure SignalR instances within quota and performance constraints. |
| Security | L71-L92 | Securing Azure SignalR: auth with Entra ID/managed identities, keys and rotation, network/private endpoints/NSGs, WAF, Key Vault access, RBAC, cross-tenant, and Azure Policy compliance. |
| Configuration | L93-L104 | Configuring SignalR apps: connection strings, upstream endpoints, custom domains, monitoring/metrics, negotiation endpoints, Functions bindings, and using the local emulator. |
| Integrations & Coding Patterns | L105-L120 | Patterns and APIs for integrating SignalR with servers and gateways: SDK usage, client management, REST data-plane versions, and wiring events through Event Grid, API Management, and Application Gateway. |
| Deployment | L121-L131 | Deploying and managing Azure SignalR via CLI, ARM/Bicep templates, autoscale setup, regional moves, and end-to-end web app deployment (incl. GitHub auth) |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Use Azure Monitor resource logs to troubleshoot SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-diagnostic-logs |
| Troubleshoot common Azure SignalR Service issues | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-troubleshoot-guide |
| Use the Azure SignalR live trace tool for diagnostics | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-troubleshoot-live-trace |
| Troubleshoot SignalR connectivity and message delivery | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-troubleshoot-method |
| Troubleshoot and use Azure SignalR Service effectively | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-resource-faq |

### Best Practices
| Topic | URL |
|-------|-----|
| Gracefully shut down Azure SignalR app servers | https://learn.microsoft.com/en-us/azure/azure-signalr/server-graceful-shutdown |
| Handle client disconnections and reconnections in Azure SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-client-disconnections |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose the right Azure SignalR Service mode | https://learn.microsoft.com/en-us/azure/azure-signalr/concept-service-mode |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design resilient multi-region Azure SignalR topologies | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-disaster-recovery |
| Scale ASP.NET Core SignalR apps using Azure SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-scale-aspnet-core |
| Scale Azure SignalR with multiple instances and sharding | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-scale-multi-instances |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand message and connection counting for SignalR billing | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-messages-and-connections |
| Plan Azure SignalR performance and capacity | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-performance |
| Scale Azure SignalR instances and understand scaling constraints | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-scale-signalr |

### Security
| Topic | URL |
|-------|-----|
| Disable access key auth and enforce Entra ID for SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/howto-disable-local-auth |
| Configure network access control for Azure SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/howto-network-access-control |
| Secure Azure SignalR with private endpoints | https://learn.microsoft.com/en-us/azure/azure-signalr/howto-private-endpoints |
| Use Azure SignalR service tags in NSGs | https://learn.microsoft.com/en-us/azure/azure-signalr/howto-service-tags |
| Secure SignalR outbound traffic via shared private endpoints | https://learn.microsoft.com/en-us/azure/azure-signalr/howto-shared-private-endpoints |
| Access Key Vault privately from Azure SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/howto-shared-private-endpoints-key-vault |
| Use managed identities with Azure SignalR Service | https://learn.microsoft.com/en-us/azure/azure-signalr/howto-use-managed-identity |
| Built-in Azure Policy definitions for Azure SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/policy-reference |
| Apply Azure Policy regulatory compliance controls to SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/security-controls-policy |
| Implement custom authentication for Azure SignalR clients | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-authenticate-oauth |
| Authorize Azure SignalR access with Microsoft Entra ID RBAC | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-authorize-azure-active-directory |
| Authorize Azure SignalR with Microsoft Entra applications | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-authorize-application |
| Configure cross-tenant authorization for Azure SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-authorize-cross-tenant |
| Authorize Azure SignalR with managed identities | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-authorize-managed-identity |
| Enforce Azure SignalR compliance with Azure Policy | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-azure-policy |
| Configure Azure SignalR Application Firewall rules | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-configure-application-firewall |
| Rotate Azure SignalR access keys securely | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-key-rotation |
| Authenticate Azure SignalR clients with Azure Functions bindings | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-tutorial-authenticate-azure-functions |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure SignalR Service connection strings in apps | https://learn.microsoft.com/en-us/azure/azure-signalr/concept-connection-string |
| Configure upstream endpoints and protocols in Azure SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/concept-upstream |
| Configure custom domains for Azure SignalR Service | https://learn.microsoft.com/en-us/azure/azure-signalr/howto-custom-domain |
| Configure monitoring for Azure SignalR with Azure Monitor | https://learn.microsoft.com/en-us/azure/azure-signalr/monitor-signalr |
| Reference for Azure SignalR monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/azure-signalr/monitor-signalr-reference |
| Customize client negotiation endpoints in Azure SignalR | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-client-negotiation |
| Develop and configure Azure Functions apps with SignalR bindings | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-serverless-development-config |
| Use Azure SignalR Local Emulator for serverless development | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-emulator |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure SignalR Service events with Event Grid | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-concept-event-grid-integration |
| Integrate Azure SignalR events with Event Grid | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-event-grid-integration |
| Use Azure SignalR Service SDK from your app server | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-use |
| Manage Azure SignalR clients using the Management SDK | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-use-management-sdk |
| Use Azure SignalR with API Management | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-work-with-apim |
| Use Azure SignalR with Application Gateway | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-work-with-app-gateway |
| Use Azure SignalR REST API for server-to-client messaging | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-quickstart-rest-api |
| Use Azure SignalR data-plane REST APIs | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-reference-data-plane-rest-api |
| Integrate with Azure SignalR REST API v1 | https://learn.microsoft.com/en-us/azure/azure-signalr/swagger/signalr-data-plane-rest-v1 |
| Integrate with Azure SignalR REST API v1-preview | https://learn.microsoft.com/en-us/azure/azure-signalr/swagger/signalr-data-plane-rest-v1-preview |
| Integrate with Azure SignalR REST API v20220601 | https://learn.microsoft.com/en-us/azure/azure-signalr/swagger/signalr-data-plane-rest-v20220601 |
| Integrate with Azure SignalR REST API v20241201 | https://learn.microsoft.com/en-us/azure/azure-signalr/swagger/signalr-data-plane-rest-v20241201 |

### Deployment
| Topic | URL |
|-------|-----|
| Create an Azure SignalR Service via Azure CLI script | https://learn.microsoft.com/en-us/azure/azure-signalr/scripts/signalr-cli-create-service |
| Provision SignalR Service with App Service using Azure CLI | https://learn.microsoft.com/en-us/azure/azure-signalr/scripts/signalr-cli-create-with-app-service |
| Deploy SignalR web app with GitHub authentication via CLI | https://learn.microsoft.com/en-us/azure/azure-signalr/scripts/signalr-cli-create-with-app-service-github-oauth |
| Move Azure SignalR resources across regions with ARM templates | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-move-across-regions |
| Configure autoscale for Azure SignalR Premium tier | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-howto-scale-autoscale |
| Deploy Azure SignalR Service using ARM templates | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-quickstart-azure-signalr-service-arm-template |
| Deploy Azure SignalR Service using Bicep templates | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-quickstart-azure-signalr-service-bicep |
| Azure CLI script samples for deploying SignalR Service | https://learn.microsoft.com/en-us/azure/azure-signalr/signalr-reference-cli |