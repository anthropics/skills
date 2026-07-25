---
name: azure-relay
description: Expert knowledge for Azure Relay development including troubleshooting, security, configuration, and integrations & coding patterns. Use when configuring Hybrid Connections, WCF relays, Entra ID/SAS auth, Private Link, or .NET/Node.js Relay clients, and other Azure Relay related development tasks. Not for Azure Service Bus (use azure-service-bus), Azure Event Hubs (use azure-event-hubs), Azure Web PubSub (use azure-web-pubsub), Azure Application Gateway (use azure-application-gateway).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-05-17"
  generator: "docs2skills/1.0.0"
---
# Azure Relay Skill

This skill provides expert guidance for Azure Relay. Covers troubleshooting, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L32-L36 | Diagnosing and fixing common Azure Relay exceptions, including connection, authentication, quota, and configuration errors, with guidance on causes and resolutions. |
| Security | L37-L46 | Authentication and network security for Azure Relay: Entra ID and SAS auth, managed identities, IP firewall, virtual network rules, and Private Link Service configuration. |
| Configuration | L47-L51 | Network and firewall requirements for Azure Relay, including which ports/protocols to open for Hybrid Connections and WCF relays and how to configure them. |
| Integrations & Coding Patterns | L52-L57 | Using Azure Relay Hybrid Connections from .NET and Node.js (WebSockets), plus low-level protocol details for implementing custom clients and integrations |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure Relay exceptions | https://learn.microsoft.com/en-us/azure/azure-relay/relay-exceptions |

### Security
| Topic | URL |
|-------|-----|
| Authenticate applications to Azure Relay with Entra ID | https://learn.microsoft.com/en-us/azure/azure-relay/authenticate-application |
| Use managed identities to access Azure Relay | https://learn.microsoft.com/en-us/azure/azure-relay/authenticate-managed-identity |
| Configure IP firewall rules for Azure Relay | https://learn.microsoft.com/en-us/azure/azure-relay/ip-firewall-virtual-networks |
| Configure network security for Azure Relay | https://learn.microsoft.com/en-us/azure/azure-relay/network-security |
| Secure Azure Relay with Private Link Service | https://learn.microsoft.com/en-us/azure/azure-relay/private-link-service |
| Configure SAS and Entra ID auth for Azure Relay | https://learn.microsoft.com/en-us/azure/azure-relay/relay-authentication-and-authorization |

### Configuration
| Topic | URL |
|-------|-----|
| Configure required port settings for Azure Relay | https://learn.microsoft.com/en-us/azure/azure-relay/relay-port-settings |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use Azure Relay Hybrid Connections .NET APIs | https://learn.microsoft.com/en-us/azure/azure-relay/relay-hybrid-connections-dotnet-api-overview |
| Use Azure Relay Node.js WebSocket APIs | https://learn.microsoft.com/en-us/azure/azure-relay/relay-hybrid-connections-node-ws-api-overview |
| Implement Azure Relay Hybrid Connections protocol | https://learn.microsoft.com/en-us/azure/azure-relay/relay-hybrid-connections-protocol |