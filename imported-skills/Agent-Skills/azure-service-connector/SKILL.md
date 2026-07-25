---
name: azure-service-connector
description: Expert knowledge for Azure Service Connector development including troubleshooting, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when wiring Azure compute to databases, messaging, storage, AI, or third‑party services via Service Connector, and other Azure Service Connector related development tasks. Not for Azure API Management (use azure-api-management), Azure App Service (use azure-app-service), Azure Functions (use azure-functions), Azure Logic Apps (use azure-logic-apps).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure Service Connector Skill

This skill provides expert guidance for Azure Service Connector. Covers troubleshooting, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L34-L40 | Diagnosing and resolving common Service Connector errors, connection failures (incl. AKS scenarios), error codes, and configuration issues between Azure compute and backing services. |
| Limits & Quotas | L41-L45 | Known limitations of Azure Service Connector, unsupported scenarios, and suggested workarounds or alternatives for common connection and configuration issues. |
| Security | L46-L51 | Managing Service Connector security: required permissions, Microsoft Entra role assignments, and configuring auth methods (managed identity, service principal, key-based). |
| Configuration | L52-L59 | How to define and retrieve Service Connector connection settings (IaC and runtime), configure auth and environment variables, and supply correct CLI parameters for connections |
| Integrations & Coding Patterns | L60-L92 | How to connect Azure compute to databases, messaging, storage, AI, and third‑party services using Service Connector, including setup patterns, auth options, and integration examples. |
| Deployment | L93-L96 | Info on where Service Connector is regionally supported per compute service and how to create connections using infrastructure-as-code tools. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure Service Connector issues | https://learn.microsoft.com/en-us/azure/service-connector/faq |
| Diagnose and fix Azure Service Connector errors | https://learn.microsoft.com/en-us/azure/service-connector/how-to-troubleshoot-front-end-error |
| Use Service Connector with AKS and troubleshoot connections | https://learn.microsoft.com/en-us/azure/service-connector/how-to-use-service-connector-in-aks |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Service Connector known limitations and workarounds | https://learn.microsoft.com/en-us/azure/service-connector/known-limitations |

### Security
| Topic | URL |
|-------|-----|
| Review Microsoft Entra roles assigned by Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/concept-microsoft-entra-roles |
| Configure required permissions for Azure Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/concept-permission |

### Configuration
| Topic | URL |
|-------|-----|
| Define Azure Service Connector IaC connection settings | https://learn.microsoft.com/en-us/azure/service-connector/how-to-build-connections-with-iac-tools |
| Retrieve and use Service Connector connection configurations | https://learn.microsoft.com/en-us/azure/service-connector/how-to-get-configurations |
| Configure authentication options and env vars in Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-manage-authentication |
| Provide correct CLI parameters to Azure Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-provide-correct-parameters |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Foundry Tools with Azure apps via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-ai-services |
| Integrate Azure App Configuration using Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-app-configuration |
| Connect Azure AI Multi-Service Resource via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-cognitive-services |
| Connect Confluent Cloud Kafka with Azure via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-confluent-kafka |
| Connect Azure Cosmos DB for Cassandra with Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-cosmos-cassandra |
| Integrate Azure Cosmos DB for MongoDB via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-cosmos-db |
| Connect Azure Cosmos DB for Gremlin with Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-cosmos-gremlin |
| Connect Cosmos DB for NoSQL via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-cosmos-sql |
| Connect Cosmos DB for Table via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-cosmos-table |
| Configure Service Connector integration with Azure Event Hubs | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-event-hubs |
| Connect Fabric SQL databases via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-fabric-sql |
| Integrate Azure Key Vault with Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-key-vault |
| Connect MongoDB Atlas clusters via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-mongodb-atlas |
| Integrate Azure Database for MySQL using Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-mysql |
| Integrate Neon Serverless Postgres with Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-neon-postgres |
| Integrate Azure OpenAI in Foundry Models via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-openai |
| Connect Azure Database for PostgreSQL via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-postgres |
| Integrate Azure Cache for Redis using Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-redis-cache |
| Connect Azure Service Bus using Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-service-bus |
| Integrate Azure SignalR Service using Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-signalr |
| Connect Azure SQL Database via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-sql-database |
| Connect to Azure Blob Storage via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-storage-blob |
| Connect Azure Files to compute with Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-storage-file |
| Integrate Azure Queue Storage via Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-storage-queue |
| Integrate Azure Table Storage with Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-storage-table |
| Connect Azure Web PubSub using Service Connector | https://learn.microsoft.com/en-us/azure/service-connector/how-to-integrate-web-pubsub |
| Connect JBoss EAP on App Service to MySQL with managed identity | https://learn.microsoft.com/en-us/azure/service-connector/tutorial-java-jboss-connect-managed-identity-mysql-database |
| Store Service Connector settings in Azure App Configuration | https://learn.microsoft.com/en-us/azure/service-connector/tutorial-portal-app-configuration-store |
| Use Service Connector with AKS workload identity for Storage | https://learn.microsoft.com/en-us/azure/service-connector/tutorial-python-aks-storage-workload-identity |

### Deployment
| Topic | URL |
|-------|-----|
| Check Service Connector regional support by compute service | https://learn.microsoft.com/en-us/azure/service-connector/concept-region-support |