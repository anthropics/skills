---
name: azure-service-bus
description: Expert knowledge for Azure Service Bus development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using queues/topics, sessions/FIFO, JMS/RabbitMQ integration, geo-replication, or Premium high-scale workloads, and other Azure Service Bus related development tasks. Not for Azure Event Hubs (use azure-event-hubs), Azure Relay (use azure-relay), Azure Notification Hubs (use azure-notification-hubs), Azure Web PubSub (use azure-web-pubsub).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Service Bus Skill

This skill provides expert guidance for Azure Service Bus. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L46 | Diagnosing and fixing Service Bus errors: AMQP issues, tracing, .NET/current SDK exceptions, ARM/Resource Manager failures, and common connectivity or messaging problems. |
| Best Practices | L47-L61 | Guidance on reliable messaging patterns: duplicates, FIFO/sessions, locks/settlement, dead-letter handling, serialization, performance tuning, prefetch, timeouts, retries, and maintenance. |
| Decision Making | L62-L70 | Guidance on choosing Service Bus vs other messaging options, configuring geo-disaster recovery/replication, Java/JMS client choices, and migrating from Standard to Premium. |
| Architecture & Design Patterns | L71-L79 | Patterns for resilient, geo-replicated, multi-namespace Service Bus architectures, including federation, message replication, partitioned entities, and using NServiceBus for message-driven systems. |
| Limits & Quotas | L80-L87 | Details on Service Bus size/throughput limits, quotas, throttling behavior, and how Premium tier handles large messages and high-scale workloads. |
| Security | L88-L110 | Securing Service Bus: auth with Entra ID/SAS/managed identities, network isolation (VNet, Private Link, firewalls, perimeters), encryption/CMK, TLS policies, and compliance/Azure Policy. |
| Configuration | L111-L136 | Configuring and managing Service Bus entities: forwarding, sessions, partitioning, TTL, dead-lettering, monitoring/metrics, SQL filters/actions, ARM/PowerShell, geo-replication, and local emulation. |
| Integrations & Coding Patterns | L137-L152 | Patterns and code for integrating Service Bus with JMS (1.1/2.0), RabbitMQ, Event Grid/Logic Apps/Functions, subscription filters/actions, replication tasks, and batch message deletion. |
| Deployment | L153-L162 | Deploying Service Bus namespaces and entities (queues, topics, subscriptions, rules) using ARM/Bicep templates, and moving namespaces across Azure regions. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot AMQP errors in Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-amqp-troubleshoot |
| Configure end-to-end tracing for Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-end-to-end-tracing |
| Diagnose and resolve Azure Service Bus .NET exceptions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-messaging-exceptions |
| Handle Azure Service Bus messaging exceptions (current SDK) | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-messaging-exceptions-latest |
| Diagnose Azure Service Bus Resource Manager exceptions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-resource-manager-exceptions |
| Troubleshoot common Azure Service Bus issues | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-troubleshooting-guide |

### Best Practices
| Topic | URL |
|-------|-----|
| Configure duplicate message detection in Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/duplicate-detection |
| Use sequencing and timestamps in Service Bus messages | https://learn.microsoft.com/en-us/azure/service-bus-messaging/message-sequencing |
| Implement FIFO and request-response with Service Bus sessions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/message-sessions |
| Handle Service Bus message transfers, locks, and settlement correctly | https://learn.microsoft.com/en-us/azure/service-bus-messaging/message-transfers-locks-settlement |
| Prepare Service Bus namespaces for planned maintenance | https://learn.microsoft.com/en-us/azure/service-bus-messaging/prepare-for-planned-maintenance |
| Handle Azure Service Bus dead-letter queues correctly | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-dead-letter-queues |
| Prevent message loss and duplicates in Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-message-loss-and-duplicates |
| Handle messages and serialization in Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-messages-payloads |
| Optimize Azure Service Bus performance with client and protocol tuning | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-performance-improvements |
| Tune Azure Service Bus prefetch for performance | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-prefetch |
| Configure Service Bus timeouts and retry policies | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-timeouts-retries |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose between Azure Event Grid, Event Hubs, and Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/compare-messaging-services |
| Decide between Azure Storage queues and Service Bus queues | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-azure-and-service-bus-queues-compared-contrasted |
| Set up Service Bus Geo-Disaster Recovery | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-geo-dr |
| Choose between JMS and native Java SDK for Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-jms-versus-native-sdk |
| Migrate Azure Service Bus from Standard to Premium | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-migrate-standard-premium |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Build message-driven systems on Service Bus with NServiceBus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/build-message-driven-apps-nservicebus |
| Design Service Bus federation and replication topologies | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-federation-overview |
| Implement Service Bus message replication patterns | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-federation-patterns |
| Design multi-namespace Service Bus for resilience | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-outages-disasters |
| Design and create partitioned Service Bus queues and topics | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-partitioning |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure Service Bus limits and behaviors | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-faq |
| Use Azure Service Bus Premium tier for large messages | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-premium-messaging |
| Reference Azure Service Bus quotas and limits | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-quotas |
| Understand Azure Service Bus throttling limits and behavior | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-throttling |

### Security
| Topic | URL |
|-------|-----|
| Authenticate applications to Azure Service Bus with Entra ID | https://learn.microsoft.com/en-us/azure/service-bus-messaging/authenticate-application |
| Enable confidential computing for Service Bus Premium | https://learn.microsoft.com/en-us/azure/service-bus-messaging/confidential-computing |
| Configure customer-managed keys for Service Bus encryption | https://learn.microsoft.com/en-us/azure/service-bus-messaging/configure-customer-managed-key |
| Disable SAS local authentication for Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/disable-local-authentication |
| Configure network security for Azure Service Bus namespaces | https://learn.microsoft.com/en-us/azure/service-bus-messaging/network-security |
| Secure Azure Service Bus with network security perimeters | https://learn.microsoft.com/en-us/azure/service-bus-messaging/network-security-perimeter |
| Use built-in Azure Policy definitions for Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/policy-reference |
| Secure Azure Service Bus with Private Link Service | https://learn.microsoft.com/en-us/azure/service-bus-messaging/private-link-service |
| Apply regulatory compliance policies to Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/security-controls-policy |
| Configure authentication and authorization for Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-authentication-and-authorization |
| Configure IP firewall rules for Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-ip-filtering |
| Use managed identities to securely access Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-managed-service-identity |
| Migrate Service Bus apps to passwordless Entra ID auth | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-migrate-azure-credentials |
| Create Service Bus authorization rules with ARM templates | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-resource-manager-namespace-auth-rule |
| Implement Shared Access Signature authorization for Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-sas |
| Configure Service Bus virtual network service endpoints | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-service-endpoints |
| Audit Service Bus TLS minimum version compliance with Azure Policy | https://learn.microsoft.com/en-us/azure/service-bus-messaging/transport-layer-security-audit-minimum-version |
| Configure minimum TLS version for a Service Bus namespace | https://learn.microsoft.com/en-us/azure/service-bus-messaging/transport-layer-security-configure-minimum-version |
| Enforce minimum TLS version for Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/transport-layer-security-enforce-minimum-version |

### Configuration
| Topic | URL |
|-------|-----|
| Map classic Service Bus management APIs to ARM | https://learn.microsoft.com/en-us/azure/service-bus-messaging/deprecate-service-bus-management |
| Configure auto-forwarding for Service Bus queues and subscriptions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/enable-auto-forward |
| Enable dead-lettering for Service Bus queues and subscriptions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/enable-dead-letter |
| Configure duplicate message detection in Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/enable-duplicate-detection |
| Enable and configure Service Bus message sessions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/enable-message-sessions |
| Enable partitioning for Service Bus queues and topics | https://learn.microsoft.com/en-us/azure/service-bus-messaging/enable-partitions-basic-standard |
| Suspend and reactivate Azure Service Bus entities | https://learn.microsoft.com/en-us/azure/service-bus-messaging/entity-suspend |
| Use Azure Service Bus message browsing and peek operations | https://learn.microsoft.com/en-us/azure/service-bus-messaging/message-browsing |
| Retrieve Service Bus queue and subscription message counts | https://learn.microsoft.com/en-us/azure/service-bus-messaging/message-counters |
| Configure message expiration and TTL in Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/message-expiration |
| Configure monitoring for Azure Service Bus with Azure Monitor | https://learn.microsoft.com/en-us/azure/service-bus-messaging/monitor-service-bus |
| Use Azure Monitor metrics and logs for Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/monitor-service-bus-reference |
| Use AMQP request/response operations in Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-amqp-request-response |
| Configure autoforwarding between Azure Service Bus entities | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-auto-forwarding |
| Configure Azure Functions-based Service Bus replication tasks | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-federation-configuration |
| Configure Azure Service Bus Geo-Replication across regions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-geo-replication |
| Use Azure Monitor insights for Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-insights |
| Manage Service Bus resources with Azure PowerShell | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-manage-with-ps |
| Programmatically manage Service Bus namespaces and entities | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-management-libraries |
| Use SQL filter syntax for Service Bus subscription rules | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-messaging-sql-filter |
| Use SQL action syntax for Service Bus subscription rules | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-messaging-sql-rule-action |
| Configure and run Azure Service Bus local emulator | https://learn.microsoft.com/en-us/azure/service-bus-messaging/test-locally-with-service-bus-emulator |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Programmatically delete Service Bus messages in batches | https://learn.microsoft.com/en-us/azure/service-bus-messaging/batch-delete |
| Use JMS 2.0 API with Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/how-to-use-java-message-service-20 |
| Develop Azure Service Bus clients using JMS 2.0 | https://learn.microsoft.com/en-us/azure/service-bus-messaging/jms-developer-guide |
| Migrate JMS apps from ActiveMQ to Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/migrate-jms-activemq-to-servicebus |
| Use legacy .NET Service Bus library with AMQP | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-amqp-dotnet |
| Build Service Bus replication tasks with Azure Functions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-federation-replicator-functions |
| Define Azure Service Bus subscription filters and actions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-filter-examples |
| Integrate RabbitMQ with Azure Service Bus | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-integrate-with-rabbitmq |
| Use JMS 1.1 with AMQP on Service Bus Standard | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-java-how-to-use-jms-api-amqp |
| Integrate Azure Service Bus with Event Grid | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-to-event-grid-integration-concept |
| Integrate Service Bus events with Event Grid and Logic Apps | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-to-event-grid-integration-example |
| Handle Service Bus events via Event Grid and Azure Functions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-to-event-grid-integration-function |

### Deployment
| Topic | URL |
|-------|-----|
| Move an Azure Service Bus namespace across regions | https://learn.microsoft.com/en-us/azure/service-bus-messaging/move-across-regions |
| Create a Service Bus namespace with ARM template | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-resource-manager-namespace |
| Deploy Service Bus namespace and queue via ARM template | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-resource-manager-namespace-queue |
| Deploy Service Bus namespace and queue using Bicep | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-resource-manager-namespace-queue-bicep |
| Deploy Service Bus namespace, topic, and subscription via ARM | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-resource-manager-namespace-topic |
| Deploy Service Bus topic, subscription, and rule via ARM | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-resource-manager-namespace-topic-with-rule |
| Deploy Service Bus resources using ARM templates | https://learn.microsoft.com/en-us/azure/service-bus-messaging/service-bus-resource-manager-overview |