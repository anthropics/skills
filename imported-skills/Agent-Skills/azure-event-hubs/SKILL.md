---
name: azure-event-hubs
description: Expert knowledge for Azure Event Hubs development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using Kafka clients/Streams, .NET SDK, geo-replication/DR, app groups throttling, or Event Hubs emulator, and other Azure Event Hubs related development tasks. Not for Azure Service Bus (use azure-service-bus), Azure Event Grid (use azure-event-grid), Azure Notification Hubs (use azure-notification-hubs), Azure Stream Analytics (use azure-stream-analytics).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Event Hubs Skill

This skill provides expert guidance for Azure Event Hubs. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L49 | Diagnosing and fixing Event Hubs runtime issues: Kafka/AMQP errors, .NET/legacy exceptions, ARM failures, auth problems, connectivity, and Blob Storage checkpoint store errors. |
| Best Practices | L50-L55 | Guidance on routing events between AMQP, Kafka, and HTTPS, and on designing/scaling Event Hubs with partitions and throughput units for performance and capacity. |
| Decision Making | L56-L63 | Guidance on choosing Event Hubs tiers, auto-inflate settings, geo-replication modes, and planning migrations from Apache Kafka to Event Hubs. |
| Architecture & Design Patterns | L64-L70 | Patterns and guidance for Event Hubs reliability: availability/consistency design, geo-disaster recovery, and building/operating replication tasks (often with Azure Functions). |
| Limits & Quotas | L71-L77 | Event Hubs capacity, throughput, and entity limits; quota rules and enforcement; and using application groups to govern and throttle client access and usage. |
| Security | L78-L105 | Securing Event Hubs: auth (Entra ID, SAS, RBAC, managed identity), encryption and CMKs, network isolation (VNet, NSG, Private Link, NSP), TLS settings, and compliance/governance via Azure Policy. |
| Configuration | L106-L119 | Configuring Event Hubs behavior: partitions, retention, geo-DR, replication, processing units, metrics/logs, app groups, log compaction, and Avro capture schema. |
| Integrations & Coding Patterns | L120-L137 | Patterns and code for integrating Event Hubs with .NET, Kafka (clients, Streams, Connect, Debezium), Flink, Spark, Akka, schema/JSON registry, and adding metadata or managing hubs programmatically |
| Deployment | L138-L144 | Guides for deploying Event Hubs with Kafka mirroring (MirrorMaker 1/2), setting up geo-replication, and running/local-testing Event Hubs apps using the emulator. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Resolve common Azure Event Hubs Kafka migration issues | https://learn.microsoft.com/en-us/azure/event-hubs/apache-kafka-frequently-asked-questions |
| Troubleshoot Azure Event Hubs for Apache Kafka | https://learn.microsoft.com/en-us/azure/event-hubs/apache-kafka-troubleshooting-guide |
| Troubleshoot AMQP errors in Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-amqp-troubleshoot |
| Handle legacy Azure Event Hubs messaging exceptions | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-messaging-exceptions |
| Handle Azure Event Hubs .NET exceptions and recommended actions | https://learn.microsoft.com/en-us/azure/event-hubs/exceptions-dotnet |
| Resolve Azure Resource Manager exceptions for Event Hubs operations | https://learn.microsoft.com/en-us/azure/event-hubs/resource-manager-exceptions |
| Troubleshoot authentication and authorization failures in Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/troubleshoot-authentication-authorization |
| Resolve Blob Storage checkpoint store issues for Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/troubleshoot-checkpoint-store-issues |
| Diagnose and fix Azure Event Hubs connectivity issues | https://learn.microsoft.com/en-us/azure/event-hubs/troubleshooting-guide |

### Best Practices
| Topic | URL |
|-------|-----|
| Exchange Event Hubs events across AMQP, Kafka, and HTTPS | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-exchange-events-different-protocols |
| Scale Azure Event Hubs with partitions and throughput units | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-scalability |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan migration from Apache Kafka to Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/apache-kafka-migration-guide |
| Choose the right Azure Event Hubs tier | https://learn.microsoft.com/en-us/azure/event-hubs/compare-tiers |
| Decide when and how to use Event Hubs Auto Inflate | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-auto-inflate |
| Choose and manage Azure Event Hubs geo-replication modes | https://learn.microsoft.com/en-us/azure/event-hubs/geo-replication |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design for availability and consistency in Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-availability-and-consistency |
| Apply Event Hubs event replication task patterns | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-federation-patterns |
| Design Event Hubs replication tasks with Azure Functions | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-federation-replicator-functions |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Azure Event Hubs platform limits and behavioral details | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-faq |
| Review Azure Event Hubs quotas and limits | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-quotas |
| Govern Event Hubs resources with application groups | https://learn.microsoft.com/en-us/azure/event-hubs/resource-governance-overview |

### Security
| Topic | URL |
|-------|-----|
| Associate network security perimeters with Event Hubs namespaces | https://learn.microsoft.com/en-us/azure/event-hubs/associate-network-security-perimeter |
| Authenticate applications with Entra ID for Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/authenticate-application |
| Authenticate to Event Hubs using managed identities | https://learn.microsoft.com/en-us/azure/event-hubs/authenticate-managed-identity |
| Authenticate to Event Hubs using SAS tokens | https://learn.microsoft.com/en-us/azure/event-hubs/authenticate-shared-access-signature |
| Authorize Event Hubs access using Entra RBAC roles | https://learn.microsoft.com/en-us/azure/event-hubs/authorize-access-azure-active-directory |
| Choose authorization options for Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/authorize-access-event-hubs |
| Configure SAS authorization for Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/authorize-access-shared-access-signature |
| Enable confidential computing for Azure Event Hubs Dedicated | https://learn.microsoft.com/en-us/azure/event-hubs/confidential-computing |
| Configure customer-managed keys for Azure Event Hubs encryption | https://learn.microsoft.com/en-us/azure/event-hubs/configure-customer-managed-key |
| Enable and configure managed identities for Event Hubs namespaces | https://learn.microsoft.com/en-us/azure/event-hubs/enable-managed-identity |
| Configure managed identity for Event Hubs Capture | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-capture-managed-identity |
| Obtain secure connection strings for Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-get-connection-string |
| Configure IP firewall rules for Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-ip-filtering |
| Secure Event Hubs with virtual network service endpoints | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-service-endpoints |
| Configure network security for Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/network-security |
| Secure Event Hubs with Network Security Perimeter | https://learn.microsoft.com/en-us/azure/event-hubs/network-security-perimeter |
| Migrate Event Hubs apps to passwordless authentication with Entra ID | https://learn.microsoft.com/en-us/azure/event-hubs/passwordless-migration-event-hubs |
| Use built-in Azure Policy definitions for Event Hubs governance | https://learn.microsoft.com/en-us/azure/event-hubs/policy-reference |
| Restrict Event Hubs access using Private Link endpoints | https://learn.microsoft.com/en-us/azure/event-hubs/private-link-service |
| Apply regulatory compliance policies to Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/security-controls-policy |
| Audit Event Hubs TLS compliance using Azure Policy | https://learn.microsoft.com/en-us/azure/event-hubs/transport-layer-security-audit-minimum-version |
| Configure Event Hubs client applications to use specific TLS versions | https://learn.microsoft.com/en-us/azure/event-hubs/transport-layer-security-configure-client-version |
| Set minimum TLS version for Azure Event Hubs namespaces | https://learn.microsoft.com/en-us/azure/event-hubs/transport-layer-security-configure-minimum-version |
| Enforce minimum TLS version for Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/transport-layer-security-enforce-minimum-version |

### Configuration
| Topic | URL |
|-------|-----|
| Configure partitioning, retention, and cleanup for Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/configure-event-hub-properties |
| Configure geo-disaster recovery pairing for Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/configure-geo-disaster-recovery |
| Configure processing units for Event Hubs Premium | https://learn.microsoft.com/en-us/azure/event-hubs/configure-processing-units-premium-namespace |
| Dynamically increase partitions in an Event Hub | https://learn.microsoft.com/en-us/azure/event-hubs/dynamically-add-partitions |
| Configure code-free Event Hubs replication tasks | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-federation-configuration |
| Understand and use Event Hubs captured Avro schema | https://learn.microsoft.com/en-us/azure/event-hubs/explore-captured-avro-files |
| Configure Azure Monitor metrics and alerts for Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/monitor-event-hubs |
| Reference for Event Hubs metrics, logs, and diagnostic settings | https://learn.microsoft.com/en-us/azure/event-hubs/monitor-event-hubs-reference |
| Configure Event Hubs application groups for resource governance | https://learn.microsoft.com/en-us/azure/event-hubs/resource-governance-with-app-groups |
| Configure and use log compaction in Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/use-log-compaction |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Add custom metadata to Event Hubs events | https://learn.microsoft.com/en-us/azure/event-hubs/add-custom-data-event |
| Configure Apache Kafka clients for Azure Event Hubs compatibility | https://learn.microsoft.com/en-us/azure/event-hubs/apache-kafka-configurations |
| Use Kafka Streams with Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/apache-kafka-streams |
| Use Kafka transactions with Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/apache-kafka-transactions |
| Connect .NET applications to Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/connect-event-hub |
| Connect Akka Streams to Azure Event Hubs via Kafka | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-kafka-akka-streams-tutorial |
| Use Debezium CDC with Kafka Connect on Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-kafka-connect-debezium |
| Integrate Kafka Connect with Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-kafka-connect-tutorial |
| Connect Apache Flink to Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-kafka-flink-tutorial |
| Connect Apache Spark streaming apps to Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-kafka-spark-tutorial |
| Use .NET management libraries to provision Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-management-libraries |
| Implement client-side schema enforcement for Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/schema-registry-client-side-enforcement |
| Use JSON Schema registry with Kafka clients on Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/schema-registry-json-schema-kafka |
| Choose and use client SDKs for Azure Event Hubs | https://learn.microsoft.com/en-us/azure/event-hubs/sdks |

### Deployment
| Topic | URL |
|-------|-----|
| Mirror Kafka brokers to Event Hubs with MirrorMaker 1 | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-kafka-mirror-maker-tutorial |
| Replicate Kafka clusters to Event Hubs with MirrorMaker 2 | https://learn.microsoft.com/en-us/azure/event-hubs/event-hubs-kafka-mirrormaker-2-tutorial |
| Test Event Hubs applications locally with the emulator | https://learn.microsoft.com/en-us/azure/event-hubs/test-locally-with-event-hub-emulator |
| Configure and operate Event Hubs geo-replication | https://learn.microsoft.com/en-us/azure/event-hubs/use-geo-replication |