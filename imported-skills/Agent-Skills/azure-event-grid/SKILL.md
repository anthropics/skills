---
name: azure-event-grid
description: Expert knowledge for Azure Event Grid development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. Use when configuring Event Grid topics/subscriptions, MQTT broker routing, webhooks, Event Hubs, or cross-tenant delivery, and other Azure Event Grid related development tasks. Not for Azure Service Bus (use azure-service-bus), Azure Event Hubs (use azure-event-hubs), Azure Notification Hubs (use azure-notification-hubs), Azure Logic Apps (use azure-logic-apps).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure Event Grid Skill

This skill provides expert guidance for Azure Event Grid. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L44 | Diagnosing and fixing Event Grid issues: MQTT broker problems, error codes, common failures, network connectivity, and event subscription validation errors. |
| Best Practices | L45-L49 | Guidance on designing client-side failover for Event Grid, including using multiple regions, retry logic, and resilient publishing patterns for high availability. |
| Decision Making | L50-L57 | Guidance on choosing Event Grid tiers, matching event schemas, comparing Azure vs Kubernetes deployments, and migrating from IoT Edge Event Grid to IoT Edge hub. |
| Architecture & Design Patterns | L58-L63 | Patterns for routing events across Event Grid namespace topics and implementing MQTT-based request/response command workflows using Event Grid. |
| Limits & Quotas | L64-L75 | Event Grid delivery/retry behavior, custom headers, event retention, and region-specific quotas/limits for topics, namespaces, and Kubernetes-based Event Grid |
| Security | L76-L127 | Securing Event Grid with auth, RBAC, managed identities, TLS, IP/firewalls, private endpoints, MQTT/webhook security, cross-tenant delivery, and Azure Policy compliance. |
| Configuration | L128-L200 | Configuring Event Grid: topics, namespaces, subscriptions, filters, dead-lettering, monitoring/metrics, MQTT broker and routing, and detailed event schemas for many Azure and Microsoft services. |
| Integrations & Coding Patterns | L201-L242 | Patterns and tutorials for integrating Event Grid with external services (Auth0, M365, Graph, Teams, SharePoint, Key Vault, MQTT) and configuring HTTP/webhook, Event Hubs, and schema-based handlers. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Event Grid MQTT broker issues | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-troubleshoot-errors |
| Azure Event Grid error codes and resolutions | https://learn.microsoft.com/en-us/azure/event-grid/troubleshoot-errors |
| Troubleshoot common Azure Event Grid issues | https://learn.microsoft.com/en-us/azure/event-grid/troubleshoot-issues |
| Diagnose Azure Event Grid network connectivity failures | https://learn.microsoft.com/en-us/azure/event-grid/troubleshoot-network-connectivity |
| Fix Azure Event Grid subscription validation errors | https://learn.microsoft.com/en-us/azure/event-grid/troubleshoot-subscription-validation |

### Best Practices
| Topic | URL |
|-------|-----|
| Implement client-side failover for Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/custom-disaster-recovery-client-side |

### Decision Making
| Topic | URL |
|-------|-----|
| Select the right Azure Event Grid tier | https://learn.microsoft.com/en-us/azure/event-grid/choose-right-tier |
| Choose compatible event schemas for Azure Event Grid subscriptions | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-compatibility |
| Compare Event Grid on Kubernetes vs Azure features | https://learn.microsoft.com/en-us/azure/event-grid/kubernetes/features |
| Migrate from Event Grid on IoT Edge to IoT Edge hub | https://learn.microsoft.com/en-us/azure/event-grid/transition |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Forward events between Event Grid namespace topics | https://learn.microsoft.com/en-us/azure/event-grid/forward-events-to-another-namespace-topic |
| Implement MQTT request-response commands with Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-request-response-messages |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Azure Event Grid delivery and retry behavior | https://learn.microsoft.com/en-us/azure/event-grid/delivery-and-retry |
| Configure custom delivery headers for Azure Event Grid events | https://learn.microsoft.com/en-us/azure/event-grid/delivery-properties |
| Understand event retention for Event Grid namespace topics | https://learn.microsoft.com/en-us/azure/event-grid/event-retention |
| Azure Event Grid FAQs on limits and behavior | https://learn.microsoft.com/en-us/azure/event-grid/faq |
| Understand Event Grid on Kubernetes delivery and retry behavior | https://learn.microsoft.com/en-us/azure/event-grid/kubernetes/delivery-retry |
| Set custom delivery headers for Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/namespace-delivery-properties |
| Delivery and retry behavior for Event Grid namespace push | https://learn.microsoft.com/en-us/azure/event-grid/namespace-delivery-retry |
| Review Azure Event Grid quotas and limits by region | https://learn.microsoft.com/en-us/azure/event-grid/quotas-limits |

### Security
| Topic | URL |
|-------|-----|
| Assign Event Grid managed identities to Azure roles on destinations | https://learn.microsoft.com/en-us/azure/event-grid/add-identity-roles |
| Use access keys and SAS to authenticate Event Grid clients | https://learn.microsoft.com/en-us/azure/event-grid/authenticate-with-access-keys-shared-access-signatures |
| Authenticate Event Grid namespace publishers with Entra ID | https://learn.microsoft.com/en-us/azure/event-grid/authenticate-with-entra-id-namespaces |
| Configure Microsoft Entra ID auth for Event Grid publishing | https://learn.microsoft.com/en-us/azure/event-grid/authenticate-with-microsoft-entra-id |
| Configure JWT authentication for Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/authenticate-with-namespaces-using-json-web-tokens |
| Configure webhook-based authentication for Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/authenticate-with-namespaces-using-webhook-authentication |
| Authenticate Event Grid publishers to topics and domains | https://learn.microsoft.com/en-us/azure/event-grid/authentication-overview |
| Configure access, identity, and data residency for Event Grid topics | https://learn.microsoft.com/en-us/azure/event-grid/configure-custom-topic |
| Configure IP firewall rules for Event Grid topics and domains | https://learn.microsoft.com/en-us/azure/event-grid/configure-firewall |
| Configure IP firewall rules for Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/configure-firewall-namespaces |
| Configure network security perimeters for Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/configure-network-security-perimeter |
| Configure private endpoints for Event Grid topics securely | https://learn.microsoft.com/en-us/azure/event-grid/configure-private-endpoints |
| Configure private endpoints for Azure Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/configure-private-endpoints-pull |
| Configure private link delivery for Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/consume-private-endpoints |
| Configure cross-tenant Event Grid delivery with managed identity | https://learn.microsoft.com/en-us/azure/event-grid/cross-tenant-delivery-using-managed-identity |
| Enforce Event Grid security controls with custom Azure Policies | https://learn.microsoft.com/en-us/azure/event-grid/custom-azure-policies-for-security-control |
| Configure custom domains for Event Grid MQTT and HTTP | https://learn.microsoft.com/en-us/azure/event-grid/custom-domains-namespaces |
| Deliver Event Grid events securely using managed identities | https://learn.microsoft.com/en-us/azure/event-grid/deliver-events-using-managed-identity |
| Enable managed identity on Event Grid custom topics and domains | https://learn.microsoft.com/en-us/azure/event-grid/enable-identity-custom-topics-domains |
| Enable managed identity on Event Grid partner topics | https://learn.microsoft.com/en-us/azure/event-grid/enable-identity-partner-topic |
| Enable managed identity on Event Grid system topics | https://learn.microsoft.com/en-us/azure/event-grid/enable-identity-system-topics |
| Validate webhook endpoints using CloudEvents schema in Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/end-point-validation-cloud-events-schema |
| Enable and use managed identities for Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/event-grid-namespace-managed-identity |
| Retrieve and manage access keys for Event Grid resources | https://learn.microsoft.com/en-us/azure/event-grid/get-access-keys |
| Use managed identities to deliver events from Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/managed-service-identity |
| Configure MQTT client access control in Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-access-control |
| Authenticate MQTT clients with CA certificate chains | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-certificate-chain-client-authentication |
| Configure MQTT client authentication for Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-client-authentication |
| Configure MQTT client certificate authentication in Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-client-certificate-authentication |
| Configure OAuth 2.0 JWT auth for Event Grid MQTT | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-client-custom-jwt |
| Use Entra JWT auth and RBAC for MQTT clients | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-client-microsoft-entra-token-and-rbac |
| Configure custom webhook authentication for Event Grid MQTT | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-client-webhook-authentication |
| Secure Event Grid MQTT namespaces with IP firewall | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-configure-firewall |
| Configure private endpoints for Event Grid MQTT namespaces | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-configure-private-endpoints |
| Understand TLS connection flow for Event Grid MQTT broker | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-transport-layer-security-flow |
| Secure Azure Event Grid with network rules and private endpoints | https://learn.microsoft.com/en-us/azure/event-grid/network-security |
| Configure network security for Azure Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/network-security-namespaces |
| Authenticate Event Grid namespaces using OAuth JWT | https://learn.microsoft.com/en-us/azure/event-grid/oauth-json-web-token-authentication |
| Built-in Azure Policy definitions for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/policy-reference |
| Secure Event Grid webhook delivery with Entra application | https://learn.microsoft.com/en-us/azure/event-grid/scripts/powershell-webhook-secure-delivery-microsoft-entra-app |
| Secure Event Grid webhook delivery with Entra user | https://learn.microsoft.com/en-us/azure/event-grid/scripts/powershell-webhook-secure-delivery-microsoft-entra-user |
| Secure Event Grid webhooks with Microsoft Entra ID | https://learn.microsoft.com/en-us/azure/event-grid/secure-webhook-delivery |
| Authenticate event delivery to handlers in Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/security-authentication |
| Configure Azure RBAC access control for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/security-authorization |
| Azure Policy regulatory compliance controls for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/security-controls-policy |
| Configure minimum TLS version for Event Grid topics and domains | https://learn.microsoft.com/en-us/azure/event-grid/transport-layer-security-configure-minimum-version |
| Configure minimum TLS version for Event Grid topics/domains | https://learn.microsoft.com/en-us/azure/event-grid/transport-layer-security-configure-minimum-version |
| Enforce minimum TLS versions for Azure Event Grid endpoints | https://learn.microsoft.com/en-us/azure/event-grid/transport-layer-security-enforce-minimum-version |

### Configuration
| Topic | URL |
|-------|-----|
| Configure custom domains for Event Grid MQTT and HTTP | https://learn.microsoft.com/en-us/azure/event-grid/assign-custom-domain-name |
| Azure Communication Services chat events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/communication-services-chat-events |
| Presence events schema for Azure Communication Services | https://learn.microsoft.com/en-us/azure/event-grid/communication-services-presence-events |
| Job Router events schema for Azure Communication Services | https://learn.microsoft.com/en-us/azure/event-grid/communication-services-router-events |
| Azure Communication Services SMS events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/communication-services-telephony-sms-events |
| Voice and video calling events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/communication-services-voice-video-events |
| Create and manage Event Grid namespace event subscriptions | https://learn.microsoft.com/en-us/azure/event-grid/create-view-manage-event-subscriptions |
| Create and manage Event Grid namespace topics | https://learn.microsoft.com/en-us/azure/event-grid/create-view-manage-namespace-topics |
| Configure dead-lettering for Event Grid namespace subscriptions | https://learn.microsoft.com/en-us/azure/event-grid/dead-letter-event-subscriptions-namespace-topics |
| Enable diagnostic logs for Azure Event Grid resources | https://learn.microsoft.com/en-us/azure/event-grid/enable-diagnostic-logs-topic |
| Configure event filtering options in Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-filtering |
| AKS events schema and usage with Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-aks |
| AKS resources events schema for Azure Resource Notifications | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-aks-resources |
| Use Azure Cache for Redis as an Event Grid source | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-azure-cache |
| Azure Health Data Services events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-azure-health-data-services |
| Azure Maps events schema for Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-azure-maps |
| Azure SignalR Service events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-azure-signalr |
| Configure Azure Communication Services as Event Grid source | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-communication-services |
| Container Registry events schema for Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-container-registry |
| ContainerService maintenance events schema for AKS notifications | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-containerservice-resources |
| Azure Data Box events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-data-box |
| Event Grid namespace events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-event-grid-namespace |
| Azure Event Hubs events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-event-hubs |
| Health Resources events schema for Azure Resource Notifications | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-health-resources |
| Azure IoT Hub events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-iot-hub |
| Azure Machine Learning workspace events schema | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-machine-learning |
| Maintenance Configuration events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-maintenance-configuration |
| Azure Media Services events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-media-services |
| Azure Policy events schema for Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-policy |
| Resource group lifecycle events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-resource-groups |
| Resource Management events schema for Azure Resource Notifications | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-resources |
| Azure Service Bus events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-service-bus |
| Azure subscription lifecycle events schema for Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-subscriptions |
| Determine schema type for an Event Grid topic | https://learn.microsoft.com/en-us/azure/event-grid/get-topic-schema |
| Manage and publish events with Event Grid event domains | https://learn.microsoft.com/en-us/azure/event-grid/how-to-event-domains |
| Configure event filters on Azure Event Grid subscriptions | https://learn.microsoft.com/en-us/azure/event-grid/how-to-filter-events |
| Map custom event schemas to Azure Event Grid schema | https://learn.microsoft.com/en-us/azure/event-grid/input-mappings |
| Configure batch event delivery for Event Grid on Kubernetes | https://learn.microsoft.com/en-us/azure/event-grid/kubernetes/batch-event-delivery |
| Configure advanced event filtering in Event Grid on Kubernetes | https://learn.microsoft.com/en-us/azure/event-grid/kubernetes/filter-events |
| Install and configure Event Grid extension on Arc-enabled Kubernetes | https://learn.microsoft.com/en-us/azure/event-grid/kubernetes/install-k8s-extension |
| Configure Event Grid dead-lettering and retry policies | https://learn.microsoft.com/en-us/azure/event-grid/manage-event-delivery |
| View Event Grid metrics and configure alerts in Azure portal | https://learn.microsoft.com/en-us/azure/event-grid/monitor-event-delivery |
| Use MQTT broker metrics and logs for monitoring | https://learn.microsoft.com/en-us/azure/event-grid/monitor-mqtt-delivery-reference |
| Monitor data reference for Event Grid namespace push delivery | https://learn.microsoft.com/en-us/azure/event-grid/monitor-namespace-push-reference |
| Configure monitoring and alerts for Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/monitor-namespaces |
| Monitor data reference for Event Grid pull delivery | https://learn.microsoft.com/en-us/azure/event-grid/monitor-pull-reference |
| Reference for Event Grid push delivery metrics and logs | https://learn.microsoft.com/en-us/azure/event-grid/monitor-push-reference |
| Configure MQTT client groups in Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-client-groups |
| Use MQTT client lifecycle events in Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-client-life-cycle-events |
| Configure Azure Event Grid MQTT clients and groups | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-clients |
| Configure multiple MQTT sessions per client in Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-establishing-multiple-sessions-per-client |
| Use MQTT Retain with Azure Event Grid broker | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-retain |
| Configure routing of MQTT messages in Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-routing |
| Configure enrichments for MQTT routed messages | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-routing-enrichment |
| Understand event schema for MQTT routed messages | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-routing-event-schema |
| Configure filtering for MQTT routed Event Grid messages | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-routing-filtering |
| Configure MQTT topic spaces in Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-topic-spaces |
| Configure event filtering for Event Grid namespaces | https://learn.microsoft.com/en-us/azure/event-grid/namespace-event-filtering |
| Microsoft Outlook events schema in Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/outlook-events |
| Microsoft Graph API resource events in Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/partner-events-graph-api |
| Query and list Azure Event Grid subscriptions | https://learn.microsoft.com/en-us/azure/event-grid/query-event-subscriptions |
| Create alerts on Event Grid metrics and activity logs | https://learn.microsoft.com/en-us/azure/event-grid/set-alerts |
| Use Sparkplug B with Azure Event Grid MQTT broker | https://learn.microsoft.com/en-us/azure/event-grid/sparkplug-support |
| Configure Event Grid subscriptions for Microsoft Entra ID events | https://learn.microsoft.com/en-us/azure/event-grid/subscribe-to-microsoft-entra-id-events-portal |
| Subscribe to Azure Resource Notifications AKS Resources events | https://learn.microsoft.com/en-us/azure/event-grid/subscribe-to-resource-notifications-aks-resources-events |
| Subscribe to Azure Resource Notifications ContainerService events | https://learn.microsoft.com/en-us/azure/event-grid/subscribe-to-resource-notifications-containerservice-events |
| Subscribe to Azure Resource Notifications Health Resources events | https://learn.microsoft.com/en-us/azure/event-grid/subscribe-to-resource-notifications-health-resources-events |
| Subscribe to Azure Resource Notifications Resource Management events | https://learn.microsoft.com/en-us/azure/event-grid/subscribe-to-resource-notifications-resources-events |
| Configure Azure Event Grid subscription request schema | https://learn.microsoft.com/en-us/azure/event-grid/subscription-creation-schema |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Connect Auth0 to Azure via Event Grid partner topics | https://learn.microsoft.com/en-us/azure/event-grid/auth0-how-to |
| Send Auth0 events to Application Insights via Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/auth0-log-stream-app-insights |
| Stream Auth0 logs to Blob Storage using Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/auth0-log-stream-blob-storage |
| Use CloudEvents v1.0 schema with Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/cloud-event-schema |
| Use Microsoft Cloud Printing events with Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/cloud-printing-events |
| Use ACS Advanced Messaging events with Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/communication-services-advanced-messaging-events |
| Use Azure Communication Services email events with Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/communication-services-email-events |
| Use Microsoft 365 Group Conversation events with Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/conversation-events |
| Understand Azure Event Grid proprietary event schema | https://learn.microsoft.com/en-us/azure/event-grid/event-schema |
| Use Azure API Center as an Event Grid source | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-api-center |
| Use API Management as an Event Grid source | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-api-management |
| Use Azure App Configuration as an Event Grid source | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-app-configuration |
| Use Azure App Service as an Event Grid source | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-app-service |
| Use Azure Blob Storage as an Event Grid source | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-blob-storage |
| Consume Azure Key Vault events from Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/event-schema-key-vault |
| Alert on Health Resources events using Azure Monitor | https://learn.microsoft.com/en-us/azure/event-grid/handle-health-resources-events-using-azure-monitor-alerts |
| Handle Key Vault expiration events with Azure Monitor alerts | https://learn.microsoft.com/en-us/azure/event-grid/handle-key-vault-events-using-azure-monitor-alerts |
| Use Microsoft Entra event schemas in Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/microsoft-entra-events |
| Route MQTT events to Microsoft Fabric via Event Hubs | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-events-fabric |
| Publish MQTT messages via HTTP using Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-how-to-http-publish |
| Publish MQTT messages via HTTP using Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/mqtt-http-publish |
| Integrate Event Grid namespaces with Event Hubs handlers | https://learn.microsoft.com/en-us/azure/event-grid/namespace-handler-event-hubs |
| Configure webhook handlers for Event Grid namespace topics | https://learn.microsoft.com/en-us/azure/event-grid/namespace-handler-webhook |
| Use supported event handlers for Event Grid namespace push | https://learn.microsoft.com/en-us/azure/event-grid/namespace-topics-event-handlers |
| Use Microsoft OneDrive events with Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/one-drive-events |
| Publish events to Event Grid custom topics with access keys | https://learn.microsoft.com/en-us/azure/event-grid/post-to-custom-topic |
| Push Event Grid namespace events to Event Hubs via CLI | https://learn.microsoft.com/en-us/azure/event-grid/publish-deliver-events-with-namespace-topics |
| Configure Event Grid namespace push to Event Hubs in portal | https://learn.microsoft.com/en-us/azure/event-grid/publish-deliver-events-with-namespace-topics-portal |
| Deliver Event Grid namespace events to webhooks via CLI | https://learn.microsoft.com/en-us/azure/event-grid/publish-deliver-events-with-namespace-topics-webhook |
| Deliver Event Grid namespace events to webhooks using portal | https://learn.microsoft.com/en-us/azure/event-grid/publish-deliver-events-with-namespace-topics-webhook-portal |
| Use HTTP publisher operations for Event Grid namespace topics | https://learn.microsoft.com/en-us/azure/event-grid/publisher-operations |
| Implement HTTP endpoints to receive Event Grid events | https://learn.microsoft.com/en-us/azure/event-grid/receive-events |
| Use Microsoft Security Alert events with Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/security-alert-events |
| Deliver Event Grid events to private webhooks via Azure Relay | https://learn.microsoft.com/en-us/azure/event-grid/send-events-webhooks-private-destinations |
| Use Microsoft SharePoint events with Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/share-point-events |
| Subscribe to Microsoft Graph change events via Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/subscribe-to-graph-api-events |
| Use HTTP subscriber operations for Event Grid namespace topics | https://learn.microsoft.com/en-us/azure/event-grid/subscriber-operations |
| Use Microsoft Teams events with Azure Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/teams-events |
| Use Microsoft To Do task events with Event Grid | https://learn.microsoft.com/en-us/azure/event-grid/to-do-events |