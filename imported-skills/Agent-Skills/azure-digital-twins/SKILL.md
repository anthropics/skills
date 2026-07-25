---
name: azure-digital-twins
description: Expert knowledge for Azure Digital Twins development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when modeling with DTDL, querying twin graphs, integrating IoT Hub/Functions, or migrating control plane APIs, and other Azure Digital Twins related development tasks. Not for Azure IoT Hub (use azure-iot-hub), Azure IoT Central (use azure-iot-central), Azure IoT Edge (use azure-iot-edge), Azure IoT Operations (use azure-iot-operations).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure Digital Twins Skill

This skill provides expert guidance for Azure Digital Twins. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L46 | Diagnosing and fixing common Azure Digital Twins issues: 403/404 errors, Explorer auth problems, CLI parse failures, known bugs, and performance troubleshooting. |
| Best Practices | L47-L53 | Guidance on modeling best practices: converting RDF/OWL ontologies to DTDL, extending DTDL for Azure Digital Twins, and designing effective tagging patterns for twin graphs. |
| Decision Making | L54-L59 | Guidance on selecting DTDL-based industry ontologies for your twin models and instructions for migrating from Azure Digital Twins preview control plane APIs to current APIs. |
| Architecture & Design Patterns | L60-L65 | Patterns for routing data into/out of Azure Digital Twins, plus strategies for high availability, redundancy, and disaster recovery planning and configuration. |
| Limits & Quotas | L66-L71 | Details on Azure Digital Twins query unit usage, plus service limits, throttling behavior, and how to view/request changes to adjustable quotas. |
| Security | L72-L80 | Security guidance for Azure Digital Twins: auth with Entra app registrations, client authentication, Private Link setup, and handling customer personal data and best practices. |
| Configuration | L81-L105 | Configuring and operating Azure Digital Twins: instance setup, security, endpoints/routes, data history, monitoring, graph/twin/model management, Explorer/3D tools, and query language usage. |
| Integrations & Coding Patterns | L106-L122 | APIs, SDKs, CLI, and query usage; integrating IoT Hub, Azure Data Explorer, Functions, Power Platform; coding .NET clients and validating DTDL models for Azure Digital Twins. |
| Deployment | L123-L126 | Guidance for moving an Azure Digital Twins instance to a different region, including prerequisites, supported scenarios, and step-by-step migration procedures. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Fix Azure Digital Twins 403 Forbidden errors | https://learn.microsoft.com/en-us/azure/digital-twins/troubleshoot-error-403-digital-twins |
| Fix Azure Digital Twins 404 sub-domain not found errors | https://learn.microsoft.com/en-us/azure/digital-twins/troubleshoot-error-404-digital-twins |
| Resolve Azure Digital Twins Explorer authentication errors | https://learn.microsoft.com/en-us/azure/digital-twins/troubleshoot-error-azure-digital-twins-explorer-authentication |
| Resolve Azure Digital Twins CLI parse failed errors | https://learn.microsoft.com/en-us/azure/digital-twins/troubleshoot-error-cli-parse |
| Resolve known issues in Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/troubleshoot-known-issues |
| Troubleshoot Azure Digital Twins performance issues | https://learn.microsoft.com/en-us/azure/digital-twins/troubleshoot-performance |

### Best Practices
| Topic | URL |
|-------|-----|
| Convert RDF/OWL ontologies to DTDL models | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-ontologies-convert |
| Extend DTDL ontologies for Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-ontologies-extend |
| Implement tagging patterns for Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-use-tags |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose DTDL-based industry ontologies for Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-ontologies-adopt |
| Migrate from Azure Digital Twins preview control plane APIs | https://learn.microsoft.com/en-us/azure/digital-twins/resources-migrate-from-preview-apis |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design data ingress and egress for Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-data-ingress-egress |
| Plan high availability and disaster recovery for Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-high-availability-disaster-recovery |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Understand Query Unit consumption in Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-query-units |
| Azure Digital Twins service limits and adjustable quotas | https://learn.microsoft.com/en-us/azure/digital-twins/reference-service-limits |

### Security
| Topic | URL |
|-------|-----|
| Apply security best practices to Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-security |
| Implement client authentication for Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-authenticate-client |
| Create Entra app registration for Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-create-app-registration |
| Enable Private Link for Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-enable-private-link |
| Handle customer personal data in Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/resources-customer-data-requests |

### Configuration
| Topic | URL |
|-------|-----|
| Interpret Azure Digital Twins event notifications | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-event-notifications |
| Configure endpoints and event routes in Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-route-events |
| Set up Azure Digital Twins data history connection | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-create-data-history-connection |
| Configure Azure Digital Twins event endpoints | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-create-endpoints |
| Configure event routes and filters in Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-create-routes |
| Manage Azure Digital Twins graphs and relationships | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-manage-graph |
| Manage DTDL models in Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-manage-model |
| Manage individual digital twins via APIs/SDKs | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-manage-twin |
| Configure monitoring, metrics, and logs for Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-monitor |
| Provision and secure Digital Twins via CLI | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-set-up-instance-cli |
| Set up an Azure Digital Twins instance in portal | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-set-up-instance-portal |
| Use 3D Scenes Studio features with Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-use-3d-scenes-studio |
| Operate Azure Digital Twins Explorer features | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-use-azure-digital-twins-explorer |
| Use FROM clause in Azure Digital Twins query language | https://learn.microsoft.com/en-us/azure/digital-twins/reference-query-clause-from |
| Use JOIN clause in Azure Digital Twins graph queries | https://learn.microsoft.com/en-us/azure/digital-twins/reference-query-clause-join |
| Use MATCH clause for graph traversal in Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/reference-query-clause-match |
| Use SELECT clause in Azure Digital Twins query language | https://learn.microsoft.com/en-us/azure/digital-twins/reference-query-clause-select |
| Use WHERE clause in Azure Digital Twins queries | https://learn.microsoft.com/en-us/azure/digital-twins/reference-query-clause-where |
| Use functions in Azure Digital Twins query language | https://learn.microsoft.com/en-us/azure/digital-twins/reference-query-functions |
| Use operators in Azure Digital Twins query language | https://learn.microsoft.com/en-us/azure/digital-twins/reference-query-operators |
| Reserved keywords in Azure Digital Twins query language | https://learn.microsoft.com/en-us/azure/digital-twins/reference-query-reserved |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Work with Azure Digital Twins APIs and SDKs | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-apis-sdks |
| Use Azure Digital Twins CLI command set | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-cli |
| Query Digital Twins via Azure Data Explorer plugin | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-data-explorer-plugin |
| Configure data history with Azure Data Explorer | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-data-history |
| Use Azure Digital Twins query language | https://learn.microsoft.com/en-us/azure/digital-twins/concepts-query-language |
| Ingest IoT Hub telemetry into Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-ingest-iot-hub-data |
| Parse and validate DTDL models with .NET | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-parse-models |
| Query Azure Digital Twins graphs with examples | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-query-graph |
| Set up twin-to-twin event propagation with Azure Functions | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-send-twin-to-twin-events |
| Call Azure Digital Twins REST APIs using .http files | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-use-apis |
| Use Power Platform connector with Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-use-power-platform-logic-apps-connector |
| Code a .NET client for Azure Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/tutorial-code |
| Use Azure CLI commands with Digital Twins | https://learn.microsoft.com/en-us/azure/digital-twins/tutorial-command-line-cli |

### Deployment
| Topic | URL |
|-------|-----|
| Move an Azure Digital Twins instance across regions | https://learn.microsoft.com/en-us/azure/digital-twins/how-to-move-regions |