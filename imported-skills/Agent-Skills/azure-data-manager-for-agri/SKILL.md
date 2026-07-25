---
name: azure-data-manager-for-agri
description: Expert knowledge for Azure Data Manager for Agriculture development including limits & quotas, security, configuration, and integrations & coding patterns. Use when setting up BYOL creds/Private Link, ag data ingestion/IoT, AI/nutrient APIs, throttling, or Event Grid logs, and other Azure Data Manager for Agriculture related development tasks. Not for Azure Data Explorer (use azure-data-explorer), Azure Data Factory (use azure-data-factory), Azure Synapse Analytics (use azure-synapse-analytics), Azure Databricks (use azure-databricks).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure Data Manager for Agriculture Skill

This skill provides expert guidance for Azure Data Manager for Agriculture. Covers limits & quotas, security, configuration, and integrations & coding patterns. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Limits & Quotas | L32-L36 | Guidance on API throttling behavior and limits in Azure Data Manager for Agriculture, plus strategies to plan capacity, avoid rate-limit errors, and manage high-volume workloads. |
| Security | L37-L42 | Managing secure BYOL credential storage and configuring Azure Private Link private endpoints for Azure Data Manager for Agriculture services. |
| Configuration | L43-L49 | Configuring diagnostics and Event Grid for Data Manager for Agriculture, including enabling logs, choosing event schemas, and understanding sample event payloads. |
| Integrations & Coding Patterns | L50-L64 | Integrating external ag data sources (farm activities, sensors, weather, satellite imagery, ISVs), configuring ingestion jobs/IoT, and using AI/copilot and nutrient APIs with Azure Data Manager for Agriculture |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Plan and manage API throttling limits for Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/concepts-understanding-throttling |

### Security
| Topic | URL |
|-------|-----|
| Store and manage BYOL credentials securely in Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/concepts-byol-and-credentials |
| Create private endpoints for Azure Data Manager for Agriculture with Azure Private Link | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-set-up-private-links |

### Configuration
| Topic | URL |
|-------|-----|
| Enable and configure diagnostic logging for Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-set-up-audit-logs |
| Configure Azure Event Grid event schemas for Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-use-events |
| Review sample Azure Event Grid events for Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/sample-events |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate and ingest farm activities data into Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/concepts-farm-operations-data |
| Configure Sentinel Hub satellite imagery ingestion for Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/concepts-ingest-satellite-imagery |
| Ingest sensor telemetry into Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/concepts-ingest-sensor-data |
| Integrate weather data providers with Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/concepts-ingest-weather-data |
| Use generative AI and copilot templates with Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/concepts-llm-apis |
| Configure farm activities ingestion jobs in Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-ingest-and-egress-farm-operations-data |
| Integrate Azure Data Manager for Agriculture with farm activities data providers | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-integrate-with-farm-ops-data-provider |
| Install and use ISV solutions with Azure Data Manager for Agriculture APIs | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-set-up-isv-solution |
| Push and consume sensor data as provider and customer in Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-set-up-sensor-as-customer-and-partner |
| Set up sensors as a customer in Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-set-up-sensors-customer |
| Onboard sensor partners and configure IoT Hub ingestion for Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-set-up-sensors-partner |
| Use plant tissue nutrient APIs in Azure Data Manager for Agriculture | https://learn.microsoft.com/en-us/azure/data-manager-for-agri/how-to-use-nutrient-apis |