---
name: azure-energy-data-services
description: Expert knowledge for Azure Energy Data Services development including troubleshooting, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. Use when configuring ADME partitions/zones, DDMS APIs, large file workflows, Geospatial CZ on AKS, or OSDU Admin UI, and other Azure Energy Data Services related development tasks. Not for Azure Data Explorer (use azure-data-explorer), Azure Synapse Analytics (use azure-synapse-analytics), Azure Data Factory (use azure-data-factory), Azure Databricks (use azure-databricks).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-05"
  generator: "docs2skills/1.0.0"
---
# Azure Energy Data Services Skill

This skill provides expert guidance for Azure Energy Data Services. Covers troubleshooting, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L39 | Diagnosing and fixing manifest ingestion failures in Azure Data Manager for Energy using Airflow logs, including log analysis steps and common error patterns. |
| Decision Making | L40-L45 | Guidance on choosing ADME deployment tiers (Developer vs Standard) and checking which OSDU data/compute services and capabilities are available in each tier. |
| Architecture & Design Patterns | L46-L50 | Guidance on architecting resilient ADME deployments in Azure Energy Data Services, including zone redundancy, disaster recovery strategies, and high-availability design patterns. |
| Security | L51-L65 | Securing Azure Data Manager for Energy: auth tokens, ACLs, encryption, legal tags, user/group entitlements, managed identities, private endpoints, and API Management access control. |
| Configuration | L66-L73 | Configuring Azure Data Manager for Energy: data partitions, analytics zone setup, CORS, audit logging, and milestone upgrade settings. |
| Integrations & Coding Patterns | L74-L94 | Patterns and examples for integrating Azure Energy Data Services with analytics platforms, external data sources, DDMS APIs, logs/monitoring, and large file workflows. |
| Deployment | L95-L98 | Guides for deploying Azure Energy Data Services components, including Geospatial Consumption Zone on AKS and the OSDU Admin UI for Azure Data Manager for Energy administration |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot manifest ingestion in Azure Data Manager for Energy using Airflow logs | https://learn.microsoft.com/en-us/azure/energy-data-services/troubleshoot-manifest-ingestion |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose between Developer and Standard ADME tiers | https://learn.microsoft.com/en-us/azure/energy-data-services/concepts-tier-details |
| Determine which OSDU services are available on ADME | https://learn.microsoft.com/en-us/azure/energy-data-services/osdu-services-on-adme |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design resilient ADME deployments with zones and DR | https://learn.microsoft.com/en-us/azure/energy-data-services/reliability-energy-data-services |

### Security
| Topic | URL |
|-------|-----|
| Use Customer Lockbox to control ADME support access | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-create-lockbox |
| Enable Analytics Consumption Zone with managed identity and storage | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-enable-analytics-consumption-zone |
| Enable legal tags for restricted origin data in Azure Energy | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-enable-legal-tags-restricted-country-of-origin |
| Generate auth and refresh tokens for Azure Data Manager for Energy | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-generate-auth-token |
| Configure and update ACLs on ADME data records | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-manage-acls |
| Configure data security and encryption for Azure Data Manager for Energy | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-manage-data-security-and-encryption |
| Create and manage legal tags for ADME data | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-manage-legal-tags |
| Manage users and OSDU group entitlements in ADME | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-manage-users |
| Secure Azure Data Manager for Energy APIs with API Management | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-secure-apis |
| Create private endpoints for ADME with Azure Private Link | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-set-up-private-links |
| Configure managed identities for Azure Data Manager for Energy | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-use-managed-identity |

### Configuration
| Topic | URL |
|-------|-----|
| Add and manage data partitions in ADME | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-add-more-data-partitions |
| Configure CORS policies for Azure Data Manager for Energy | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-enable-cors |
| Configure and use audit logs in Azure Data Manager for Energy | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-manage-audit-logs |
| Configure milestone upgrade settings for Azure Data Manager for Energy | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-manage-upgrade-settings |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure Energy ACZ with Azure Databricks | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-connect-analytics-consumption-zone-to-databricks |
| Connect Azure Energy ACZ data to Microsoft Fabric | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-connect-analytics-consumption-zone-to-fabric |
| Enable External Data Services and Key Vault access | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-enable-external-data-services |
| Integrate Airflow task logs from ADME with Azure Monitor | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-integrate-airflow-logs-with-azure-monitor |
| Send ADME Elasticsearch logs to Azure Monitor | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-integrate-elastic-logs-with-azure-monitor |
| Export OSDU service logs from ADME to Azure Monitor | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-integrate-osdu-service-logs-with-azure-monitor |
| Register external data sources with ADME EDS | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-register-external-data-services |
| Upload large files via Azure Data Manager for Energy File service API | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-upload-large-files-using-file-service |
| Call Analytics Consumption Zone management APIs with cURL | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-analytics-consumption-zone-apis |
| Work with Petrel data via Petrel DDMS APIs | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-petrel-ddms |
| Read reservoir data using Reservoir DDMS REST APIs | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-reservoir-ddms-apis |
| Use Reservoir DDMS websocket endpoints for data | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-reservoir-ddms-websocket |
| Call RAFS DDMS APIs for rock and fluid samples | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-rock-and-fluid-samples-ddms |
| Call Seismic DDMS APIs with cURL | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-seismic-ddms |
| Use sdutil CLI to interact with Seismic Store | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-seismic-ddms-sdutil |
| Manage well records with Well Delivery DDMS APIs | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-well-delivery-ddms |
| Use Wellbore DDMS APIs for well data | https://learn.microsoft.com/en-us/azure/energy-data-services/tutorial-wellbore-ddms |

### Deployment
| Topic | URL |
|-------|-----|
| Deploy Geospatial Consumption Zone on AKS with Azure Data Manager for Energy | https://learn.microsoft.com/en-us/azure/energy-data-services/how-to-deploy-gcz |