---
name: azure-planetary-computer-pro
description: Expert knowledge for Microsoft Planetary Computer Pro development including troubleshooting, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when using GeoCatalog/STAC APIs, QGIS/ArcGIS Pro integrations, Entra ID/RBAC access, tiles/mosaics, or ingestion, and other Microsoft Planetary Computer Pro related development tasks. Not for Azure Maps (use azure-maps), Azure Open Datasets (use azure-open-datasets), Azure Data Explorer (use azure-data-explorer).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Microsoft Planetary Computer Pro Skill

This skill provides expert guidance for Microsoft Planetary Computer Pro. Covers troubleshooting, decision making, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L35-L40 | Diagnosing and resolving Planetary Computer Pro GeoCatalog ingestion failures, including error code meanings, common causes, and step-by-step remediation guidance. |
| Decision Making | L41-L45 | Guidance on selecting how to access Planetary Computer Pro data, including connection options, integrations with tools/services, and choosing the best method for your workflow. |
| Limits & Quotas | L46-L50 | Supported file formats, data types, and size/usage limits for datasets and computations in Planetary Computer Pro, including quotas that affect how you process and store data. |
| Security | L51-L62 | Configuring secure access to Planetary Computer Pro/GeoCatalog using Entra ID, RBAC, managed identities, cross-tenant auth, API Management, and SAS tokens for collections. |
| Configuration | L63-L77 | Configuring Planetary Computer Pro data collections: visualization/render settings, colormaps, tiles/mosaics, queryable filters, ingestion sources/credentials, and US Gov cloud endpoints. |
| Integrations & Coding Patterns | L78-L91 | Using GeoCatalog/STAC with code and tools: ingest and bulk-load data, build apps, create collections/items, and integrate with QGIS, ArcGIS Pro, Azure Batch, and other geospatial clients. |
| Deployment | L92-L96 | Deploying and safely deleting Planetary Computer GeoCatalog resources, including deployment steps, best practices, and cleanup to avoid data loss or orphaned assets. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Reference ingestion error codes for Planetary Computer Pro GeoCatalogs | https://learn.microsoft.com/en-us/azure/planetary-computer/error-codes-ingestion |
| Troubleshoot data ingestion issues in Planetary Computer Pro | https://learn.microsoft.com/en-us/azure/planetary-computer/troubleshooting-ingestion |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose connection methods and integrations for Planetary Computer Pro data | https://learn.microsoft.com/en-us/azure/planetary-computer/build-applications-with-planetary-computer-pro |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Use supported data types in Planetary Computer Pro | https://learn.microsoft.com/en-us/azure/planetary-computer/supported-data-types |

### Security
| Topic | URL |
|-------|-----|
| Configure application authentication to Planetary Computer Pro with Entra ID | https://learn.microsoft.com/en-us/azure/planetary-computer/application-authentication |
| Use managed identities with Planetary Computer GeoCatalog | https://learn.microsoft.com/en-us/azure/planetary-computer/assign-managed-identity-geocatalog-resource |
| Authorize cross-tenant partner applications to access Planetary Computer Pro GeoCatalogs | https://learn.microsoft.com/en-us/azure/planetary-computer/authorize-cross-tenant-partner-applications |
| Configure cross-tenant app access to Planetary Computer Pro | https://learn.microsoft.com/en-us/azure/planetary-computer/configure-cross-tenant-application |
| Secure GeoCatalog access via Azure API Management | https://learn.microsoft.com/en-us/azure/planetary-computer/create-api-proxy-geocatalog |
| Generate collection-level SAS tokens for GeoCatalog assets | https://learn.microsoft.com/en-us/azure/planetary-computer/get-collection-sas-token |
| Configure RBAC access for Planetary Computer GeoCatalog | https://learn.microsoft.com/en-us/azure/planetary-computer/manage-access |
| Configure managed identity credentials for Planetary Computer Pro ingestion | https://learn.microsoft.com/en-us/azure/planetary-computer/set-up-ingestion-credentials-managed-identity |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Planetary Computer Pro collections for Explorer visualization | https://learn.microsoft.com/en-us/azure/planetary-computer/collection-configuration-concept |
| Configure collection visualization settings in Planetary Computer Pro portal | https://learn.microsoft.com/en-us/azure/planetary-computer/configure-collection-web-interface |
| Apply sample render configurations for Planetary Computer Pro data visualization | https://learn.microsoft.com/en-us/azure/planetary-computer/data-visualization-samples |
| Configure ingestion sources for Planetary Computer Pro GeoCatalogs | https://learn.microsoft.com/en-us/azure/planetary-computer/ingestion-source |
| Configure mosaic options for Planetary Computer Pro collections | https://learn.microsoft.com/en-us/azure/planetary-computer/mosaic-configurations-for-collections |
| Configure queryables for custom search filters in Planetary Computer Pro | https://learn.microsoft.com/en-us/azure/planetary-computer/queryables-for-explorer-custom-search-filter |
| Configure render settings for Planetary Computer visualization | https://learn.microsoft.com/en-us/azure/planetary-computer/render-configuration |
| Configure SAS-based ingestion credentials for GeoCatalog | https://learn.microsoft.com/en-us/azure/planetary-computer/set-up-ingestion-credentials-sas-tokens |
| Use supported colormaps in Planetary Computer Pro render configurations | https://learn.microsoft.com/en-us/azure/planetary-computer/supported-colormaps |
| Configure tile settings for Planetary Computer Pro STAC collections | https://learn.microsoft.com/en-us/azure/planetary-computer/tile-settings |
| Configure US Government cloud endpoints for Planetary Computer Pro | https://learn.microsoft.com/en-us/azure/planetary-computer/us-government-cloud-support |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Ingest STAC items into GeoCatalog collections | https://learn.microsoft.com/en-us/azure/planetary-computer/add-stac-item-to-collection |
| Use Planetary Computer Pro APIs for STAC data | https://learn.microsoft.com/en-us/azure/planetary-computer/api-tutorial |
| Use Planetary Computer Pro GeoCatalog with Azure Batch | https://learn.microsoft.com/en-us/azure/planetary-computer/azure-batch |
| Build web apps using GeoCatalog STAC APIs and tiles | https://learn.microsoft.com/en-us/azure/planetary-computer/build-web-application |
| Bulk ingest geospatial data with GeoCatalog API | https://learn.microsoft.com/en-us/azure/planetary-computer/bulk-ingestion-api |
| Configure QGIS to connect to Planetary Computer Pro STAC collections | https://learn.microsoft.com/en-us/azure/planetary-computer/configure-qgis |
| Connect ArcGIS Pro to Planetary Computer GeoCatalog | https://learn.microsoft.com/en-us/azure/planetary-computer/create-connection-arc-gis-pro |
| Create STAC collections in GeoCatalog with Python | https://learn.microsoft.com/en-us/azure/planetary-computer/create-stac-collection |
| Create STAC items for Planetary Computer Pro raster assets | https://learn.microsoft.com/en-us/azure/planetary-computer/create-stac-item |
| Integrate third-party geospatial applications with Planetary Computer Pro | https://learn.microsoft.com/en-us/azure/planetary-computer/working-with-partner-applications |

### Deployment
| Topic | URL |
|-------|-----|
| Delete Planetary Computer GeoCatalog resources safely | https://learn.microsoft.com/en-us/azure/planetary-computer/delete-geocatalog-resource |
| Deploy Planetary Computer GeoCatalog resources | https://learn.microsoft.com/en-us/azure/planetary-computer/deploy-geocatalog-resource |