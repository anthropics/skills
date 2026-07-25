---
name: azure-container-storage
description: Expert knowledge for Azure Container Storage development including troubleshooting, decision making, limits & quotas, security, and configuration. Use when configuring Elastic SAN-backed pools, CMK encryption, LRS/ZRS redundancy, volume resizing, or Prometheus/Grafana monitoring, and other Azure Container Storage related development tasks. Not for Azure Blob Storage (use azure-blob-storage), Azure Files (use azure-files), Azure Elastic SAN (use azure-elastic-san), Azure NetApp Files (use azure-netapp-files).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Container Storage Skill

This skill provides expert guidance for Azure Container Storage. Covers troubleshooting, decision making, limits & quotas, security, and configuration. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L33-L37 | Diagnosing and fixing Azure Container Storage v1 install failures, pool creation/health issues, and related Kubernetes cluster/storage configuration problems. |
| Decision Making | L38-L45 | Guidance on Azure Container Storage costs (v1 vs v2), billing models, and choosing/configuring redundancy options like LRS vs ZRS and multi-zone setups |
| Limits & Quotas | L46-L51 | Guidance on resizing Azure Container Storage volumes (v2 and v1), including capacity/pool limits, constraints, and steps to safely expand volumes within those limits. |
| Security | L52-L56 | Configuring customer-managed key (CMK) encryption for Azure Container Storage using Elastic SAN volumes, including setup steps and security considerations. |
| Configuration | L57-L65 | Configuring Azure Container Storage pools, node placement, Elastic SAN integration, and setting up Prometheus/Grafana monitoring and metrics dashboards. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Troubleshoot Azure Container Storage v1 installation and pool issues | https://learn.microsoft.com/en-us/azure/storage/container-storage/troubleshoot-container-storage |

### Decision Making
| Topic | URL |
|-------|-----|
| Understand billing model for Azure Container Storage v2 | https://learn.microsoft.com/en-us/azure/storage/container-storage/container-storage-billing |
| Understand billing model for Azure Container Storage v1 | https://learn.microsoft.com/en-us/azure/storage/container-storage/container-storage-billing-version-1 |
| Choose LRS vs ZRS for Azure Container Storage | https://learn.microsoft.com/en-us/azure/storage/container-storage/enable-multi-zone-redundancy |
| Configure multi-zone redundancy for Azure Container Storage v1 | https://learn.microsoft.com/en-us/azure/storage/container-storage/enable-multi-zone-redundancy-version-1 |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Resize Azure Container Storage volumes within capacity limits | https://learn.microsoft.com/en-us/azure/storage/container-storage/resize-volume |
| Resize Azure Container Storage v1 volumes within pool limits | https://learn.microsoft.com/en-us/azure/storage/container-storage/resize-volume-version-1 |

### Security
| Topic | URL |
|-------|-----|
| Configure CMK-based encryption for Elastic SAN volumes | https://learn.microsoft.com/en-us/azure/storage/container-storage/configure-encryption-for-elastic-san |

### Configuration
| Topic | URL |
|-------|-----|
| Reference storage pool parameters for Azure Container Storage v1 | https://learn.microsoft.com/en-us/azure/storage/container-storage/container-storage-storage-pool-parameters |
| Enable Prometheus monitoring for Azure Container Storage | https://learn.microsoft.com/en-us/azure/storage/container-storage/enable-monitoring |
| Enable Prometheus monitoring for Azure Container Storage v1 | https://learn.microsoft.com/en-us/azure/storage/container-storage/enable-monitoring-version-1 |
| Configure node affinity for local CSI driver placement | https://learn.microsoft.com/en-us/azure/storage/container-storage/manage-local-container-storage-interface-driver-placement |
| Configure Azure Container Storage with Elastic SAN | https://learn.microsoft.com/en-us/azure/storage/container-storage/use-container-storage-with-elastic-san |
| Use Azure Managed Grafana dashboards for container storage | https://learn.microsoft.com/en-us/azure/storage/container-storage/use-grafana-dashboard |