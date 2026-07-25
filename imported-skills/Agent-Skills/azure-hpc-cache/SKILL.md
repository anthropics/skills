---
name: azure-hpc-cache
description: Expert knowledge for Azure HPC Cache development including troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. Use when configuring HPC Cache namespaces, NFS/Blob targets, client access, data ingest scripts, or cache failover, and other Azure HPC Cache related development tasks. Not for Azure Managed Lustre (use azure-managed-lustre), Azure NetApp Files (use azure-netapp-files), Azure Batch (use azure-batch), Azure Virtual Machines (use azure-virtual-machines).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-02-28"
  generator: "docs2skills/1.0.0"
---
# Azure HPC Cache Skill

This skill provides expert guidance for Azure HPC Cache. Covers troubleshooting, best practices, decision making, architecture & design patterns, limits & quotas, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L37-L42 | Diagnosing and resolving Azure HPC Cache issues with Blob storage firewalls and NFS storage targets, including connectivity, access, and configuration problems. |
| Best Practices | L43-L51 | Guidance on optimizing Azure HPC Cache: client load balancing, efficient data movement and manual copy to Blob targets, NFS-on-Blob considerations, and priming caches for better hit rates. |
| Decision Making | L52-L57 | Guidance on when Azure HPC Cache is appropriate, comparing usage models, workload patterns, performance needs, and deciding if/when to adopt it for your architecture. |
| Architecture & Design Patterns | L58-L63 | Designing Azure HPC Cache namespaces across multiple back-end storage systems, and planning regional redundancy, high availability, and failover strategies for cached workloads. |
| Limits & Quotas | L64-L68 | How to request and manage Azure HPC Cache quota increases, including limits on cache instances, capacities, and the support process for raising quotas. |
| Security | L69-L76 | Configuring HPC Cache security: client access policies, directory/AD integration and extended groups, customer-managed encryption keys, and overall cache security settings. |
| Configuration | L77-L90 | Configuring and operating Azure HPC Cache: CLI setup, networking/DNS/NTP, storage targets and namespaces, mounting NFS clients, lifecycle management, metrics, and environment prerequisites. |
| Integrations & Coding Patterns | L91-L98 | Scripts and patterns for ingesting data (msrsync, parallelcp), controlling write-back with flush_file.py, and integrating Azure HPC Cache with Azure NetApp Files. |
| Deployment | L99-L103 | Creating Azure HPC Cache instances via portal/CLI, and recreating or moving existing caches to a different region while preserving configuration and data paths |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Work around Blob firewall issues for HPC Cache targets | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-blob-firewall-fix |
| Troubleshoot NFS storage target issues in Azure HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/troubleshoot-nas |

### Best Practices
| Topic | URL |
|-------|-----|
| Load balance client connections across Azure HPC Cache IPs | https://learn.microsoft.com/en-us/azure/hpc-cache/client-load-balancing |
| Optimize data movement to Azure HPC Cache Blob targets | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-ingest |
| Manually copy data into Azure HPC Cache Blob targets | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-ingest-manual |
| Apply NFS Blob storage considerations with Azure HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/nfs-blob-considerations |
| Prime Azure HPC Cache to improve cache hit rates | https://learn.microsoft.com/en-us/azure/hpc-cache/prime-cache |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose Azure HPC Cache usage models | https://learn.microsoft.com/en-us/azure/hpc-cache/cache-usage-models |
| Decide when Azure HPC Cache fits your workload | https://learn.microsoft.com/en-us/azure/hpc-cache/usage-scenarios |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design Azure HPC Cache aggregated namespaces | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-namespace |
| Design regional redundancy and failover for Azure HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-region-recovery |

### Limits & Quotas
| Topic | URL |
|-------|-----|
| Request Azure HPC Cache quota increases | https://learn.microsoft.com/en-us/azure/hpc-cache/increase-quota |

### Security
| Topic | URL |
|-------|-----|
| Define client access policies for Azure HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/access-policies |
| Configure customer-managed encryption keys for Azure HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/customer-keys |
| Configure directory services and extended groups for HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/directory-services |
| Understand security configuration for Azure HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-security-info |

### Configuration
| Topic | URL |
|-------|-----|
| Set up Azure HPC Cache namespace paths | https://learn.microsoft.com/en-us/azure/hpc-cache/add-namespace-paths |
| Prepare Azure CLI environment for managing HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/az-cli-prerequisites |
| Configure networking, NTP, DNS, and snapshots for HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/configuration |
| Configure storage targets for Azure HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-add-storage |
| Modify Azure HPC Cache storage target settings | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-edit-storage |
| Operate and update Azure HPC Cache instances | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-manage |
| Mount Azure HPC Cache on NFS clients | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-mount |
| Verify environment prerequisites for Azure HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-prerequisites |
| Manage Azure HPC Cache storage target lifecycle | https://learn.microsoft.com/en-us/azure/hpc-cache/manage-storage-targets |
| Monitor Azure HPC Cache metrics and reports | https://learn.microsoft.com/en-us/azure/hpc-cache/metrics |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Use flush_file.py to control HPC Cache write-back | https://learn.microsoft.com/en-us/azure/hpc-cache/custom-flush-script |
| Ingest data to HPC Cache using msrsync | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-ingest-msrsync |
| Use parallelcp script to ingest data for HPC Cache | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-ingest-parallelcp |
| Integrate Azure HPC Cache with Azure NetApp Files | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-netapp |

### Deployment
| Topic | URL |
|-------|-----|
| Create Azure HPC Cache instances via portal or CLI | https://learn.microsoft.com/en-us/azure/hpc-cache/hpc-cache-create |
| Recreate or move Azure HPC Cache to another region | https://learn.microsoft.com/en-us/azure/hpc-cache/move-resource |