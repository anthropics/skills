---
name: azure-cache-redis
description: Expert knowledge for Azure Cache for Redis development including troubleshooting, best practices, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. Use when configuring Redis clustering/replication, VNet/Private Link access, TLS/auth, CLI automation, or ARM/Bicep deployments, and other Azure Cache for Redis related development tasks. Not for Azure Managed Redis (use azure-managed-redis), Azure Cosmos DB (use azure-cosmos-db), Azure Table Storage (use azure-table-storage).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-28"
  generator: "docs2skills/1.0.0"
---
# Azure Cache for Redis Skill

This skill provides expert guidance for Azure Cache for Redis. Covers troubleshooting, best practices, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L47 | Diagnosing and fixing Azure Cache for Redis issues: client and server errors, connectivity, latency/timeouts, monitoring, data loss, and using redis-cli for debugging. |
| Best Practices | L48-L61 | Guidance on client usage, resilience, scaling, memory/CPU tuning, Kubernetes optimization, performance testing, and handling failover/patching for Azure Cache for Redis and Enterprise tiers |
| Decision Making | L62-L71 | Guidance on sizing and planning Redis deployments, migrations (including retirement and VNet→Private Link), network isolation choices, and purchasing/managing Azure Redis reservations |
| Architecture & Design Patterns | L72-L76 | Guidance on designing highly available Azure Cache for Redis deployments, including redundancy options, failover behavior, and resilience best practices. |
| Security | L77-L89 | Securing Azure Cache for Redis: auth (Entra, managed identity), network isolation (VNets, Private Link), TLS config, disk encryption, data access policies, and Azure Policy compliance. |
| Configuration | L90-L103 | Configuring Redis cache behavior, replication, persistence, redundancy, maintenance (reboots/updates), and setting up monitoring, diagnostics, and metrics/logs for Azure Cache for Redis. |
| Integrations & Coding Patterns | L104-L115 | Managing Azure Cache for Redis via CLI/PowerShell, routing Redis events to webhooks/endpoints, and importing/exporting cache data with Azure Blob Storage |
| Deployment | L116-L123 | Scaling, upgrading, region-moving, and ARM/Bicep-based deployment of Azure Cache for Redis instances, including safe resize and version/region migration steps. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Use redis-cli to debug Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-redis-cli-tool |
| Resolve common Azure Cache for Redis management issues | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-management-faq |
| Diagnose and fix Azure Cache for Redis monitoring issues | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-monitor-troubleshoot-faq |
| Troubleshoot Redis client issues for Azure Cache | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-troubleshoot-client |
| Troubleshoot connectivity issues with Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-troubleshoot-connectivity |
| Diagnose and fix Azure Cache for Redis data loss | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-troubleshoot-data-loss |
| Troubleshoot Azure Cache for Redis server-side issues | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-troubleshoot-server |
| Troubleshoot latency and timeout issues in Azure Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-troubleshoot-timeouts |

### Best Practices
| Topic | URL |
|-------|-----|
| Use Redis client libraries effectively with Azure Cache | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-client-libraries |
| Improve Azure Redis connection resilience | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-connection |
| Apply development best practices for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-development |
| Use Azure Redis Enterprise and Flash tiers effectively | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-enterprise-tiers |
| Optimize Kubernetes-hosted clients for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-kubernetes |
| Optimize Azure Redis memory management | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-memory-management |
| Run performance testing for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-performance |
| Scale Azure Cache for Redis effectively and safely | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-scale |
| Monitor and manage CPU utilization for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-best-practices-server-load |
| Handle failover and patching in Azure Redis clients | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-failover |

### Decision Making
| Topic | URL |
|-------|-----|
| Plan and execute migrations to Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-migration-guide |
| Choose Azure Redis network isolation options | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-network-isolation |
| Plan and size Azure Cache for Redis deployments | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-planning-faq |
| Choose and manage Azure Redis reservations | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-reserved-pricing |
| Migrate Azure Cache for Redis from VNet injection to Private Link | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-vnet-migration |
| Plan migration for Azure Cache for Redis retirement | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/retirement-faq |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Design high availability for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-high-availability |

### Security
| Topic | URL |
|-------|-----|
| Configure Microsoft Entra authentication for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-azure-active-directory-for-authentication |
| Configure custom data access policies for Azure Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-configure-role-based-access-control |
| Configure disk encryption for Azure Cache for Redis data at rest | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-encryption |
| Configure VNet integration for Premium Azure Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-premium-vnet |
| Use managed identity with Azure Cache for Redis and storage | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-managed-identity |
| Secure Azure Redis with Private Link and VNets | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-private-link |
| Remove TLS 1.0/1.1 and enforce TLS 1.2 for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-remove-tls-10-11 |
| Configure TLS settings for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-tls-configuration |
| Use Azure Policy built-ins for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/policy-reference |

### Configuration
| Topic | URL |
|-------|-----|
| Reboot, flush, and schedule updates for Azure Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-administration |
| Configure Azure Cache for Redis server settings | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-configure |
| Configure active geo-replication for Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-active-geo-replication |
| Configure passive geo-replication for Premium Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-geo-replication |
| Configure additional replicas for Premium Redis caches | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-multi-replicas |
| Configure Redis data persistence for Azure Cache | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-premium-persistence |
| Enable zone redundancy for Azure Redis caches | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-zone-redundancy |
| Configure Azure Monitor insights for Azure Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-insights-overview |
| Configure diagnostic settings for Azure Redis monitoring | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-monitor-diagnostic-settings |
| Use Azure Cache for Redis monitoring metrics and logs | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/monitor-cache-reference |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Route Azure Redis events to web endpoints with CLI | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-event-grid-quickstart-cli |
| Route Azure Redis events to webhooks via portal | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-event-grid-quickstart-portal |
| Route Azure Redis events to web endpoints with PowerShell | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-event-grid-quickstart-powershell |
| Import and export Azure Cache for Redis data via Blob storage | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-import-export-data |
| Use Azure CLI scripts to manage Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cli-samples |
| Administer Azure Cache for Redis using PowerShell | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/how-to-manage-redis-cache-powershell |
| Create and manage Redis caches with Azure CLI | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/scripts/create-manage-cache |
| Provision Premium clustered Redis cache via CLI | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/scripts/create-manage-premium-cache-cluster |

### Deployment
| Topic | URL |
|-------|-----|
| Scale Azure Cache for Redis instances safely | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-scale |
| Upgrade Redis server version for Azure Cache | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-how-to-upgrade |
| Move Azure Cache for Redis instances across regions | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/cache-moving-resources |
| Deploy Azure Cache for Redis with ARM templates | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/redis-cache-arm-provision |
| Deploy Azure Cache for Redis using Bicep templates | https://learn.microsoft.com/en-us/azure/azure-cache-for-redis/redis-cache-bicep-provision |