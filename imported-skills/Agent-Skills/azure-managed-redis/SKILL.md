---
name: azure-managed-redis
description: Expert knowledge for Azure Managed Redis development including troubleshooting, best practices, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. Use when using Azure Managed Redis clustering, sharding, persistence, geo-replication, Entra auth, or Private Link, and other Azure Managed Redis related development tasks. Not for Azure Cache for Redis (use azure-cache-redis).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-06-21"
  generator: "docs2skills/1.0.0"
---
# Azure Managed Redis Skill

This skill provides expert guidance for Azure Managed Redis. Covers troubleshooting, best practices, decision making, architecture & design patterns, security, configuration, integrations & coding patterns, and deployment. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Troubleshooting | L36-L47 | Diagnosing and fixing Azure Managed Redis issues: connectivity, latency/timeouts, data loss, server resources, client performance, common errors, and using Redis Insight/redis-cli for troubleshooting. |
| Best Practices | L48-L63 | Guidance on client and app design, connections, scaling, memory, performance, Kubernetes hosting, monitoring, failover, and troubleshooting best practices for Azure Managed Redis. |
| Decision Making | L64-L76 | Guidance on choosing Managed Redis vs other tiers, planning capacity and reservations, and selecting/migrating from Basic/Standard/Premium or Redis Enterprise to Azure Managed Redis |
| Architecture & Design Patterns | L77-L81 | Details of Azure Managed Redis internals: cluster architecture, sharding, high availability, persistence, networking, scaling behavior, and how these design choices affect performance and reliability. |
| Security | L82-L92 | Securing Azure Managed Redis: TLS, Entra auth, ACLs, disk encryption, Private Link, security best practices, and applying Azure Policy compliance controls. |
| Configuration | L93-L107 | How to configure and operate Azure Managed Redis: instance settings, modules, persistence, geo-replication, monitoring/diagnostics, Grafana, CLI/PowerShell, migration, and data import/export. |
| Integrations & Coding Patterns | L108-L120 | Patterns and code samples for connecting apps (ASP.NET, Go, Node.js, Python, Functions) to Azure Managed Redis, securing with Entra ID, caching, keyspace notifications, and data import/export. |
| Deployment | L121-L130 | Scaling, version upgrades, migrations from Basic/Standard/Premium or Redis Enterprise, ARM/Bicep deployment, and configuring maintenance windows for Azure Managed Redis. |

### Troubleshooting
| Topic | URL |
|-------|-----|
| Use Redis Insight and redis-cli with Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/how-to-redis-access-data |
| Resolve common Azure Managed Redis management issues | https://learn.microsoft.com/en-us/azure/redis/management-faq |
| Diagnose and fix Azure Managed Redis common errors | https://learn.microsoft.com/en-us/azure/redis/monitor-troubleshoot-faq |
| Resolve Azure Managed Redis client-side performance issues | https://learn.microsoft.com/en-us/azure/redis/troubleshoot-client |
| Troubleshoot connectivity issues in Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/troubleshoot-connectivity |
| Diagnose and mitigate data loss in Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/troubleshoot-data-loss |
| Troubleshoot Azure Managed Redis server resource issues | https://learn.microsoft.com/en-us/azure/redis/troubleshoot-server |
| Diagnose latency and timeout problems in Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/troubleshoot-timeouts |

### Best Practices
| Topic | URL |
|-------|-----|
| Apply client library best practices for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/best-practices-client-libraries |
| Design resilient connections to Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/best-practices-connection |
| Apply development best practices for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/best-practices-development |
| Apply best practices for Flash Optimized Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/best-practices-flash-optimized |
| Host Kubernetes clients for Azure Managed Redis effectively | https://learn.microsoft.com/en-us/azure/redis/best-practices-kubernetes |
| Optimize memory management in Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/best-practices-memory-management |
| Run performance testing for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/best-practices-performance |
| Apply scaling best practices for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/best-practices-scale |
| Monitor and manage Azure Managed Redis server load | https://learn.microsoft.com/en-us/azure/redis/best-practices-server-load |
| Resolve common Azure Managed Redis development issues | https://learn.microsoft.com/en-us/azure/redis/development-faq |
| Handle failover and patching for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/failover |
| Apply patterns and best practices for Azure Redis | https://learn.microsoft.com/en-us/azure/redis/faq |

### Decision Making
| Topic | URL |
|-------|-----|
| Choose migration options to Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-basic-standard-premium-options |
| Plan migration from Basic/Standard/Premium to Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-basic-standard-premium-overview |
| Compare Azure Cache tiers with Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-basic-standard-premium-understand |
| Choose migration options from Redis Enterprise to Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-redis-enterprise-options |
| Plan migration from Redis Enterprise to Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-redis-enterprise-overview |
| Understand differences between Redis Enterprise and Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-redis-enterprise-understand |
| Select an approach to migrate to Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migration-guide |
| Plan Azure Managed Redis deployments and capacity | https://learn.microsoft.com/en-us/azure/redis/planning-faq |
| Choose and purchase Azure Managed Redis reservations | https://learn.microsoft.com/en-us/azure/redis/reserved-pricing |

### Architecture & Design Patterns
| Topic | URL |
|-------|-----|
| Understand Azure Managed Redis architecture internals | https://learn.microsoft.com/en-us/azure/redis/architecture |

### Security
| Topic | URL |
|-------|-----|
| Configure custom Redis ACL permissions in Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/configure-access-permissions |
| Configure Microsoft Entra authentication for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/entra-for-authentication |
| Configure customer-managed disk encryption for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/how-to-encryption |
| Secure Azure Managed Redis with Private Link endpoints | https://learn.microsoft.com/en-us/azure/redis/private-link |
| Apply security best practices to Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/secure-azure-managed-redis |
| Apply Azure Policy compliance controls to Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/security-controls-policy |
| Configure TLS settings for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/tls-configuration |

### Configuration
| Topic | URL |
|-------|-----|
| Configure Azure Managed Redis instance settings | https://learn.microsoft.com/en-us/azure/redis/configure |
| Configure built-in Grafana dashboards for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/grafana-dashboards |
| Set up active geo-replication for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/how-to-active-geo-replication |
| Administer Azure Managed Redis using PowerShell | https://learn.microsoft.com/en-us/azure/redis/how-to-manage-redis-cache-powershell |
| Configure persistence options for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/how-to-persistence |
| Configure Azure migration tooling for Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-basic-standard-premium-with-tooling |
| Configure monitoring and alerts for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/monitor-cache |
| Reference metrics and logs for Azure Managed Redis monitoring | https://learn.microsoft.com/en-us/azure/redis/monitor-cache-reference |
| Configure diagnostic settings for Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/monitor-diagnostic-settings |
| Configure Redis modules on Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/redis-modules |
| Manage Azure Managed Redis via Azure CLI | https://learn.microsoft.com/en-us/azure/redis/scripts/create-manage-cache |

### Integrations & Coding Patterns
| Topic | URL |
|-------|-----|
| Integrate Azure Functions with Azure Redis services using bindings | https://learn.microsoft.com/en-us/azure/azure-functions/functions-bindings-cache |
| Secure ASP.NET Core Web API with Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/aspnet |
| Configure ASP.NET Core output caching with Azure Cache for Redis | https://learn.microsoft.com/en-us/azure/redis/aspnet-core-output-cache-provider |
| Connect .NET apps to Azure Managed Redis with Entra ID | https://learn.microsoft.com/en-us/azure/redis/dotnet |
| Use Redis keyspace notifications in Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/enable-redis-keyspace-notifications |
| Integrate Go applications with Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/go-get-started |
| Import and export Azure Managed Redis data via Blob | https://learn.microsoft.com/en-us/azure/redis/how-to-import-export-data |
| Use Azure Managed Redis from Node.js TypeScript | https://learn.microsoft.com/en-us/azure/redis/nodejs-get-started |
| Connect Python applications to Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/python-get-started |

### Deployment
| Topic | URL |
|-------|-----|
| Upgrade Redis versions in Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/how-to-upgrade |
| Execute migration from Basic/Standard/Premium to Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-basic-standard-premium-self-service |
| Execute Redis Enterprise to Azure Managed Redis migration | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-redis-enterprise-self-service |
| Use built-in tooling to migrate Redis Enterprise to Azure Managed Redis | https://learn.microsoft.com/en-us/azure/redis/migrate/migrate-redis-enterprise-with-tooling |
| Deploy Azure Managed Redis using ARM templates | https://learn.microsoft.com/en-us/azure/redis/redis-cache-arm-provision |
| Deploy Azure Managed Redis with Bicep templates | https://learn.microsoft.com/en-us/azure/redis/redis-cache-bicep-provision |
| Configure maintenance windows for Azure Managed Redis updates | https://learn.microsoft.com/en-us/azure/redis/scheduled-maintenance |