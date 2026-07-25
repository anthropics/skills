# Azure Service Selection Guide

Quick reference for choosing the right Azure service based on workload requirements.

---

## Table of Contents

- [Compute Services](#compute-services)
- [Database Services](#database-services)
- [Storage Services](#storage-services)
- [Messaging and Events](#messaging-and-events)
- [Networking](#networking)
- [Security and Identity](#security-and-identity)
- [Monitoring and Observability](#monitoring-and-observability)

---

## Compute Services

### Decision Matrix

| Requirement | Recommended Service |
|-------------|---------------------|
| Event-driven, short tasks (<10 min) | Azure Functions (Consumption) |
| Event-driven, longer tasks (<30 min) | Azure Functions (Premium) |
| Containerized apps, simple deployment | Azure Container Apps |
| Full Kubernetes control | AKS |
| Traditional web apps (PaaS) | App Service |
| GPU, HPC, custom OS | Virtual Machines |
| Batch processing | Azure Batch |
| Simple container from source | App Service (container) |

### Azure Functions vs Container Apps vs AKS vs App Service

| Feature | Functions | Container Apps | AKS | App Service |
|---------|-----------|---------------|-----|-------------|
| Scale to zero | Yes (Consumption) | Yes | No (min 1 node) | No |
| Kubernetes | No | Built on K8s (abstracted) | Full K8s | No |
| Cold start | 1-5s (Consumption) | 0-2s | N/A | N/A |
| Max execution time | 10 min (Consumption), 30 min (Premium) | Unlimited | Unlimited | Unlimited |
| Languages | C#, JS, Python, Java, Go, Rust, PowerShell | Any container | Any container | .NET, Node, Python, Java, PHP, Ruby |
| Pricing model | Per-execution | Per vCPU-second | Per node | Per plan |
| Best for | Event handlers, APIs, scheduled jobs | Microservices, APIs | Complex platforms, multi-team | Web apps, APIs, mobile backends |
| Operational complexity | Low | Low-Medium | High | Low |
| Dapr integration | No | Built-in | Manual | No |
| KEDA autoscaling | No | Built-in | Manual install | No |

**Opinionated recommendation:**
- **Start with App Service** for web apps and APIs — simplest operational model.
- **Use Container Apps** for microservices — serverless containers without Kubernetes complexity.
- **Use AKS** only when you need full Kubernetes API access (custom operators, service mesh, multi-cluster).
- **Use Functions** for event-driven glue (queue processing, webhooks, scheduled jobs).

### VM Size Selection

| Workload | Series | Example | vCPUs | RAM | Use Case |
|----------|--------|---------|-------|-----|----------|
| General purpose | Dv5/Dsv5 | Standard_D4s_v5 | 4 | 16 GB | Web servers, small databases |
| Memory optimized | Ev5/Esv5 | Standard_E8s_v5 | 8 | 64 GB | Databases, caching, analytics |
| Compute optimized | Fv2/Fsv2 | Standard_F8s_v2 | 8 | 16 GB | Batch processing, ML inference |
| Storage optimized | Lsv3 | Standard_L8s_v3 | 8 | 64 GB | Data warehouses, large databases |
| GPU | NCv3/NDv4 | Standard_NC6s_v3 | 6 | 112 GB | ML training, rendering |

**Always use v5 generation or newer** — better price-performance than older series.

---

## Database Services

### Decision Matrix

| Requirement | Recommended Service |
|-------------|---------------------|
| Relational, SQL Server compatible | Azure SQL Database |
| Relational, PostgreSQL | Azure Database for PostgreSQL Flexible Server |
| Relational, MySQL | Azure Database for MySQL Flexible Server |
| Document / multi-model, global distribution | Cosmos DB |
| Key-value cache, sessions | Azure Cache for Redis |
| Time-series, IoT data | Azure Data Explorer (Kusto) |
| Full-text search | Azure AI Search (formerly Cognitive Search) |
| Graph database | Cosmos DB (Gremlin API) |

### Cosmos DB vs Azure SQL vs PostgreSQL

| Feature | Cosmos DB | Azure SQL | PostgreSQL Flexible |
|---------|-----------|-----------|-------------------|
| Data model | Document, key-value, graph, table, column | Relational | Relational + JSON |
| Global distribution | Native multi-region writes | Geo-replication (async) | Read replicas |
| Consistency | 5 levels (strong to eventual) | Strong | Strong |
| Scaling | RU/s (auto or manual) | DTU or vCore | vCore |
| Serverless tier | Yes | Yes | No |
| Best for | Global apps, variable schema, low-latency reads | OLTP, complex queries, transactions | PostgreSQL ecosystem, extensions |
| Pricing model | Per RU/s + storage | Per DTU or per vCore | Per vCore |
| Managed backups | Continuous + point-in-time | Automatic + long-term retention | Automatic |

**Opinionated recommendation:**
- **Default to Azure SQL Serverless** for most relational workloads — auto-pause saves money in dev/staging.
- **Use PostgreSQL Flexible** when you need PostGIS, full-text search, or specific PostgreSQL extensions.
- **Use Cosmos DB** only when you need global distribution, sub-10ms latency, or flexible schema.
- **Never use Cosmos DB** for workloads that need complex joins or transactions across partitions.

### Azure SQL Tier Selection

| Tier | Use Case | Compute | Cost Range |
|------|----------|---------|------------|
| Basic / S0 | Dev/test, tiny workloads | 5 DTUs | $5/month |
| General Purpose (Serverless) | Variable workloads, dev/staging | 0.5-40 vCores (auto-pause) | $40-800/month |
| General Purpose (Provisioned) | Steady production workloads | 2-80 vCores | $150-3000/month |
| Business Critical | High IOPS, low latency, readable secondary | 2-128 vCores | $400-8000/month |
| Hyperscale | Large databases (>4 TB), instant scaling | 2-128 vCores | $200-5000/month |

---

## Storage Services

### Decision Matrix

| Requirement | Recommended Service |
|-------------|---------------------|
| Unstructured data (files, images, backups) | Blob Storage |
| File shares (SMB/NFS) | Azure Files |
| High-performance file shares | Azure NetApp Files |
| Data Lake (analytics, big data) | Data Lake Storage Gen2 |
| Disk storage for VMs | Managed Disks |
| Queue-based messaging (simple) | Queue Storage |
| Table data (simple key-value) | Table Storage (or Cosmos DB Table API) |

### Blob Storage Tiers

| Tier | Access Pattern | Cost (per GB/month) | Access Cost | Use Case |
|------|---------------|---------------------|-------------|----------|
| Hot | Frequent access | $0.018 | Low | Active data, web content |
| Cool | Infrequent (30+ days) | $0.01 | Medium | Backups, older data |
| Cold | Rarely accessed (90+ days) | $0.0036 | Higher | Compliance archives |
| Archive | Almost never (180+ days) | $0.00099 | High (rehydrate required) | Long-term retention |

**Always set lifecycle management policies.** Rule of thumb: Hot for 30 days, Cool for 90 days, Cold or Archive after that.

---

## Messaging and Events

### Decision Matrix

| Requirement | Recommended Service |
|-------------|---------------------|
| Pub/sub, event routing, reactive | Event Grid |
| Reliable message queues, transactions | Service Bus |
| High-throughput event streaming | Event Hubs |
| Simple task queues | Queue Storage |
| IoT device telemetry | IoT Hub |

### Event Grid vs Service Bus vs Event Hubs

| Feature | Event Grid | Service Bus | Event Hubs |
|---------|-----------|-------------|------------|
| Pattern | Pub/Sub events | Message queue / topic | Event streaming |
| Delivery | At-least-once | At-least-once (peek-lock) | At-least-once (partitioned) |
| Ordering | No guarantee | FIFO (sessions) | Per partition |
| Max message size | 1 MB | 256 KB (Standard), 100 MB (Premium) | 1 MB (Standard), 20 MB (Premium) |
| Retention | 24 hours | 14 days (Standard) | 1-90 days |
| Throughput | Millions/sec | Thousands/sec | Millions/sec |
| Best for | Reactive events, webhooks | Business workflows, commands | Telemetry, logs, analytics |
| Dead letter | Yes | Yes | Via capture to storage |

**Opinionated recommendation:**
- **Event Grid** for reactive, fan-out scenarios (blob uploaded, resource created, custom events).
- **Service Bus** for reliable business messaging (orders, payments, workflows). Use topics for pub/sub, queues for point-to-point.
- **Event Hubs** for high-volume telemetry, log aggregation, and streaming analytics.

---

## Networking

### Decision Matrix

| Requirement | Recommended Service |
|-------------|---------------------|
| Global HTTP load balancing + CDN + WAF | Azure Front Door |
| Regional Layer 7 load balancing + WAF | Application Gateway |
| Regional Layer 4 load balancing | Azure Load Balancer |
| DNS management | Azure DNS |
| DNS-based global traffic routing | Traffic Manager |
| Private connectivity to PaaS | Private Endpoints |
| Site-to-site VPN | VPN Gateway |
| Dedicated private connection | ExpressRoute |
| Outbound internet from VNet | NAT Gateway |
| DDoS protection | Azure DDoS Protection |

### Front Door vs Application Gateway vs Load Balancer

| Feature | Front Door | Application Gateway | Load Balancer |
|---------|-----------|-------------------|--------------|
| Layer | 7 (HTTP/HTTPS) | 7 (HTTP/HTTPS) | 4 (TCP/UDP) |
| Scope | Global | Regional | Regional |
| WAF | Yes (Premium) | Yes (v2) | No |
| SSL termination | Yes | Yes | No |
| CDN | Built-in | No | No |
| Health probes | Yes | Yes | Yes |
| Best for | Global web apps, multi-region | Single-region web apps | TCP/UDP workloads, internal LB |

---

## Security and Identity

### Decision Matrix

| Requirement | Recommended Service |
|-------------|---------------------|
| User authentication | Entra ID (Azure AD) |
| B2C customer identity | Entra External ID (Azure AD B2C) |
| Secrets, keys, certificates | Key Vault |
| Service-to-service auth | Managed Identity |
| Network access control | NSGs + Private Endpoints |
| Web application firewall | Front Door WAF or App Gateway WAF |
| Threat detection | Microsoft Defender for Cloud |
| Policy enforcement | Azure Policy |
| Privileged access management | Entra ID PIM |

### Managed Identity Usage

| Scenario | Configuration |
|----------|---------------|
| App Service accessing SQL | System-assigned MI + Azure SQL Entra auth |
| Functions accessing Key Vault | System-assigned MI + Key Vault RBAC |
| AKS pods accessing Cosmos DB | Workload Identity + Cosmos DB RBAC |
| VM accessing Storage | System-assigned MI + Storage RBAC |
| DevOps pipeline deploying | Workload Identity Federation (no secrets) |

**Rule: Every Azure service that supports Managed Identity should use it.** No connection strings with passwords, no service principal secrets in config.

---

## Monitoring and Observability

### Decision Matrix

| Requirement | Recommended Service |
|-------------|---------------------|
| Application performance monitoring | Application Insights |
| Log aggregation and queries | Log Analytics (KQL) |
| Metrics and alerts | Azure Monitor |
| Dashboards | Azure Dashboard or Grafana (managed) |
| Distributed tracing | Application Insights (OpenTelemetry) |
| Cost monitoring | Cost Management + Budgets |
| Security monitoring | Microsoft Defender for Cloud |
| Compliance monitoring | Azure Policy + Regulatory Compliance |

**Every resource should have diagnostic settings** sending logs and metrics to a Log Analytics workspace. Non-negotiable for production.
