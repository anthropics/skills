# Azure Architecture Patterns

Reference guide for selecting the right Azure architecture pattern based on application requirements.

---

## Table of Contents

- [Pattern Selection Matrix](#pattern-selection-matrix)
- [Pattern 1: App Service Web Application](#pattern-1-app-service-web-application)
- [Pattern 2: Microservices on AKS](#pattern-2-microservices-on-aks)
- [Pattern 3: Serverless Event-Driven](#pattern-3-serverless-event-driven)
- [Pattern 4: Data Pipeline](#pattern-4-data-pipeline)
- [Pattern 5: Multi-Region Active-Active](#pattern-5-multi-region-active-active)
- [Well-Architected Framework Alignment](#well-architected-framework-alignment)

---

## Pattern Selection Matrix

| Pattern | Best For | Users | Monthly Cost | Complexity |
|---------|----------|-------|--------------|------------|
| App Service Web | MVPs, SaaS, APIs | <100K | $50-500 | Low |
| Microservices on AKS | Complex platforms, multi-team | Any | $500-5000 | High |
| Serverless Event-Driven | Event processing, webhooks, APIs | <1M | $20-500 | Low-Medium |
| Data Pipeline | Analytics, ETL, ML | Any | $200-3000 | Medium-High |
| Multi-Region Active-Active | Global apps, 99.99% uptime | >100K | 1.5-2x single | High |

---

## Pattern 1: App Service Web Application

### Architecture

```
                    ┌──────────────┐
                    │  Azure Front │
                    │    Door      │
                    │  (CDN + WAF) │
                    └──────┬───────┘
                           │
                    ┌──────▼───────┐
                    │  App Service │
                    │  (Linux P1v3)│
                    │  + Slots     │
                    └──┬───────┬───┘
                       │       │
              ┌────────▼──┐ ┌──▼────────┐
              │ Azure SQL  │ │  Blob     │
              │ Serverless │ │  Storage  │
              └────────────┘ └───────────┘
                       │
              ┌────────▼──────────┐
              │  Key Vault        │
              │  (secrets, certs) │
              └───────────────────┘
```

### Services

| Service | Purpose | Configuration |
|---------|---------|---------------|
| Azure Front Door | Global CDN, WAF, SSL | Standard or Premium tier, custom domain |
| App Service | Web application hosting | Linux P1v3 (production), B1 (dev) |
| Azure SQL Database | Relational database | Serverless GP_S_Gen5_2 with auto-pause |
| Blob Storage | Static assets, uploads | Hot tier with lifecycle policies |
| Key Vault | Secrets management | RBAC authorization, soft-delete enabled |
| Application Insights | Monitoring and APM | Workspace-based, connected to Log Analytics |
| Entra ID | Authentication | Easy Auth or MSAL library |

### Deployment Strategy

- **Deployment slots**: staging slot for zero-downtime deploys, swap to production after validation
- **Auto-scale**: CPU-based rules, 1-10 instances in production
- **Health checks**: `/health` endpoint monitored by App Service and Front Door

### Cost Estimate

| Component | Dev | Production |
|-----------|-----|-----------|
| App Service | $13 (B1) | $75 (P1v3) |
| Azure SQL | $5 (Basic) | $40-120 (Serverless GP) |
| Front Door | $0 (disabled) | $35-55 |
| Blob Storage | $1 | $5-15 |
| Key Vault | $0.03 | $1-5 |
| Application Insights | $0 (free tier) | $5-20 |
| **Total** | **~$19** | **~$160-290** |

---

## Pattern 2: Microservices on AKS

### Architecture

```
                    ┌──────────────┐
                    │  Azure Front │
                    │    Door      │
                    └──────┬───────┘
                           │
                    ┌──────▼───────┐
                    │  API Mgmt    │
                    │  (gateway)   │
                    └──────┬───────┘
                           │
              ┌────────────▼────────────┐
              │        AKS Cluster       │
              │ ┌───────┐ ┌───────┐     │
              │ │ svc-A │ │ svc-B │     │
              │ └───┬───┘ └───┬───┘     │
              │     │         │          │
              │ ┌───▼─────────▼───┐     │
              │ │   Service Bus    │     │
              │ │   (async msgs)   │     │
              │ └─────────────────┘     │
              └─────────────────────────┘
                       │        │
              ┌────────▼──┐ ┌──▼────────┐
              │ Cosmos DB  │ │  ACR      │
              │ (data)     │ │ (images)  │
              └────────────┘ └───────────┘
```

### Services

| Service | Purpose | Configuration |
|---------|---------|---------------|
| AKS | Container orchestration | 3 node pools: system (D2s_v5), app (D4s_v5), jobs (spot) |
| API Management | API gateway, rate limiting | Standard v2 or Consumption tier |
| Cosmos DB | Multi-model database | Session consistency, autoscale RU/s |
| Service Bus | Async messaging | Standard tier, topics for pub/sub |
| Container Registry | Docker image storage | Basic (dev), Standard (prod) |
| Key Vault | Secrets for pods | CSI driver + workload identity |
| Azure Monitor | Cluster and app observability | Container Insights + App Insights |

### AKS Best Practices

**Node Pools:**
- System pool: 2-3 nodes, D2s_v5, taints for system pods only
- App pool: 2-10 nodes (autoscaler), D4s_v5, for application workloads
- Jobs pool: spot instances, for batch processing and CI runners

**Networking:**
- Azure CNI for VNet-native pod networking
- Network policies (Azure or Calico) for pod-to-pod isolation
- Ingress via NGINX Ingress Controller or Application Gateway Ingress Controller (AGIC)

**Security:**
- Workload Identity for pod-to-Azure service auth (replaces pod identity)
- Azure Policy for Kubernetes (OPA Gatekeeper)
- Defender for Containers for runtime threat detection
- Private cluster for production (API server not exposed to internet)

**Deployment:**
- Helm charts for application packaging
- Flux or ArgoCD for GitOps
- Horizontal Pod Autoscaler (HPA) + KEDA for event-driven scaling

### Cost Estimate

| Component | Dev | Production |
|-----------|-----|-----------|
| AKS nodes (system) | $60 (1x D2s_v5) | $180 (3x D2s_v5) |
| AKS nodes (app) | $120 (1x D4s_v5) | $360 (3x D4s_v5) |
| API Management | $0 (Consumption) | $175 (Standard v2) |
| Cosmos DB | $25 (serverless) | $100-400 (autoscale) |
| Service Bus | $10 | $10-50 |
| Container Registry | $5 | $20 |
| Monitoring | $0 | $50-100 |
| **Total** | **~$220** | **~$900-1300** |

---

## Pattern 3: Serverless Event-Driven

### Architecture

```
    ┌──────────┐     ┌──────────┐     ┌──────────┐
    │ HTTP     │     │ Blob     │     │ Timer    │
    │ Trigger  │     │ Trigger  │     │ Trigger  │
    └────┬─────┘     └────┬─────┘     └────┬─────┘
         │                │                 │
         └────────┬───────┘─────────┬───────┘
                  │                 │
           ┌──────▼───────┐ ┌──────▼───────┐
           │    Azure     │ │    Azure     │
           │  Functions   │ │  Functions   │
           │  (handlers)  │ │  (workers)   │
           └──┬────┬──────┘ └──────┬───────┘
              │    │               │
    ┌─────────▼┐ ┌─▼──────────┐ ┌─▼──────────┐
    │ Event    │ │ Service    │ │ Cosmos DB  │
    │ Grid     │ │ Bus Queue  │ │ (data)     │
    │ (fanout) │ │ (reliable) │ │            │
    └──────────┘ └────────────┘ └────────────┘
```

### Services

| Service | Purpose | Configuration |
|---------|---------|---------------|
| Azure Functions | Event handlers, APIs | Consumption plan (dev), Premium (prod) |
| Event Grid | Event routing and fan-out | System + custom topics |
| Service Bus | Reliable messaging with DLQ | Basic or Standard, queues + topics |
| Cosmos DB | Low-latency data store | Serverless (dev), autoscale (prod) |
| Blob Storage | File processing triggers | Lifecycle policies |
| Application Insights | Function monitoring | Sampling at 5-10% for high volume |

### Durable Functions Patterns

Use Durable Functions for orchestration instead of building custom state machines:

| Pattern | Use Case | Example |
|---------|----------|---------|
| Function chaining | Sequential steps | Order: validate -> charge -> fulfill -> notify |
| Fan-out/fan-in | Parallel processing | Process all images in a batch, aggregate results |
| Async HTTP APIs | Long-running operations | Start job, poll for status, return result |
| Monitor | Periodic polling | Check external API until condition met |
| Human interaction | Approval workflows | Send approval email, wait for response with timeout |

### Cost Estimate

| Component | Dev | Production |
|-----------|-----|-----------|
| Functions (Consumption) | $0 (1M free) | $5-30 |
| Event Grid | $0 | $0-5 |
| Service Bus | $0 (Basic) | $10-30 |
| Cosmos DB | $0 (serverless free tier) | $25-150 |
| Blob Storage | $1 | $5-15 |
| Application Insights | $0 | $5-15 |
| **Total** | **~$1** | **~$50-245** |

---

## Pattern 4: Data Pipeline

### Architecture

```
    ┌──────────┐     ┌──────────┐
    │ IoT/Apps │     │ Batch    │
    │ (events) │     │ (files)  │
    └────┬─────┘     └────┬─────┘
         │                │
    ┌────▼─────┐     ┌────▼─────┐
    │ Event    │     │ Data     │
    │ Hubs     │     │ Factory  │
    └────┬─────┘     └────┬─────┘
         │                │
         └────────┬───────┘
                  │
         ┌────────▼────────┐
         │  Data Lake      │
         │  Storage Gen2   │
         │  (raw/curated)  │
         └────────┬────────┘
                  │
         ┌────────▼────────┐
         │  Synapse         │
         │  Analytics       │
         │  (SQL + Spark)   │
         └────────┬────────┘
                  │
         ┌────────▼────────┐
         │  Power BI       │
         │  (dashboards)   │
         └─────────────────┘
```

### Services

| Service | Purpose | Configuration |
|---------|---------|---------------|
| Event Hubs | Real-time event ingestion | Standard, 2-8 partitions |
| Data Factory | Batch ETL orchestration | Managed, 90+ connectors |
| Data Lake Storage Gen2 | Raw and curated data lake | HNS enabled, lifecycle policies |
| Synapse Analytics | SQL and Spark analytics | Serverless SQL pool (pay-per-query) |
| Azure Functions | Lightweight processing | Triggered by Event Hubs or Blob |
| Power BI | Business intelligence | Pro ($10/user/month) |

### Data Lake Organization

```
data-lake/
├── raw/                    # Landing zone — immutable source data
│   ├── source-system-a/
│   │   └── YYYY/MM/DD/     # Date-partitioned
│   └── source-system-b/
├── curated/                # Cleaned, validated, business-ready
│   ├── dimension/
│   └── fact/
├── sandbox/                # Ad-hoc exploration
└── archive/                # Cold storage (lifecycle policy target)
```

### Cost Estimate

| Component | Dev | Production |
|-----------|-----|-----------|
| Event Hubs (1 TU) | $22 | $44-176 |
| Data Factory | $0 (free tier) | $50-200 |
| Data Lake Storage | $5 | $20-80 |
| Synapse Serverless SQL | $5 | $50-300 |
| Azure Functions | $0 | $5-20 |
| Power BI Pro | $10/user | $10/user |
| **Total** | **~$42** | **~$180-800** |

---

## Pattern 5: Multi-Region Active-Active

### Architecture

```
                    ┌──────────────┐
                    │  Azure Front │
                    │  Door (Global│
                    │  LB + WAF)   │
                    └──┬────────┬──┘
                       │        │
            ┌──────────▼──┐ ┌──▼──────────┐
            │  Region 1   │ │  Region 2   │
            │  (East US)  │ │  (West EU)  │
            │             │ │             │
            │ App Service │ │ App Service │
            │ + SQL       │ │ + SQL       │
            │ + Redis     │ │ + Redis     │
            └──────┬──────┘ └──────┬──────┘
                   │               │
            ┌──────▼───────────────▼──────┐
            │      Cosmos DB              │
            │  (multi-region writes)      │
            │  Session consistency         │
            └─────────────────────────────┘
```

### Multi-Region Design Decisions

| Decision | Recommendation | Rationale |
|----------|---------------|-----------|
| Global load balancer | Front Door Premium | Built-in WAF, CDN, health probes, fastest failover |
| Database replication | Cosmos DB multi-write or SQL failover groups | Cosmos for global writes, SQL for relational needs |
| Session state | Azure Cache for Redis (per region) | Local sessions, avoid cross-region latency |
| Static content | Front Door CDN | Edge-cached, no origin required |
| DNS strategy | Front Door handles routing | No separate Traffic Manager needed |
| Failover | Automatic (Front Door health probes) | 10-30 second detection, automatic reroute |

### Azure SQL Failover Groups vs Cosmos DB Multi-Region

| Feature | SQL Failover Groups | Cosmos DB Multi-Region |
|---------|-------------------|----------------------|
| Replication | Async (RPO ~5s) | Sync or async (configurable) |
| Write region | Single primary | Multi-write capable |
| Failover | Automatic or manual (60s grace) | Automatic |
| Consistency | Strong (single writer) | 5 levels (session recommended) |
| Cost | 2x compute (active-passive) | Per-region RU/s charge |
| Best for | Relational data, transactions | Document data, global low-latency |

### Cost Impact

Multi-region typically costs 1.5-2x single region:
- Compute: 2x (running in both regions)
- Database: 1.5-2x (replication, multi-write)
- Networking: Additional cross-region data transfer (~$0.02-0.05/GB)
- Front Door Premium: ~$100-200/month

---

## Well-Architected Framework Alignment

Every architecture pattern should address all five pillars of the Azure Well-Architected Framework.

### Reliability

- Deploy across Availability Zones (zone-redundant App Service, AKS, SQL)
- Enable health probes at every layer
- Implement retry policies with exponential backoff (Polly for .NET, tenacity for Python)
- Define RPO/RTO and test disaster recovery quarterly
- Use Azure Chaos Studio for fault injection testing

### Security

- Entra ID for all human and service authentication
- Managed Identity for all Azure service-to-service communication
- Key Vault for secrets, certificates, and encryption keys — no secrets in code or config
- Private Endpoints for all PaaS services in production
- Microsoft Defender for Cloud for threat detection and compliance

### Cost Optimization

- Use serverless and consumption-based services where possible
- Auto-pause Azure SQL in dev/test (serverless tier)
- Spot VMs for fault-tolerant AKS node pools
- Reserved Instances for steady-state production workloads (1-year = 35% savings)
- Azure Advisor cost recommendations — review weekly
- Set budgets and alerts at subscription and resource group level

### Operational Excellence

- Bicep for all infrastructure (no manual portal deployments)
- GitOps for AKS (Flux or ArgoCD)
- Deployment slots or blue-green for zero-downtime deploys
- Centralized logging in Log Analytics with standardized KQL queries
- Azure DevOps or GitHub Actions for CI/CD with workload identity federation

### Performance Efficiency

- Application Insights for distributed tracing and performance profiling
- Azure Cache for Redis for session state and hot-path caching
- Front Door for edge caching and global acceleration
- Autoscale rules on compute (CPU, memory, HTTP queue length)
- Load testing with Azure Load Testing before production launch
