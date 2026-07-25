# Azure Best Practices

Production-ready practices for naming, tagging, security, networking, monitoring, and disaster recovery on Azure.

---

## Table of Contents

- [Naming Conventions](#naming-conventions)
- [Tagging Strategy](#tagging-strategy)
- [RBAC and Least Privilege](#rbac-and-least-privilege)
- [Network Security](#network-security)
- [Monitoring and Alerting](#monitoring-and-alerting)
- [Disaster Recovery](#disaster-recovery)
- [Common Pitfalls](#common-pitfalls)

---

## Naming Conventions

Follow the Azure Cloud Adoption Framework (CAF) naming convention for consistency and automation.

### Format

```
<resource-type>-<workload>-<environment>-<region>-<instance>
```

### Examples

| Resource | Naming Pattern | Example |
|----------|---------------|---------|
| Resource Group | rg-\<workload\>-\<env\> | rg-myapp-prod |
| App Service | app-\<workload\>-\<env\> | app-myapp-prod |
| App Service Plan | plan-\<workload\>-\<env\> | plan-myapp-prod |
| Azure SQL Server | sql-\<workload\>-\<env\> | sql-myapp-prod |
| Azure SQL Database | sqldb-\<workload\>-\<env\> | sqldb-myapp-prod |
| Storage Account | st\<workload\>\<env\> (no hyphens) | stmyappprod |
| Key Vault | kv-\<workload\>-\<env\> | kv-myapp-prod |
| AKS Cluster | aks-\<workload\>-\<env\> | aks-myapp-prod |
| Container Registry | cr\<workload\>\<env\> (no hyphens) | crmyappprod |
| Virtual Network | vnet-\<workload\>-\<env\> | vnet-myapp-prod |
| Subnet | snet-\<purpose\> | snet-app, snet-data |
| NSG | nsg-\<subnet-name\> | nsg-snet-app |
| Public IP | pip-\<resource\>-\<env\> | pip-agw-prod |
| Cosmos DB | cosmos-\<workload\>-\<env\> | cosmos-myapp-prod |
| Service Bus | sb-\<workload\>-\<env\> | sb-myapp-prod |
| Event Hubs | evh-\<workload\>-\<env\> | evh-myapp-prod |
| Log Analytics | log-\<workload\>-\<env\> | log-myapp-prod |
| Application Insights | ai-\<workload\>-\<env\> | ai-myapp-prod |

### Rules

- Lowercase only (some resources require it — be consistent everywhere)
- Hyphens as separators (except where disallowed: storage accounts, container registries)
- No longer than the resource type max length (e.g., storage accounts max 24 characters)
- Environment abbreviations: `dev`, `stg`, `prod`
- Region abbreviations: `eus` (East US), `weu` (West Europe), `sea` (Southeast Asia)

---

## Tagging Strategy

Tags enable cost allocation, ownership tracking, and automation. Apply to every resource.

### Required Tags

| Tag Key | Purpose | Example Values |
|---------|---------|---------------|
| environment | Cost splitting, policy targeting | dev, staging, production |
| app-name | Workload identification | myapp, data-pipeline |
| owner | Team or individual responsible | platform-team, jane.doe@company.com |
| cost-center | Finance allocation | CC-1234, engineering |

### Recommended Tags

| Tag Key | Purpose | Example Values |
|---------|---------|---------------|
| created-by | IaC or manual tracking | bicep, terraform, portal |
| data-classification | Security posture | public, internal, confidential |
| compliance | Regulatory requirements | hipaa, gdpr, sox |
| auto-shutdown | Dev/test cost savings | true, false |

### Enforcement

Use Azure Policy to enforce tagging:

```json
{
  "if": {
    "allOf": [
      { "field": "tags['environment']", "exists": "false" },
      { "field": "type", "notEquals": "Microsoft.Resources/subscriptions/resourceGroups" }
    ]
  },
  "then": { "effect": "deny" }
}
```

---

## RBAC and Least Privilege

### Principles

1. **Use built-in roles** before creating custom roles
2. **Assign roles to groups**, not individual users
3. **Scope to the narrowest level** — resource group or resource, not subscription
4. **Use Managed Identity** for service-to-service — never store credentials
5. **Enable Entra ID PIM** (Privileged Identity Management) for just-in-time admin access

### Common Role Assignments

| Persona | Scope | Role |
|---------|-------|------|
| Developer | Resource Group (dev) | Contributor |
| Developer | Resource Group (prod) | Reader |
| CI/CD pipeline | Resource Group | Contributor (via workload identity) |
| App Service | Key Vault | Key Vault Secrets User |
| App Service | Azure SQL | SQL DB Contributor (or Entra auth) |
| AKS pod | Cosmos DB | Cosmos DB Built-in Data Contributor |
| Security team | Subscription | Security Reader |
| Platform team | Subscription | Owner (with PIM) |

### Workload Identity Federation

For CI/CD pipelines (GitHub Actions, Azure DevOps), use workload identity federation instead of service principal secrets:

```bash
# Create federated credential (GitHub Actions example)
az ad app federated-credential create \
  --id <app-object-id> \
  --parameters '{
    "name": "github-main",
    "issuer": "https://token.actions.githubusercontent.com",
    "subject": "repo:org/repo:ref:refs/heads/main",
    "audiences": ["api://AzureADTokenExchange"]
  }'
```

---

## Network Security

### Defense in Depth

| Layer | Control | Implementation |
|-------|---------|---------------|
| Edge | DDoS + WAF | Azure DDoS Protection + Front Door WAF |
| Perimeter | Firewall | Azure Firewall or NVA for hub VNet |
| Network | Segmentation | VNet + subnets + NSGs |
| Application | Access control | Private Endpoints + Managed Identity |
| Data | Encryption | TLS 1.2+ in transit, CMK at rest |

### Private Endpoints

Every PaaS service in production must use Private Endpoints:

| Service | Private Endpoint Support | Private DNS Zone |
|---------|------------------------|------------------|
| Azure SQL | Yes | privatelink.database.windows.net |
| Cosmos DB | Yes | privatelink.documents.azure.com |
| Key Vault | Yes | privatelink.vaultcore.azure.net |
| Storage (Blob) | Yes | privatelink.blob.core.windows.net |
| Container Registry | Yes | privatelink.azurecr.io |
| Service Bus | Yes | privatelink.servicebus.windows.net |
| App Service | VNet Integration (outbound) + Private Endpoint (inbound) | privatelink.azurewebsites.net |

### NSG Rules Baseline

Every subnet should have an NSG. Start with deny-all inbound, then open only what is needed:

```
Priority  Direction  Action  Source          Destination     Port
100       Inbound    Allow   Front Door      App Subnet      443
200       Inbound    Allow   App Subnet      Data Subnet     1433,5432
300       Inbound    Allow   VNet            VNet            Any (internal)
4096      Inbound    Deny    Any             Any             Any
```

### Application Gateway + WAF

For single-region web apps without Front Door:

- Application Gateway v2 with WAF enabled
- OWASP 3.2 rule set + custom rules
- Rate limiting per client IP
- Bot protection (managed rule set)
- SSL termination with Key Vault certificate

---

## Monitoring and Alerting

### Monitoring Stack

```
Application Insights (APM + distributed tracing)
        │
        ▼
Log Analytics Workspace (central log store)
        │
        ▼
Azure Monitor Alerts (metric + log-based)
        │
        ▼
Action Groups (email, Teams, PagerDuty, webhook)
```

### Essential Alerts

| Alert | Condition | Severity |
|-------|-----------|----------|
| App Service HTTP 5xx | > 10 in 5 minutes | Critical (Sev 1) |
| App Service response time | P95 > 2 seconds | Warning (Sev 2) |
| Azure SQL DTU/CPU | > 80% for 10 minutes | Warning (Sev 2) |
| Azure SQL deadlocks | > 0 | Warning (Sev 2) |
| Cosmos DB throttled requests | 429 count > 10 in 5 min | Warning (Sev 2) |
| AKS node CPU | > 80% for 10 minutes | Warning (Sev 2) |
| AKS pod restart count | > 5 in 10 minutes | Critical (Sev 1) |
| Key Vault access denied | > 0 | Critical (Sev 1) |
| Budget threshold | 80% of monthly budget | Warning (Sev 3) |
| Budget threshold | 100% of monthly budget | Critical (Sev 1) |

### KQL Queries for Troubleshooting

**App Service slow requests:**
```kql
requests
| where duration > 2000
| summarize count(), avg(duration), percentile(duration, 95) by name
| order by count_ desc
| take 10
```

**Failed dependencies (SQL, HTTP, etc.):**
```kql
dependencies
| where success == false
| summarize count() by type, target, resultCode
| order by count_ desc
```

**AKS pod errors:**
```kql
KubePodInventory
| where PodStatus != "Running" and PodStatus != "Succeeded"
| summarize count() by PodStatus, Namespace, Name
| order by count_ desc
```

### Application Insights Configuration

- Enable **distributed tracing** with W3C trace context
- Set **sampling** to 5-10% for high-volume production (100% for dev)
- Enable **profiler** for .NET applications
- Enable **snapshot debugger** for exception analysis
- Configure **availability tests** (URL ping every 5 minutes from multiple regions)

---

## Disaster Recovery

### RPO/RTO Mapping

| Tier | RPO | RTO | Strategy | Cost |
|------|-----|-----|----------|------|
| Tier 1 (critical) | < 5 minutes | < 1 hour | Active-active multi-region | 2x |
| Tier 2 (important) | < 1 hour | < 4 hours | Warm standby | 1.3x |
| Tier 3 (standard) | < 24 hours | < 24 hours | Backup and restore | 1.1x |
| Tier 4 (non-critical) | < 72 hours | < 72 hours | Rebuild from IaC | 1x |

### Backup Strategy

| Service | Backup Method | Retention |
|---------|--------------|-----------|
| Azure SQL | Automated backups | 7 days (short-term), 10 years (long-term) |
| Cosmos DB | Continuous backup + point-in-time restore | 7-30 days |
| Blob Storage | Soft delete + versioning + geo-redundant | 30 days soft delete |
| AKS | Velero backup to Blob Storage | 7 days |
| Key Vault | Soft delete + purge protection | 90 days |
| App Service | Manual or automated (Backup and Restore feature) | Custom |

### Storage Redundancy

| Redundancy | Regions | Durability | Use Case |
|-----------|---------|-----------|----------|
| LRS | 1 (3 copies) | 11 nines | Dev/test, easily recreatable data |
| ZRS | 1 (3 AZs) | 12 nines | Production, zone failure protection |
| GRS | 2 (6 copies) | 16 nines | Business-critical, regional failure protection |
| GZRS | 2 (3 AZs + secondary) | 16 nines | Most critical data, best protection |

**Default to ZRS for production.** Use GRS/GZRS only when cross-region DR is required.

### DR Testing Checklist

- [ ] Verify automated backups are running and retention is correct
- [ ] Test point-in-time restore for databases (monthly)
- [ ] Test regional failover for SQL failover groups (quarterly)
- [ ] Validate IaC can recreate full environment from scratch
- [ ] Test Front Door failover by taking down primary region health endpoint
- [ ] Document and test runbook for manual failover steps
- [ ] Measure actual RTO vs target during DR drill

---

## Common Pitfalls

### Cost Pitfalls

| Pitfall | Impact | Prevention |
|---------|--------|-----------|
| No budget alerts | Unexpected bills | Set alerts at 50%, 80%, 100% on day one |
| Premium tier in dev/test | 3-5x overspend | Use Basic/Free tiers, auto-shutdown VMs |
| Orphaned resources | Silent monthly charges | Tag everything, review Cost Management weekly |
| Ignoring Reserved Instances | 35-55% overpay on steady workloads | Review Azure Advisor quarterly |
| Over-provisioned Cosmos DB RU/s | Paying for unused throughput | Use autoscale or serverless |

### Security Pitfalls

| Pitfall | Impact | Prevention |
|---------|--------|-----------|
| Secrets in App Settings | Leaked credentials | Use Key Vault references |
| Public PaaS endpoints | Exposed attack surface | Private Endpoints + VNet integration |
| Contributor role on subscription | Overprivileged access | Scope to resource group, use PIM |
| No diagnostic settings | Blind to attacks | Enable on every resource from day one |
| SQL password authentication | Weak identity model | Entra-only auth, Managed Identity |

### Operational Pitfalls

| Pitfall | Impact | Prevention |
|---------|--------|-----------|
| Manual portal deployments | Drift, no audit trail | Bicep for everything, block portal changes via Policy |
| No health checks configured | Silent failures | /health endpoint, Front Door probes, App Service checks |
| Single region deployment | Single point of failure | At minimum, use Availability Zones |
| No tagging strategy | Cannot track costs/ownership | Enforce via Azure Policy from day one |
| Ignoring Azure Advisor | Missed optimizations | Weekly review, enable email digest |
