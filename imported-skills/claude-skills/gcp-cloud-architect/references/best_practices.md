# GCP Best Practices

Production-ready practices for naming, labels, IAM, networking, monitoring, and disaster recovery.

---

## Table of Contents

- [Naming Conventions](#naming-conventions)
- [Labels and Organization](#labels-and-organization)
- [IAM and Security](#iam-and-security)
- [Networking](#networking)
- [Monitoring and Logging](#monitoring-and-logging)
- [Cost Optimization](#cost-optimization)
- [Disaster Recovery](#disaster-recovery)
- [Common Pitfalls](#common-pitfalls)

---

## Naming Conventions

### Resource Naming Pattern

```
{environment}-{project}-{resource-type}-{purpose}

Examples:
  prod-myapp-gke-cluster
  dev-myapp-sql-primary
  staging-myapp-run-api
  prod-myapp-gcs-uploads
```

### Project Naming

```
{org}-{team}-{environment}

Examples:
  acme-platform-prod
  acme-platform-dev
  acme-data-prod
```

### Naming Rules

| Resource | Format | Max Length | Example |
|----------|--------|-----------|---------|
| Project ID | lowercase, hyphens | 30 chars | acme-platform-prod |
| GKE Cluster | lowercase, hyphens | 40 chars | prod-api-cluster |
| Cloud Run | lowercase, hyphens | 49 chars | prod-myapp-api |
| Cloud SQL | lowercase, hyphens | 84 chars | prod-myapp-sql-primary |
| GCS Bucket | lowercase, hyphens, dots | 63 chars | acme-prod-myapp-uploads |
| Service Account | lowercase, hyphens | 30 chars | myapp-run-sa |

---

## Labels and Organization

### Required Labels

Apply these labels to all resources:

```
labels:
  environment: "prod"          # dev, staging, prod
  team: "platform"             # team owning the resource
  app: "myapp"                 # application name
  cost-center: "eng-001"       # billing allocation
  managed-by: "terraform"      # terraform, gcloud, console
```

### Label-Based Cost Reporting

```bash
# Export billing data to BigQuery with labels
# Then query by label:
SELECT
  labels.value AS environment,
  SUM(cost) AS total_cost
FROM `billing_export.gcp_billing_export_v1_*`
CROSS JOIN UNNEST(labels) AS labels
WHERE labels.key = 'environment'
GROUP BY environment
ORDER BY total_cost DESC
```

### Organization Hierarchy

```
Organization
├── Folder: Production
│   ├── Project: platform-prod
│   ├── Project: data-prod
│   └── Project: ml-prod
├── Folder: Non-Production
│   ├── Project: platform-dev
│   ├── Project: platform-staging
│   └── Project: data-dev
└── Folder: Shared Services
    ├── Project: shared-networking
    ├── Project: shared-security
    └── Project: shared-monitoring
```

---

## IAM and Security

### Principle of Least Privilege

```bash
# BAD: Basic roles are too broad
gcloud projects add-iam-policy-binding my-project \
  --member="user:dev@example.com" \
  --role="roles/editor"

# GOOD: Use predefined roles
gcloud projects add-iam-policy-binding my-project \
  --member="user:dev@example.com" \
  --role="roles/run.developer"
```

### Service Account Best Practices

```bash
# 1. Create dedicated SA per workload
gcloud iam service-accounts create myapp-api-sa \
  --display-name="MyApp API Service Account"

# 2. Grant only required roles
gcloud projects add-iam-policy-binding my-project \
  --member="serviceAccount:myapp-api-sa@my-project.iam.gserviceaccount.com" \
  --role="roles/datastore.user"

# 3. Use Workload Identity for GKE (no key files)
gcloud iam service-accounts add-iam-policy-binding \
  myapp-api-sa@my-project.iam.gserviceaccount.com \
  --role="roles/iam.workloadIdentityUser" \
  --member="serviceAccount:my-project.svc.id.goog[default/myapp-api-ksa]"

# 4. NEVER download SA key files in production
# Instead, use attached service accounts or impersonation
```

### VPC Service Controls

```bash
# Create a service perimeter to restrict data exfiltration
gcloud access-context-manager perimeters create my-perimeter \
  --title="Production Data Perimeter" \
  --resources="projects/123456" \
  --restricted-services="bigquery.googleapis.com,storage.googleapis.com" \
  --policy=$POLICY_ID
```

### Organization Policies

```bash
# Restrict external IPs on VMs
gcloud resource-manager org-policies set-policy \
  --project=my-project policy.yaml

# policy.yaml
constraint: compute.vmExternalIpAccess
listPolicy:
  allValues: DENY

# Restrict public Cloud Storage
constraint: storage.publicAccessPrevention
booleanPolicy:
  enforced: true
```

### Encryption

| Layer | Service | Default |
|-------|---------|---------|
| At rest | Google-managed keys | Always enabled |
| At rest | CMEK (Cloud KMS) | Optional, recommended |
| In transit | TLS 1.3 | Always enabled |
| Application | Cloud KMS | Encrypt sensitive fields |

```bash
# Create CMEK key for Cloud SQL
gcloud kms keys create myapp-sql-key \
  --keyring=myapp-keyring \
  --location=us-central1 \
  --purpose=encryption

# Use CMEK with Cloud SQL
gcloud sql instances create myapp-db \
  --disk-encryption-key=projects/my-project/locations/us-central1/keyRings/myapp-keyring/cryptoKeys/myapp-sql-key
```

---

## Networking

### VPC Design

```bash
# Create custom VPC (avoid default network)
gcloud compute networks create myapp-vpc \
  --subnet-mode=custom

# Create subnets with secondary ranges for GKE
gcloud compute networks subnets create myapp-subnet \
  --network=myapp-vpc \
  --region=us-central1 \
  --range=10.0.0.0/20 \
  --secondary-range pods=10.4.0.0/14,services=10.8.0.0/20 \
  --enable-private-google-access
```

### Shared VPC

Use Shared VPC for multi-project environments:

```
Host Project (shared-networking)
├── VPC: shared-vpc
│   ├── Subnet: prod-us-central1 → Service Project: platform-prod
│   ├── Subnet: prod-europe-west1 → Service Project: platform-prod
│   └── Subnet: dev-us-central1 → Service Project: platform-dev
```

### Firewall Rules

```bash
# Allow internal traffic
gcloud compute firewall-rules create allow-internal \
  --network=myapp-vpc \
  --allow=tcp,udp,icmp \
  --source-ranges=10.0.0.0/8

# Allow health checks from Google load balancers
gcloud compute firewall-rules create allow-health-checks \
  --network=myapp-vpc \
  --allow=tcp:8080 \
  --source-ranges=35.191.0.0/16,130.211.0.0/22 \
  --target-tags=allow-health-check

# Deny all other ingress (implicit, but be explicit)
gcloud compute firewall-rules create deny-all-ingress \
  --network=myapp-vpc \
  --action=DENY \
  --rules=all \
  --direction=INGRESS \
  --priority=65534
```

### Private Google Access

Always enable Private Google Access to reach GCP APIs without public IPs:

```bash
gcloud compute networks subnets update myapp-subnet \
  --region=us-central1 \
  --enable-private-google-access
```

---

## Monitoring and Logging

### Cloud Monitoring Setup

```bash
# Create uptime check
gcloud monitoring uptime create \
  --display-name="API Health Check" \
  --resource-type=cloud-run-revision \
  --resource-labels="service_name=myapp-api,location=us-central1" \
  --check-request-path="/health" \
  --period=60s

# Create alerting policy
gcloud alpha monitoring policies create \
  --display-name="High Error Rate" \
  --condition-display-name="Cloud Run 5xx > 1%" \
  --condition-filter='resource.type="cloud_run_revision" AND metric.type="run.googleapis.com/request_count" AND metric.labels.response_code_class="5xx"' \
  --condition-threshold-value=1 \
  --notification-channels="projects/my-project/notificationChannels/12345"
```

### Key Metrics to Monitor

| Service | Metric | Alert Threshold |
|---------|--------|-----------------|
| Cloud Run | request_latencies (p99) | >2s |
| Cloud Run | request_count (5xx) | >1% of total |
| Cloud SQL | cpu/utilization | >80% |
| Cloud SQL | disk/utilization | >85% |
| GKE | container/cpu/utilization | >80% |
| GKE | node/cpu/allocatable_utilization | >85% |
| Pub/Sub | subscription/oldest_unacked_message_age | >300s |
| BigQuery | query/execution_time | >60s |

### Log-Based Metrics

```bash
# Create a metric for application errors
gcloud logging metrics create app-errors \
  --description="Application error count" \
  --log-filter='resource.type="cloud_run_revision" AND severity>=ERROR'

# Create log sink to BigQuery for analysis
gcloud logging sinks create audit-logs-bq \
  bigquery.googleapis.com/projects/my-project/datasets/audit_logs \
  --log-filter='logName="projects/my-project/logs/cloudaudit.googleapis.com%2Factivity"'
```

### Log Exclusion (Cost Reduction)

```bash
# Exclude verbose debug logs to save on Cloud Logging costs
gcloud logging sinks create _Default \
  --log-filter='NOT (severity="DEBUG" OR severity="DEFAULT")' \
  --description="Exclude debug-level logs"

# Or create exclusion filters
gcloud logging exclusions create exclude-debug \
  --log-filter='severity="DEBUG"' \
  --description="Exclude debug logs to reduce costs"
```

---

## Cost Optimization

### Committed Use Discounts

| Term | Compute Discount | Memory Discount |
|------|-----------------|-----------------|
| 1 year | 37% | 37% |
| 3 years | 55% | 55% |

```bash
# Check recommendations
gcloud recommender recommendations list \
  --project=my-project \
  --location=us-central1 \
  --recommender=google.compute.commitment.UsageCommitmentRecommender
```

### Sustained Use Discounts

Automatic discounts for resources running >25% of the month:

| Usage | Discount |
|-------|----------|
| 25-50% | 20% |
| 50-75% | 40% |
| 75-100% | 60% |

### BigQuery Cost Control

```sql
-- Use partitioning to limit data scanned
CREATE TABLE my_dataset.events
PARTITION BY DATE(timestamp)
CLUSTER BY event_type
AS SELECT * FROM raw_events;

-- Estimate query cost before running
-- Use --dry_run flag
bq query --dry_run --use_legacy_sql=false \
  'SELECT * FROM my_dataset.events WHERE DATE(timestamp) = "2026-01-01"'
```

### Cloud Storage Optimization

```bash
# Enable Autoclass for automatic class management
gsutil mb -l us-central1 --autoclass gs://my-bucket/

# Set lifecycle policy
gsutil lifecycle set lifecycle.json gs://my-bucket/
```

---

## Disaster Recovery

### RPO/RTO Targets

| Tier | RPO | RTO | Strategy |
|------|-----|-----|----------|
| Tier 1 (Critical) | 0 | <1 hour | Multi-region active-active |
| Tier 2 (Important) | <1 hour | <4 hours | Regional HA + cross-region backup |
| Tier 3 (Standard) | <24 hours | <24 hours | Automated backups + restore |

### Backup Strategy

```bash
# Cloud SQL automated backups
gcloud sql instances patch myapp-db \
  --backup-start-time=02:00 \
  --enable-point-in-time-recovery

# Firestore scheduled exports
gcloud firestore export gs://myapp-backups/firestore/$(date +%Y%m%d)

# GKE cluster backup with Backup for GKE
gcloud beta container backup-restore backup-plans create myapp-plan \
  --project=my-project \
  --location=us-central1 \
  --cluster=projects/my-project/locations/us-central1/clusters/myapp-cluster \
  --all-namespaces \
  --cron-schedule="0 2 * * *"
```

### Multi-Region Failover

```bash
# Cloud SQL cross-region replica for DR
gcloud sql instances create myapp-db-replica \
  --master-instance-name=myapp-db \
  --region=us-east1

# Promote replica during failover
gcloud sql instances promote-replica myapp-db-replica
```

---

## Common Pitfalls

### Technical Debt

| Pitfall | Solution |
|---------|----------|
| Using default VPC | Always create custom VPCs |
| Not enabling audit logs | Enable Cloud Audit Logs from day one |
| Single-region deployment | Plan for multi-zone at minimum |
| No IaC | Use Terraform from the start |

### Security Mistakes

| Mistake | Prevention |
|---------|------------|
| SA key files in code | Use Workload Identity, attached SAs |
| Public GCS buckets | Enable org policy for public access prevention |
| Basic roles (Owner/Editor) | Use predefined or custom roles |
| No encryption key management | Use CMEK for sensitive data |
| Default service account | Create dedicated SAs per workload |

### Performance Issues

| Issue | Solution |
|-------|----------|
| Cold starts on Cloud Run | Set min-instances=1 for latency-critical services |
| Slow BigQuery queries | Partition tables, use clustering, avoid SELECT * |
| GKE pod scheduling delays | Use PodDisruptionBudget, pre-provision with Autopilot |
| Firestore hotspots | Distribute writes across document IDs evenly |

### Cost Surprises

| Surprise | Prevention |
|----------|------------|
| Undeleted resources | Label everything, review weekly |
| Egress costs | Keep traffic in same region, use Private Google Access |
| Cloud NAT charges | Use Private Google Access for GCP service traffic |
| Log ingestion costs | Set exclusion filters for debug/verbose logs |
| BigQuery full scans | Always use partitioning and clustering |
| Idle GKE clusters | Delete dev clusters nightly, use Autopilot |
