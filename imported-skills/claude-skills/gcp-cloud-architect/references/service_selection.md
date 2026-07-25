# GCP Service Selection Guide

Quick reference for choosing the right GCP service based on requirements.

---

## Table of Contents

- [Compute Services](#compute-services)
- [Database Services](#database-services)
- [Storage Services](#storage-services)
- [Messaging and Events](#messaging-and-events)
- [API and Integration](#api-and-integration)
- [Networking](#networking)
- [Security and Identity](#security-and-identity)

---

## Compute Services

### Decision Matrix

| Requirement | Recommended Service |
|-------------|---------------------|
| HTTP-triggered containers, auto-scaling | Cloud Run |
| Event-driven, short tasks (<9 min) | Cloud Functions (2nd gen) |
| Kubernetes workloads, microservices | GKE Autopilot |
| Custom VMs, GPU/TPU | Compute Engine |
| Batch processing, HPC | Batch |
| Kubernetes with full control | GKE Standard |

### Cloud Run

**Best for:** Containerized HTTP services, APIs, web backends

```
Limits:
- vCPU: 1-8 per instance
- Memory: 128 MiB - 32 GiB
- Request timeout: 3600 seconds
- Concurrency: 1-1000 per instance
- Min instances: 0 (scale-to-zero)
- Max instances: 1000

Pricing: Per vCPU-second + GiB-second (free tier: 2M requests/month)
```

**Use when:**
- Containerized apps with HTTP endpoints
- Variable/unpredictable traffic
- Want scale-to-zero capability
- No Kubernetes expertise needed

**Avoid when:**
- Non-HTTP workloads (use Cloud Functions or GKE)
- Need GPU/TPU (use Compute Engine or GKE)
- Require persistent local storage

### Cloud Functions (2nd gen)

**Best for:** Event-driven functions, lightweight triggers, webhooks

```
Limits:
- Execution: 9 minutes max (2nd gen), 9 minutes (1st gen)
- Memory: 128 MB - 32 GB
- Concurrency: Up to 1000 per instance (2nd gen)
- Runtimes: Node.js, Python, Go, Java, .NET, Ruby, PHP

Pricing: $0.40 per million invocations + compute time
```

**Use when:**
- Event-driven processing (Pub/Sub, Cloud Storage, Firestore)
- Lightweight API endpoints
- Scheduled tasks (Cloud Scheduler triggers)
- Minimal infrastructure management

**Avoid when:**
- Long-running processes (>9 min)
- Complex multi-container apps
- Need fine-grained scaling control

### GKE Autopilot

**Best for:** Kubernetes workloads with managed node provisioning

```
Limits:
- Pod resources: 0.25-112 vCPU, 0.5-896 GiB memory
- GPU support: NVIDIA T4, L4, A100, H100
- Management fee: $0.10/hour per cluster ($74.40/month)

Pricing: Per pod vCPU-hour + GiB-hour (no node management)
```

**Use when:**
- Team has Kubernetes expertise
- Need pod-level resource control
- Multi-container services
- GPU workloads

### Compute Engine

**Best for:** Custom configurations, specialized hardware

```
Machine Types:
- General: e2, n2, n2d, c3
- Compute: c2, c2d
- Memory: m1, m2, m3
- Accelerator: a2 (GPU), a3 (GPU)
- Storage: z3

Pricing Options:
- On-demand, Spot (60-91% discount), Committed Use (37-55% discount)
```

**Use when:**
- Need GPU/TPU
- Windows workloads
- Specific hardware requirements
- Lift-and-shift migrations

---

## Database Services

### Decision Matrix

| Data Type | Query Pattern | Scale | Recommended |
|-----------|--------------|-------|-------------|
| Key-value, document | Simple lookups, real-time | Any | Firestore |
| Wide-column | High-throughput reads/writes | >1TB | Cloud Bigtable |
| Relational | Complex joins, ACID | Variable | Cloud SQL |
| Relational, global | Strong consistency, global | Large | Cloud Spanner |
| Time-series | Time-based queries | Any | Bigtable or BigQuery |
| Analytics, warehouse | SQL analytics | Petabytes | BigQuery |

### Firestore

**Best for:** Document data, mobile/web apps, real-time sync

```
Limits:
- Document size: 1 MiB max
- Field depth: 20 nested levels
- Write rate: 10,000 writes/sec per database
- Indexes: Automatic single-field, manual composite

Pricing:
- Reads: $0.036 per 100K reads
- Writes: $0.108 per 100K writes
- Storage: $0.108 per GiB/month
- Free tier: 50K reads, 20K writes, 1 GiB storage per day
```

**Use when:**
- Mobile/web apps needing offline sync
- Real-time data updates
- Flexible schema
- Serverless architecture

**Avoid when:**
- Complex SQL queries with joins
- Heavy analytics workloads
- Data >1 MiB per document

### Cloud SQL

**Best for:** Relational data with familiar SQL

| Engine | Version | Max Storage | Max Connections |
|--------|---------|-------------|-----------------|
| PostgreSQL | 15 | 64 TB | Instance-dependent |
| MySQL | 8.0 | 64 TB | Instance-dependent |
| SQL Server | 2022 | 64 TB | Instance-dependent |

```
Pricing:
- Machine type + storage + networking
- HA: 2x cost (regional instance)
- Read replicas: Per-replica pricing
```

**Use when:**
- Relational data with complex queries
- Existing SQL expertise
- Need ACID transactions
- Migration from on-premises databases

### Cloud Spanner

**Best for:** Globally distributed relational data

```
Limits:
- Storage: Unlimited
- Nodes: 1-100+ per instance
- Consistency: Strong global consistency

Pricing:
- Regional: $0.90/node-hour (~$657/month per node)
- Multi-region: $2.70/node-hour (~$1,971/month per node)
- Storage: $0.30/GiB/month
```

**Use when:**
- Global applications needing strong consistency
- Relational data at massive scale
- 99.999% availability requirement
- Horizontal scaling with SQL

### BigQuery

**Best for:** Analytics, data warehouse, SQL on massive datasets

```
Limits:
- Query: 6-hour timeout
- Concurrent queries: 100 default
- Streaming inserts: 100K rows/sec per table

Pricing:
- On-demand: $6.25 per TB queried (first 1 TB free/month)
- Editions: Autoscale slots starting at $0.04/slot-hour
- Storage: $0.02/GiB (active), $0.01/GiB (long-term)
```

### Firestore vs Cloud SQL vs Spanner

| Factor | Firestore | Cloud SQL | Cloud Spanner |
|--------|-----------|-----------|---------------|
| Query flexibility | Document-based | Full SQL | Full SQL |
| Scaling | Automatic | Vertical + read replicas | Horizontal |
| Consistency | Strong (single region) | ACID | Strong (global) |
| Cost model | Per-operation | Per-hour | Per-node-hour |
| Operational | Zero management | Managed (some ops) | Managed |
| Best for | Mobile/web apps | Traditional apps | Global scale |

---

## Storage Services

### Cloud Storage Classes

| Class | Access Pattern | Min Duration | Cost (GiB/mo) |
|-------|---------------|--------------|----------------|
| Standard | Frequent | None | $0.020 |
| Nearline | Monthly access | 30 days | $0.010 |
| Coldline | Quarterly access | 90 days | $0.004 |
| Archive | Annual access | 365 days | $0.0012 |

### Lifecycle Policy Example

```json
{
  "lifecycle": {
    "rule": [
      {
        "action": { "type": "SetStorageClass", "storageClass": "NEARLINE" },
        "condition": { "age": 30, "matchesStorageClass": ["STANDARD"] }
      },
      {
        "action": { "type": "SetStorageClass", "storageClass": "COLDLINE" },
        "condition": { "age": 90, "matchesStorageClass": ["NEARLINE"] }
      },
      {
        "action": { "type": "SetStorageClass", "storageClass": "ARCHIVE" },
        "condition": { "age": 365, "matchesStorageClass": ["COLDLINE"] }
      },
      {
        "action": { "type": "Delete" },
        "condition": { "age": 2555 }
      }
    ]
  }
}
```

### Autoclass

Automatically transitions objects between storage classes based on access patterns. Recommended for mixed or unknown access patterns.

```bash
gsutil mb -l us-central1 --autoclass gs://my-bucket/
```

### Block and File Storage

| Service | Use Case | Access |
|---------|----------|--------|
| Persistent Disk | GCE/GKE block storage | Single instance (RW) or multi (RO) |
| Filestore | NFS shared file system | Multiple instances |
| Parallelstore | HPC parallel file system | High throughput |
| Cloud Storage FUSE | Mount GCS as filesystem | Any compute |

---

## Messaging and Events

### Decision Matrix

| Pattern | Service | Use Case |
|---------|---------|----------|
| Pub/sub messaging | Pub/Sub | Event streaming, microservice decoupling |
| Task queue | Cloud Tasks | Asynchronous task execution with retries |
| Workflow orchestration | Workflows | Multi-step service orchestration |
| Batch orchestration | Cloud Composer | Complex DAG-based pipelines (Airflow) |
| Event triggers | Eventarc | Route events to Cloud Run, GKE, Workflows |

### Pub/Sub

**Best for:** Event-driven architectures, stream processing

```
Limits:
- Message size: 10 MB max
- Throughput: Unlimited (auto-scaling)
- Retention: 7 days default (up to 31 days)
- Ordering: Per ordering key

Pricing: $40/TiB for message delivery
```

```python
# Pub/Sub publisher example
from google.cloud import pubsub_v1
import json

publisher = pubsub_v1.PublisherClient()
topic_path = publisher.topic_path('my-project', 'events')

def publish_event(event_type, payload):
    data = json.dumps(payload).encode('utf-8')
    future = publisher.publish(
        topic_path,
        data,
        event_type=event_type
    )
    return future.result()
```

### Cloud Tasks

**Best for:** Asynchronous task execution with delivery guarantees

```
Features:
- Configurable retry policies
- Rate limiting
- Scheduled delivery
- HTTP and App Engine targets

Pricing: $0.40 per million operations
```

### Eventarc

**Best for:** Routing cloud events to services

```python
# Eventarc routes events from 130+ Google Cloud sources
# to Cloud Run, GKE, or Workflows

# Example: Trigger Cloud Run on Cloud Storage upload
# gcloud eventarc triggers create my-trigger \
#   --destination-run-service=my-service \
#   --event-filters="type=google.cloud.storage.object.v1.finalized" \
#   --event-filters="bucket=my-bucket"
```

---

## API and Integration

### API Gateway vs Cloud Endpoints vs Cloud Run

| Factor | API Gateway | Cloud Endpoints | Cloud Run (direct) |
|--------|-------------|-----------------|---------------------|
| Protocol | REST, gRPC | REST, gRPC | Any HTTP |
| Auth | API keys, JWT, Firebase | API keys, JWT | IAM, custom |
| Rate limiting | Built-in | Built-in | Manual |
| Cost | Per-call pricing | Per-call pricing | Per-request |
| Best for | External APIs | Internal APIs | Simple services |

### Cloud Endpoints Configuration

```yaml
# openapi.yaml
swagger: "2.0"
info:
  title: "My API"
  version: "1.0.0"
host: "my-api-xyz.apigateway.my-project.cloud.goog"
schemes:
  - "https"
paths:
  /users:
    get:
      summary: "List users"
      operationId: "listUsers"
      x-google-backend:
        address: "https://my-app-api-xyz.a.run.app"
      security:
        - api_key: []
securityDefinitions:
  api_key:
    type: "apiKey"
    name: "key"
    in: "query"
```

### Workflows

**Best for:** Orchestrating multi-service processes

```yaml
# workflow.yaml
main:
  steps:
    - processOrder:
        call: http.post
        args:
          url: https://orders-service.run.app/process
          body:
            orderId: ${args.orderId}
        result: orderResult

    - checkInventory:
        switch:
          - condition: ${orderResult.body.inStock}
            next: shipOrder
        next: backOrder

    - shipOrder:
        call: http.post
        args:
          url: https://shipping-service.run.app/ship
          body:
            orderId: ${args.orderId}
        result: shipResult

    - backOrder:
        call: http.post
        args:
          url: https://inventory-service.run.app/backorder
          body:
            orderId: ${args.orderId}
```

---

## Networking

### VPC Components

| Component | Purpose |
|-----------|---------|
| VPC | Isolated network (global resource) |
| Subnet | Regional network segment |
| Cloud NAT | Outbound internet for private instances |
| Cloud Router | Dynamic routing (BGP) |
| Private Google Access | Access GCP APIs without public IP |
| VPC Peering | Connect two VPC networks |
| Shared VPC | Share VPC across projects |

### VPC Design Pattern

```
VPC: 10.0.0.0/16 (global)

Subnet us-central1:
  10.0.0.0/20 (primary)
  10.4.0.0/14 (pods - secondary)
  10.8.0.0/20 (services - secondary)
  - GKE cluster, Cloud Run (VPC connector)

Subnet us-east1:
  10.0.16.0/20 (primary)
  - Cloud SQL (private IP), Memorystore

Subnet europe-west1:
  10.0.32.0/20 (primary)
  - DR / multi-region workloads
```

### Private Google Access

```bash
# Enable Private Google Access on a subnet
gcloud compute networks subnets update my-subnet \
  --region=us-central1 \
  --enable-private-google-access
```

---

## Security and Identity

### IAM Best Practices

```bash
# Prefer predefined roles over basic roles
# BAD: roles/editor (too broad)
# GOOD: roles/run.invoker (specific)

# Grant role to service account
gcloud projects add-iam-policy-binding my-project \
  --member="serviceAccount:my-sa@my-project.iam.gserviceaccount.com" \
  --role="roles/datastore.user" \
  --condition='expression=resource.name.startsWith("projects/my-project/databases/(default)/documents/users"),title=firestore-users-only'
```

### Service Account Best Practices

| Practice | Description |
|----------|-------------|
| One SA per service | Separate service accounts per workload |
| Workload Identity | Bind K8s SAs to GCP SAs in GKE |
| Short-lived tokens | Use impersonation instead of key files |
| No SA keys | Avoid downloading JSON key files |

### Secret Manager vs Environment Variables

| Factor | Secret Manager | Env Variables |
|--------|---------------|---------------|
| Rotation | Automatic versioning | Manual redeploy |
| Audit | Cloud Audit Logs | No audit trail |
| Access control | IAM per-secret | Per-service |
| Pricing | $0.06/10K access ops | Free |
| Use case | Credentials, API keys | Non-sensitive config |

### Secret Manager Usage

```python
from google.cloud import secretmanager

def get_secret(project_id, secret_id, version="latest"):
    client = secretmanager.SecretManagerServiceClient()
    name = f"projects/{project_id}/secrets/{secret_id}/versions/{version}"
    response = client.access_secret_version(request={"name": name})
    return response.payload.data.decode("UTF-8")

# Usage
db_password = get_secret("my-project", "db-password")
```
