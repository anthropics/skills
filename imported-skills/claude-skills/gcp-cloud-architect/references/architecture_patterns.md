# GCP Architecture Patterns

Reference guide for selecting the right GCP architecture pattern based on application requirements.

---

## Table of Contents

- [Pattern Selection Matrix](#pattern-selection-matrix)
- [Pattern 1: Serverless Web Application](#pattern-1-serverless-web-application)
- [Pattern 2: Microservices on GKE](#pattern-2-microservices-on-gke)
- [Pattern 3: Three-Tier Application](#pattern-3-three-tier-application)
- [Pattern 4: Serverless Data Pipeline](#pattern-4-serverless-data-pipeline)
- [Pattern 5: ML Platform](#pattern-5-ml-platform)
- [Pattern 6: Multi-Region High Availability](#pattern-6-multi-region-high-availability)

---

## Pattern Selection Matrix

| Pattern | Best For | Users | Monthly Cost | Complexity |
|---------|----------|-------|--------------|------------|
| Serverless Web | MVP, SaaS, mobile backend | <50K | $30-400 | Low |
| Microservices on GKE | Complex services, enterprise | 10K-500K | $400-2500 | Medium |
| Three-Tier | Traditional web, e-commerce | 10K-200K | $300-1500 | Medium |
| Data Pipeline | Analytics, ETL, streaming | Any | $100-2000 | Medium-High |
| ML Platform | Training, serving, MLOps | Any | $200-5000 | High |
| Multi-Region HA | Global apps, DR | >100K | 2x single | High |

---

## Pattern 1: Serverless Web Application

### Use Case
SaaS platforms, mobile backends, low-traffic websites, MVPs

### Architecture Diagram

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│  Cloud CDN  │────▶│   Cloud     │     │  Identity   │
│   (CDN)     │     │  Storage    │     │  Platform   │
└─────────────┘     │  (Static)   │     │   (Auth)    │
                    └─────────────┘     └──────┬──────┘
                                               │
┌─────────────┐     ┌─────────────┐     ┌──────▼──────┐
│  Cloud DNS  │────▶│   Cloud     │────▶│  Cloud Run  │
│   (DNS)     │     │  Load Bal.  │     │   (API)     │
└─────────────┘     └─────────────┘     └──────┬──────┘
                                               │
                                        ┌──────▼──────┐
                                        │  Firestore  │
                                        │ (Database)  │
                                        └─────────────┘
```

### Service Stack

| Layer | Service | Configuration |
|-------|---------|---------------|
| Frontend | Cloud Storage + Cloud CDN | Static hosting with HTTPS |
| API | Cloud Run | Containerized API with auto-scaling |
| Database | Firestore | Native mode, pay-per-operation |
| Auth | Identity Platform | Multi-provider authentication |
| CI/CD | Cloud Build | Automated container deployments |

### Terraform Example

```hcl
resource "google_cloud_run_v2_service" "api" {
  name     = "my-app-api"
  location = "us-central1"

  template {
    containers {
      image = "gcr.io/my-project/my-app:latest"
      resources {
        limits = {
          cpu    = "1000m"
          memory = "512Mi"
        }
      }
    }
    scaling {
      min_instance_count = 0
      max_instance_count = 10
    }
  }
}
```

### Cost Breakdown (10K users)

| Service | Monthly Cost |
|---------|-------------|
| Cloud Run | $5-25 |
| Firestore | $5-30 |
| Cloud CDN | $5-15 |
| Cloud Storage | $1-5 |
| Identity Platform | $0-10 |
| **Total** | **$16-85** |

### Pros and Cons

**Pros:**
- Scale-to-zero (pay nothing when idle)
- Container-based (no runtime restrictions)
- Built-in HTTPS and custom domains
- Auto-scaling with no configuration

**Cons:**
- Cold starts if min instances = 0
- Firestore query limitations vs SQL
- Vendor lock-in to GCP

---

## Pattern 2: Microservices on GKE

### Use Case
Complex business systems, enterprise applications, platform engineering

### Architecture Diagram

```
┌─────────────┐     ┌─────────────┐
│  Cloud CDN  │────▶│   Global    │
│   (CDN)     │     │  Load Bal.  │
└─────────────┘     └──────┬──────┘
                           │
                    ┌──────▼──────┐
                    │     GKE     │
                    │  Autopilot  │
                    └──────┬──────┘
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
 ┌──────▼──────┐    ┌──────▼──────┐    ┌──────▼──────┐
 │  Cloud SQL  │    │ Memorystore │    │   Pub/Sub   │
 │ (Postgres)  │    │   (Redis)   │    │ (Messaging) │
 └─────────────┘    └─────────────┘    └─────────────┘
```

### Service Stack

| Layer | Service | Configuration |
|-------|---------|---------------|
| CDN | Cloud CDN | Edge caching, HTTPS |
| Load Balancer | Global Application LB | Backend services, health checks |
| Compute | GKE Autopilot | Managed node provisioning |
| Database | Cloud SQL PostgreSQL | Regional HA, read replicas |
| Cache | Memorystore Redis | Session, query caching |
| Messaging | Pub/Sub | Async service communication |

### GKE Autopilot Configuration

```yaml
# Deployment manifest
apiVersion: apps/v1
kind: Deployment
metadata:
  name: api-service
spec:
  replicas: 2
  selector:
    matchLabels:
      app: api-service
  template:
    metadata:
      labels:
        app: api-service
    spec:
      serviceAccountName: api-workload-sa
      containers:
        - name: api
          image: us-central1-docker.pkg.dev/my-project/my-app/api:latest
          ports:
            - containerPort: 8080
          resources:
            requests:
              cpu: "500m"
              memory: "512Mi"
            limits:
              cpu: "1000m"
              memory: "1Gi"
          env:
            - name: DB_HOST
              valueFrom:
                secretKeyRef:
                  name: db-credentials
                  key: host
          readinessProbe:
            httpGet:
              path: /health
              port: 8080
            initialDelaySeconds: 5
            periodSeconds: 10
---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: api-service-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: api-service
  minReplicas: 2
  maxReplicas: 20
  metrics:
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: 70
```

### Cost Breakdown (50K users)

| Service | Monthly Cost |
|---------|-------------|
| GKE Autopilot | $150-400 |
| Cloud Load Balancing | $25-50 |
| Cloud SQL | $100-300 |
| Memorystore | $40-80 |
| Pub/Sub | $5-20 |
| **Total** | **$320-850** |

---

## Pattern 3: Three-Tier Application

### Use Case
Traditional web apps, e-commerce, CMS, applications with complex queries

### Architecture Diagram

```
┌─────────────┐     ┌─────────────┐
│  Cloud CDN  │────▶│   Global    │
│   (CDN)     │     │  Load Bal.  │
└─────────────┘     └──────┬──────┘
                           │
                    ┌──────▼──────┐
                    │  Cloud Run  │
                    │  (or MIG)   │
                    └──────┬──────┘
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
 ┌──────▼──────┐    ┌──────▼──────┐    ┌──────▼──────┐
 │  Cloud SQL  │    │ Memorystore │    │   Cloud     │
 │ (Database)  │    │   (Redis)   │    │  Storage    │
 └─────────────┘    └─────────────┘    └─────────────┘
```

### Service Stack

| Layer | Service | Configuration |
|-------|---------|---------------|
| CDN | Cloud CDN | Edge caching, compression |
| Load Balancer | External Application LB | SSL termination, health checks |
| Compute | Cloud Run or Managed Instance Group | Auto-scaling containers or VMs |
| Database | Cloud SQL (MySQL/PostgreSQL) | Regional HA, automated backups |
| Cache | Memorystore Redis | Session store, query cache |
| Storage | Cloud Storage | Uploads, static assets, backups |

### Cost Breakdown (50K users)

| Service | Monthly Cost |
|---------|-------------|
| Cloud Run / MIG | $80-200 |
| Cloud Load Balancing | $25-50 |
| Cloud SQL | $100-250 |
| Memorystore | $30-60 |
| Cloud Storage | $10-30 |
| **Total** | **$245-590** |

---

## Pattern 4: Serverless Data Pipeline

### Use Case
Analytics, IoT data ingestion, log processing, real-time streaming, ETL

### Architecture Diagram

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Sources   │────▶│   Pub/Sub   │────▶│  Dataflow   │
│ (Apps/IoT)  │     │  (Ingest)   │     │  (Process)  │
└─────────────┘     └─────────────┘     └──────┬──────┘
                                               │
┌─────────────┐     ┌─────────────┐     ┌──────▼──────┐
│   Looker    │◀────│  BigQuery   │◀────│   Cloud     │
│  (Dashbd)   │     │(Warehouse)  │     │  Storage    │
└─────────────┘     └─────────────┘     │ (Data Lake) │
                                        └─────────────┘
```

### Service Stack

| Layer | Service | Purpose |
|-------|---------|---------|
| Ingestion | Pub/Sub | Real-time event capture |
| Processing | Dataflow (Apache Beam) | Stream/batch transforms |
| Warehouse | BigQuery | SQL analytics at scale |
| Storage | Cloud Storage | Raw data lake |
| Visualization | Looker / Looker Studio | Dashboards and reports |
| Orchestration | Cloud Composer (Airflow) | Pipeline scheduling |

### Dataflow Pipeline Example

```python
import apache_beam as beam
from apache_beam.options.pipeline_options import PipelineOptions

options = PipelineOptions([
    '--runner=DataflowRunner',
    '--project=my-project',
    '--region=us-central1',
    '--temp_location=gs://my-bucket/temp',
    '--streaming'
])

with beam.Pipeline(options=options) as p:
    (p
     | 'ReadPubSub' >> beam.io.ReadFromPubSub(topic='projects/my-project/topics/events')
     | 'ParseJSON' >> beam.Map(lambda x: json.loads(x))
     | 'WindowInto' >> beam.WindowInto(beam.window.FixedWindows(60))
     | 'WriteBQ' >> beam.io.WriteToBigQuery(
         'my-project:analytics.events',
         schema='event_id:STRING,event_type:STRING,timestamp:TIMESTAMP',
         write_disposition=beam.io.BigQueryDisposition.WRITE_APPEND
     ))
```

### Cost Breakdown

| Service | Monthly Cost |
|---------|-------------|
| Pub/Sub | $5-30 |
| Dataflow | $30-200 |
| BigQuery (on-demand) | $10-100 |
| Cloud Storage | $5-30 |
| Looker Studio | $0 (free) |
| **Total** | **$50-360** |

---

## Pattern 5: ML Platform

### Use Case
Model training, serving, MLOps, feature engineering

### Architecture Diagram

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│  BigQuery   │────▶│  Vertex AI  │────▶│  Vertex AI  │
│ (Features)  │     │ (Training)  │     │ (Endpoints) │
└─────────────┘     └──────┬──────┘     └─────────────┘
                           │
┌─────────────┐     ┌──────▼──────┐     ┌─────────────┐
│   Cloud     │◀────│   Cloud     │────▶│  Vertex AI  │
│  Functions  │     │  Storage    │     │  Pipelines  │
│ (Triggers)  │     │ (Artifacts) │     │  (MLOps)    │
└─────────────┘     └─────────────┘     └─────────────┘
```

### Service Stack

| Layer | Service | Purpose |
|-------|---------|---------|
| Data | BigQuery | Feature engineering, exploration |
| Training | Vertex AI Training | Custom or AutoML training |
| Serving | Vertex AI Endpoints | Online/batch prediction |
| Storage | Cloud Storage | Datasets, model artifacts |
| Orchestration | Vertex AI Pipelines | ML workflow automation |
| Monitoring | Vertex AI Model Monitoring | Drift and skew detection |

### Vertex AI Training Example

```python
from google.cloud import aiplatform

aiplatform.init(project='my-project', location='us-central1')

job = aiplatform.CustomTrainingJob(
    display_name='my-model-training',
    script_path='train.py',
    container_uri='us-docker.pkg.dev/vertex-ai/training/tf-gpu.2-12:latest',
    requirements=['pandas', 'scikit-learn'],
)

model = job.run(
    replica_count=1,
    machine_type='n1-standard-8',
    accelerator_type='NVIDIA_TESLA_T4',
    accelerator_count=1,
)

endpoint = model.deploy(
    deployed_model_display_name='my-model-v1',
    machine_type='n1-standard-4',
    min_replica_count=1,
    max_replica_count=5,
)
```

### Cost Breakdown

| Service | Monthly Cost |
|---------|-------------|
| Vertex AI Training (T4 GPU) | $50-500 |
| Vertex AI Prediction | $30-200 |
| BigQuery | $10-50 |
| Cloud Storage | $5-30 |
| **Total** | **$95-780** |

---

## Pattern 6: Multi-Region High Availability

### Use Case
Global applications, disaster recovery, data sovereignty compliance

### Architecture Diagram

```
                    ┌─────────────┐
                    │  Cloud DNS  │
                    │(Geo routing)│
                    └──────┬──────┘
                           │
          ┌────────────────┼────────────────┐
          │                                 │
   ┌──────▼──────┐                   ┌──────▼──────┐
   │us-central1  │                   │europe-west1 │
   │  Cloud Run  │                   │  Cloud Run  │
   └──────┬──────┘                   └──────┬──────┘
          │                                 │
   ┌──────▼──────┐                   ┌──────▼──────┐
   │Cloud Spanner│◀── Replication ──▶│Cloud Spanner│
   │  (Region)   │                   │  (Region)   │
   └─────────────┘                   └─────────────┘
```

### Service Stack

| Component | Service | Configuration |
|-----------|---------|---------------|
| DNS | Cloud DNS | Geolocation or latency routing |
| CDN | Cloud CDN | Multiple regional origins |
| Compute | Cloud Run (multi-region) | Deployed in each region |
| Database | Cloud Spanner (multi-region) | Strong global consistency |
| Storage | Cloud Storage (multi-region) | Automatic geo-redundancy |

### Cloud DNS Geolocation Policy

```bash
# Create geolocation routing policy
gcloud dns record-sets create api.example.com \
  --zone=my-zone \
  --type=A \
  --routing-policy-type=GEO \
  --routing-policy-data="us-central1=projects/my-project/regions/us-central1/addresses/api-us;europe-west1=projects/my-project/regions/europe-west1/addresses/api-eu"
```

### Cost Considerations

| Factor | Impact |
|--------|--------|
| Compute | 2x (each region) |
| Cloud Spanner | Multi-region 3x regional price |
| Data Transfer | Cross-region replication costs |
| Cloud DNS | Geolocation queries premium |
| **Total** | **2-3x single region** |

---

## Pattern Comparison Summary

### Latency

| Pattern | Typical Latency |
|---------|-----------------|
| Serverless Web | 30-150ms (Cloud Run) |
| GKE Microservices | 15-80ms |
| Three-Tier | 20-100ms |
| Multi-Region | <50ms (regional) |

### Scaling Characteristics

| Pattern | Scale Limit | Scale Speed |
|---------|-------------|-------------|
| Serverless Web | 1000 instances/service | Seconds |
| GKE Microservices | Cluster node limits | Minutes |
| Data Pipeline | Unlimited (Dataflow) | Seconds |
| Multi-Region | Regional limits | Seconds |

### Operational Complexity

| Pattern | Setup | Maintenance | Debugging |
|---------|-------|-------------|-----------|
| Serverless Web | Low | Low | Medium |
| GKE Microservices | Medium | Medium | Medium |
| Three-Tier | Medium | Medium | Low |
| Data Pipeline | High | Medium | High |
| ML Platform | High | High | High |
| Multi-Region | High | High | High |
