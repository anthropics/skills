# MLOps Production Patterns

Production ML infrastructure patterns for model deployment, monitoring, and lifecycle management.

---

## Table of Contents

- [Model Deployment Pipeline](#model-deployment-pipeline)
- [Feature Store Architecture](#feature-store-architecture)
- [Model Monitoring](#model-monitoring)
- [A/B Testing Infrastructure](#ab-testing-infrastructure)
- [Automated Retraining](#automated-retraining)

---

## Model Deployment Pipeline

### Deployment Workflow

1. Export trained model to standardized format (ONNX, TorchScript, SavedModel)
2. Package model with dependencies in Docker container
3. Deploy to staging environment
4. Run integration tests against staging
5. Deploy canary (5% traffic) to production
6. Monitor latency and error rates for 1 hour
7. Promote to full production if metrics pass
8. **Validation:** p95 latency < 100ms, error rate < 0.1%

### Container Structure

```dockerfile
FROM python:3.11-slim

# Install dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy model artifacts
COPY model/ /app/model/
COPY src/ /app/src/

# Health check endpoint
HEALTHCHECK CMD curl -f http://localhost:8080/health || exit 1

EXPOSE 8080
CMD ["uvicorn", "src.server:app", "--host", "0.0.0.0", "--port", "8080"]
```

### Model Serving Options

| Option | Latency | Throughput | Use Case |
|--------|---------|------------|----------|
| FastAPI + Uvicorn | Low | Medium | REST APIs, small models |
| Triton Inference Server | Very Low | Very High | GPU inference, batching |
| TensorFlow Serving | Low | High | TensorFlow models |
| TorchServe | Low | High | PyTorch models |
| Ray Serve | Medium | High | Complex pipelines, multi-model |

### Kubernetes Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: model-serving
spec:
  replicas: 3
  selector:
    matchLabels:
      app: model-serving
  template:
    spec:
      containers:
      - name: model
        image: model:v1.0.0
        resources:
          requests:
            memory: "2Gi"
            cpu: "1"
          limits:
            memory: "4Gi"
            cpu: "2"
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 5
```

---

## Feature Store Architecture

### Feature Store Components

| Component | Purpose | Tools |
|-----------|---------|-------|
| Offline Store | Training data, batch features | BigQuery, Snowflake, S3 |
| Online Store | Low-latency serving | Redis, DynamoDB, Feast |
| Feature Registry | Metadata, lineage | Feast, Tecton, Hopsworks |
| Transformation | Feature engineering | Spark, Flink, dbt |

### Feature Pipeline Workflow

1. Define feature schema in registry
2. Implement transformation logic (SQL or Python)
3. Backfill historical features to offline store
4. Schedule incremental updates
5. Materialize to online store for serving
6. Monitor feature freshness and quality
7. **Validation:** Feature values within expected ranges, no nulls in required fields

### Feature Definition Example

```python
from feast import Entity, Feature, FeatureView, FileSource

user = Entity(name="user_id", value_type=ValueType.INT64)

user_features = FeatureView(
    name="user_features",
    entities=["user_id"],
    ttl=timedelta(days=1),
    features=[
        Feature(name="purchase_count_30d", dtype=ValueType.INT64),
        Feature(name="avg_order_value", dtype=ValueType.FLOAT),
        Feature(name="days_since_last_purchase", dtype=ValueType.INT64),
    ],
    online=True,
    source=FileSource(path="data/user_features.parquet"),
)
```

---

## Model Monitoring

### Monitoring Dimensions

| Dimension | Metrics | Alert Threshold |
|-----------|---------|-----------------|
| Latency | p50, p95, p99 | p95 > 100ms |
| Throughput | requests/sec | < 80% baseline |
| Errors | error rate, 5xx count | > 0.1% |
| Data Drift | PSI, KS statistic | PSI > 0.2 |
| Model Drift | accuracy, AUC decay | > 5% drop |

### Data Drift Detection

```python
from scipy.stats import ks_2samp
import numpy as np

def detect_drift(reference: np.array, current: np.array, threshold: float = 0.05):
    """Detect distribution drift using Kolmogorov-Smirnov test."""
    statistic, p_value = ks_2samp(reference, current)

    drift_detected = p_value < threshold

    return {
        "drift_detected": drift_detected,
        "ks_statistic": statistic,
        "p_value": p_value,
        "threshold": threshold
    }
```

### Monitoring Dashboard Metrics

**Infrastructure:**
- Request latency (p50, p95, p99)
- Requests per second
- Error rate by type
- CPU/memory utilization
- GPU utilization (if applicable)

**Model Performance:**
- Prediction distribution
- Feature value distributions
- Model output confidence
- Ground truth vs predictions (when available)

---

## A/B Testing Infrastructure

### Experiment Workflow

1. Define experiment hypothesis and success metrics
2. Calculate required sample size for statistical power
3. Configure traffic split (control vs treatment)
4. Deploy treatment model alongside control
5. Route traffic based on user/session hash
6. Collect metrics for both variants
7. Run statistical significance test
8. **Validation:** p-value < 0.05, minimum sample size reached

### Traffic Splitting

```python
import hashlib

def get_variant(user_id: str, experiment: str, control_pct: float = 0.5) -> str:
    """Deterministic traffic splitting based on user ID."""
    hash_input = f"{user_id}:{experiment}"
    hash_value = int(hashlib.md5(hash_input.encode()).hexdigest(), 16)
    bucket = (hash_value % 100) / 100.0

    return "control" if bucket < control_pct else "treatment"
```

### Metrics Collection

| Metric Type | Examples | Collection Method |
|-------------|----------|-------------------|
| Primary | Conversion rate, revenue | Event logging |
| Secondary | Latency, engagement | Request logs |
| Guardrail | Error rate, crashes | Monitoring system |

---

## Automated Retraining

### Retraining Triggers

| Trigger | Detection Method | Action |
|---------|------------------|--------|
| Scheduled | Cron (weekly/monthly) | Full retrain |
| Performance drop | Accuracy < threshold | Immediate retrain |
| Data drift | PSI > 0.2 | Evaluate, then retrain |
| New data volume | X new samples | Incremental update |

### Retraining Pipeline

1. Trigger detection (schedule, drift, performance)
2. Fetch latest training data from feature store
3. Run training job with hyperparameter config
4. Evaluate model on holdout set
5. Compare against production model
6. If improved: register new model version
7. Deploy to staging for validation
8. Promote to production via canary
9. **Validation:** New model outperforms baseline on key metrics

### MLflow Model Registry Integration

```python
import mlflow

def register_model(model, metrics: dict, model_name: str):
    """Register trained model with MLflow."""
    with mlflow.start_run():
        # Log metrics
        for name, value in metrics.items():
            mlflow.log_metric(name, value)

        # Log model
        mlflow.sklearn.log_model(model, "model")

        # Register in model registry
        model_uri = f"runs:/{mlflow.active_run().info.run_id}/model"
        mlflow.register_model(model_uri, model_name)
```
