"""
GCP deployment script generator.
Creates gcloud CLI scripts and Terraform configurations for GCP architectures.
"""

import argparse
import json
import sys
from typing import Dict, Any


class DeploymentManager:
    """Generate GCP deployment scripts and IaC configurations."""

    def __init__(self, app_name: str, requirements: Dict[str, Any]):
        """
        Initialize with application requirements.

        Args:
            app_name: Application name (used for resource naming)
            requirements: Dictionary with pattern, region, project requirements
        """
        self.app_name = app_name.lower().replace(' ', '-')
        self.requirements = requirements
        self.region = requirements.get('region', 'us-central1')
        self.project_id = requirements.get('project_id', 'my-project')
        self.pattern = requirements.get('pattern', 'serverless_web')

    def generate_gcloud_script(self) -> str:
        """
        Generate gcloud CLI deployment script.

        Returns:
            Shell script as string
        """
        if self.pattern == 'serverless_web':
            return self._gcloud_serverless_web()
        elif self.pattern == 'gke_microservices':
            return self._gcloud_gke_microservices()
        elif self.pattern == 'data_pipeline':
            return self._gcloud_data_pipeline()
        else:
            return self._gcloud_serverless_web()

    def _gcloud_serverless_web(self) -> str:
        """Generate gcloud script for serverless web pattern."""
        return f"""#!/bin/bash
# GCP Serverless Web Deployment Script
# Application: {self.app_name}
# Region: {self.region}
# Pattern: Cloud Run + Firestore + Cloud Storage + Cloud CDN

set -euo pipefail

PROJECT_ID="{self.project_id}"
REGION="{self.region}"
APP_NAME="{self.app_name}"
ENVIRONMENT="${{ENVIRONMENT:-dev}}"

echo "=== Deploying $APP_NAME to GCP ($ENVIRONMENT) ==="

# 1. Set project
gcloud config set project $PROJECT_ID

# 2. Enable required APIs
echo "Enabling required APIs..."
gcloud services enable \\
  run.googleapis.com \\
  firestore.googleapis.com \\
  cloudbuild.googleapis.com \\
  artifactregistry.googleapis.com \\
  secretmanager.googleapis.com \\
  compute.googleapis.com \\
  monitoring.googleapis.com \\
  logging.googleapis.com

# 3. Create Artifact Registry repository
echo "Creating Artifact Registry repository..."
gcloud artifacts repositories create $APP_NAME \\
  --repository-format=docker \\
  --location=$REGION \\
  --description="Docker images for $APP_NAME" \\
  || echo "Repository already exists"

# 4. Build and push container image
echo "Building container image..."
gcloud builds submit \\
  --tag $REGION-docker.pkg.dev/$PROJECT_ID/$APP_NAME/$APP_NAME:latest \\
  .

# 5. Create Firestore database
echo "Creating Firestore database..."
gcloud firestore databases create \\
  --location=$REGION \\
  --type=firestore-native \\
  || echo "Firestore database already exists"

# 6. Create service account for Cloud Run
echo "Creating service account..."
SA_NAME="${{APP_NAME}}-run-sa"
gcloud iam service-accounts create $SA_NAME \\
  --display-name="$APP_NAME Cloud Run Service Account" \\
  || echo "Service account already exists"

# Grant Firestore access
gcloud projects add-iam-policy-binding $PROJECT_ID \\
  --member="serviceAccount:$SA_NAME@$PROJECT_ID.iam.gserviceaccount.com" \\
  --role="roles/datastore.user" \\
  --condition=None

# Grant Secret Manager access
gcloud projects add-iam-policy-binding $PROJECT_ID \\
  --member="serviceAccount:$SA_NAME@$PROJECT_ID.iam.gserviceaccount.com" \\
  --role="roles/secretmanager.secretAccessor" \\
  --condition=None

# 7. Deploy Cloud Run service
echo "Deploying Cloud Run service..."
gcloud run deploy $APP_NAME-api \\
  --image $REGION-docker.pkg.dev/$PROJECT_ID/$APP_NAME/$APP_NAME:latest \\
  --region $REGION \\
  --platform managed \\
  --service-account $SA_NAME@$PROJECT_ID.iam.gserviceaccount.com \\
  --memory 512Mi \\
  --cpu 1 \\
  --min-instances 0 \\
  --max-instances 10 \\
  --set-env-vars "PROJECT_ID=$PROJECT_ID,ENVIRONMENT=$ENVIRONMENT" \\
  --allow-unauthenticated

# 8. Create Cloud Storage bucket for static assets
echo "Creating static assets bucket..."
BUCKET_NAME="${{PROJECT_ID}}-${{APP_NAME}}-static"
gsutil mb -l $REGION gs://$BUCKET_NAME/ || echo "Bucket already exists"
gsutil iam ch allUsers:objectViewer gs://$BUCKET_NAME

# 9. Set up Cloud Monitoring alerting
echo "Setting up monitoring..."
gcloud alpha monitoring policies create \\
  --notification-channels="" \\
  --display-name="$APP_NAME High Error Rate" \\
  --condition-display-name="Cloud Run 5xx Error Rate" \\
  --condition-filter='resource.type="cloud_run_revision" AND metric.type="run.googleapis.com/request_count" AND metric.labels.response_code_class="5xx"' \\
  --condition-threshold-value=10 \\
  --condition-threshold-duration=60s \\
  || echo "Alert policy creation requires additional configuration"

# 10. Output deployment info
echo ""
echo "=== Deployment Complete ==="
SERVICE_URL=$(gcloud run services describe $APP_NAME-api --region $REGION --format 'value(status.url)')
echo "Cloud Run URL: $SERVICE_URL"
echo "Static Bucket: gs://$BUCKET_NAME"
echo "Firestore: https://console.cloud.google.com/firestore?project=$PROJECT_ID"
echo "Monitoring: https://console.cloud.google.com/monitoring?project=$PROJECT_ID"
"""

    def _gcloud_gke_microservices(self) -> str:
        """Generate gcloud script for GKE microservices pattern."""
        return f"""#!/bin/bash
# GCP GKE Microservices Deployment Script
# Application: {self.app_name}
# Region: {self.region}
# Pattern: GKE Autopilot + Cloud SQL + Memorystore

set -euo pipefail

PROJECT_ID="{self.project_id}"
REGION="{self.region}"
APP_NAME="{self.app_name}"
ENVIRONMENT="${{ENVIRONMENT:-dev}}"
CLUSTER_NAME="${{APP_NAME}}-cluster"
NETWORK_NAME="${{APP_NAME}}-vpc"

echo "=== Deploying $APP_NAME GKE Microservices ($ENVIRONMENT) ==="

# 1. Set project
gcloud config set project $PROJECT_ID

# 2. Enable required APIs
echo "Enabling required APIs..."
gcloud services enable \\
  container.googleapis.com \\
  sqladmin.googleapis.com \\
  redis.googleapis.com \\
  cloudbuild.googleapis.com \\
  artifactregistry.googleapis.com \\
  secretmanager.googleapis.com \\
  servicenetworking.googleapis.com \\
  compute.googleapis.com

# 3. Create VPC network
echo "Creating VPC network..."
gcloud compute networks create $NETWORK_NAME \\
  --subnet-mode=auto \\
  || echo "Network already exists"

# Allocate IP range for private services
gcloud compute addresses create google-managed-services-$NETWORK_NAME \\
  --global \\
  --purpose=VPC_PEERING \\
  --prefix-length=16 \\
  --network=$NETWORK_NAME \\
  || echo "IP range already exists"

gcloud services vpc-peerings connect \\
  --service=servicenetworking.googleapis.com \\
  --ranges=google-managed-services-$NETWORK_NAME \\
  --network=$NETWORK_NAME \\
  || echo "VPC peering already exists"

# 4. Create GKE Autopilot cluster
echo "Creating GKE Autopilot cluster..."
gcloud container clusters create-auto $CLUSTER_NAME \\
  --region $REGION \\
  --network $NETWORK_NAME \\
  --release-channel regular \\
  --enable-master-authorized-networks \\
  --enable-private-nodes \\
  || echo "Cluster already exists"

# 5. Get cluster credentials
gcloud container clusters get-credentials $CLUSTER_NAME --region $REGION

# 6. Create Cloud SQL instance
echo "Creating Cloud SQL instance..."
gcloud sql instances create $APP_NAME-db \\
  --database-version=POSTGRES_15 \\
  --tier=db-custom-2-8192 \\
  --region=$REGION \\
  --network=$NETWORK_NAME \\
  --no-assign-ip \\
  --availability-type=regional \\
  --backup-start-time=02:00 \\
  --storage-auto-increase \\
  || echo "Cloud SQL instance already exists"

# Create database
gcloud sql databases create $APP_NAME \\
  --instance=$APP_NAME-db \\
  || echo "Database already exists"

# 7. Create Memorystore Redis instance
echo "Creating Memorystore Redis instance..."
gcloud redis instances create $APP_NAME-cache \\
  --size=1 \\
  --region=$REGION \\
  --redis-version=redis_7_0 \\
  --network=$NETWORK_NAME \\
  --tier=basic \\
  || echo "Redis instance already exists"

# 8. Configure Workload Identity
echo "Configuring Workload Identity..."
SA_NAME="${{APP_NAME}}-workload"
gcloud iam service-accounts create $SA_NAME \\
  --display-name="$APP_NAME Workload Identity SA" \\
  || echo "Service account already exists"

gcloud projects add-iam-policy-binding $PROJECT_ID \\
  --member="serviceAccount:$SA_NAME@$PROJECT_ID.iam.gserviceaccount.com" \\
  --role="roles/cloudsql.client"

gcloud iam service-accounts add-iam-policy-binding \\
  $SA_NAME@$PROJECT_ID.iam.gserviceaccount.com \\
  --role="roles/iam.workloadIdentityUser" \\
  --member="serviceAccount:$PROJECT_ID.svc.id.goog[default/$SA_NAME]"

echo ""
echo "=== GKE Cluster Ready ==="
echo "Cluster: $CLUSTER_NAME"
echo "Cloud SQL: $APP_NAME-db"
echo "Redis: $APP_NAME-cache"
echo ""
echo "Next: Apply Kubernetes manifests with 'kubectl apply -f k8s/'"
"""

    def _gcloud_data_pipeline(self) -> str:
        """Generate gcloud script for data pipeline pattern."""
        return f"""#!/bin/bash
# GCP Data Pipeline Deployment Script
# Application: {self.app_name}
# Region: {self.region}
# Pattern: Pub/Sub + Dataflow + BigQuery

set -euo pipefail

PROJECT_ID="{self.project_id}"
REGION="{self.region}"
APP_NAME="{self.app_name}"

echo "=== Deploying $APP_NAME Data Pipeline ==="

# 1. Set project
gcloud config set project $PROJECT_ID

# 2. Enable required APIs
echo "Enabling required APIs..."
gcloud services enable \\
  pubsub.googleapis.com \\
  dataflow.googleapis.com \\
  bigquery.googleapis.com \\
  storage.googleapis.com \\
  monitoring.googleapis.com

# 3. Create Pub/Sub topic and subscription
echo "Creating Pub/Sub resources..."
gcloud pubsub topics create $APP_NAME-events \\
  || echo "Topic already exists"

gcloud pubsub subscriptions create $APP_NAME-events-sub \\
  --topic=$APP_NAME-events \\
  --ack-deadline=60 \\
  --message-retention-duration=7d \\
  || echo "Subscription already exists"

# Dead letter topic
gcloud pubsub topics create $APP_NAME-events-dlq \\
  || echo "DLQ topic already exists"

gcloud pubsub subscriptions update $APP_NAME-events-sub \\
  --dead-letter-topic=$APP_NAME-events-dlq \\
  --max-delivery-attempts=5

# 4. Create BigQuery dataset and table
echo "Creating BigQuery resources..."
bq mk --dataset --location=$REGION $PROJECT_ID:${{APP_NAME//-/_}}_analytics \\
  || echo "Dataset already exists"

bq mk --table \\
  $PROJECT_ID:${{APP_NAME//-/_}}_analytics.events \\
  event_id:STRING,event_type:STRING,payload:STRING,timestamp:TIMESTAMP,processed_at:TIMESTAMP \\
  --time_partitioning_type=DAY \\
  --time_partitioning_field=timestamp \\
  --clustering_fields=event_type \\
  || echo "Table already exists"

# 5. Create Cloud Storage bucket for Dataflow temp/staging
echo "Creating staging bucket..."
STAGING_BUCKET="${{PROJECT_ID}}-${{APP_NAME}}-dataflow"
gsutil mb -l $REGION gs://$STAGING_BUCKET/ || echo "Bucket already exists"

# 6. Create service account for Dataflow
echo "Creating Dataflow service account..."
SA_NAME="${{APP_NAME}}-dataflow-sa"
gcloud iam service-accounts create $SA_NAME \\
  --display-name="$APP_NAME Dataflow Worker SA" \\
  || echo "Service account already exists"

for ROLE in roles/dataflow.worker roles/bigquery.dataEditor roles/pubsub.subscriber roles/storage.objectAdmin; do
  gcloud projects add-iam-policy-binding $PROJECT_ID \\
    --member="serviceAccount:$SA_NAME@$PROJECT_ID.iam.gserviceaccount.com" \\
    --role="$ROLE" \\
    --condition=None
done

echo ""
echo "=== Data Pipeline Infrastructure Ready ==="
echo "Pub/Sub Topic: $APP_NAME-events"
echo "BigQuery Dataset: ${{APP_NAME//-/_}}_analytics"
echo "Staging Bucket: gs://$STAGING_BUCKET"
echo ""
echo "Next: Deploy Dataflow job with Apache Beam pipeline"
echo "  python -m apache_beam.examples.streaming_wordcount \\\\"
echo "    --runner DataflowRunner \\\\"
echo "    --project $PROJECT_ID \\\\"
echo "    --region $REGION \\\\"
echo "    --temp_location gs://$STAGING_BUCKET/temp"
"""

    def generate_terraform_configuration(self) -> str:
        """
        Generate Terraform configuration for the selected pattern.

        Returns:
            Terraform HCL configuration as string
        """
        if self.pattern == 'serverless_web':
            return self._terraform_serverless_web()
        elif self.pattern == 'gke_microservices':
            return self._terraform_gke_microservices()
        else:
            return self._terraform_serverless_web()

    def _terraform_serverless_web(self) -> str:
        """Generate Terraform for serverless web pattern."""
        return f"""terraform {{
  required_version = ">= 1.0"
  required_providers {{
    google = {{
      source  = "hashicorp/google"
      version = "~> 5.0"
    }}
  }}
}}

provider "google" {{
  project = var.project_id
  region  = var.region
}}

variable "project_id" {{
  description = "GCP project ID"
  type        = string
}}

variable "region" {{
  description = "GCP region"
  type        = string
  default     = "{self.region}"
}}

variable "environment" {{
  description = "Environment name"
  type        = string
  default     = "dev"
}}

variable "app_name" {{
  description = "Application name"
  type        = string
  default     = "{self.app_name}"
}}

# Enable required APIs
resource "google_project_service" "apis" {{
  for_each = toset([
    "run.googleapis.com",
    "firestore.googleapis.com",
    "secretmanager.googleapis.com",
    "artifactregistry.googleapis.com",
    "monitoring.googleapis.com",
  ])
  project = var.project_id
  service = each.value
}}

# Service Account for Cloud Run
resource "google_service_account" "cloud_run" {{
  account_id   = "${{var.app_name}}-run-sa"
  display_name = "${{var.app_name}} Cloud Run Service Account"
}}

resource "google_project_iam_member" "firestore_user" {{
  project = var.project_id
  role    = "roles/datastore.user"
  member  = "serviceAccount:${{google_service_account.cloud_run.email}}"
}}

resource "google_project_iam_member" "secret_accessor" {{
  project = var.project_id
  role    = "roles/secretmanager.secretAccessor"
  member  = "serviceAccount:${{google_service_account.cloud_run.email}}"
}}

# Firestore Database
resource "google_firestore_database" "default" {{
  project     = var.project_id
  name        = "(default)"
  location_id = var.region
  type        = "FIRESTORE_NATIVE"

  depends_on = [google_project_service.apis["firestore.googleapis.com"]]
}}

# Cloud Run Service
resource "google_cloud_run_v2_service" "api" {{
  name     = "${{var.environment}}-${{var.app_name}}-api"
  location = var.region

  template {{
    service_account = google_service_account.cloud_run.email

    containers {{
      image = "${{var.region}}-docker.pkg.dev/${{var.project_id}}/${{var.app_name}}/${{var.app_name}}:latest"

      resources {{
        limits = {{
          cpu    = "1000m"
          memory = "512Mi"
        }}
      }}

      env {{
        name  = "PROJECT_ID"
        value = var.project_id
      }}

      env {{
        name  = "ENVIRONMENT"
        value = var.environment
      }}
    }}

    scaling {{
      min_instance_count = 0
      max_instance_count = 10
    }}
  }}

  depends_on = [google_project_service.apis["run.googleapis.com"]]

  labels = {{
    environment = var.environment
    app         = var.app_name
  }}
}}

# Allow unauthenticated access (public API)
resource "google_cloud_run_v2_service_iam_member" "public" {{
  project  = var.project_id
  location = var.region
  name     = google_cloud_run_v2_service.api.name
  role     = "roles/run.invoker"
  member   = "allUsers"
}}

# Cloud Storage bucket for static assets
resource "google_storage_bucket" "static" {{
  name     = "${{var.project_id}}-${{var.app_name}}-static"
  location = var.region

  uniform_bucket_level_access = true

  website {{
    main_page_suffix = "index.html"
    not_found_page   = "404.html"
  }}

  lifecycle_rule {{
    condition {{
      age = 30
    }}
    action {{
      type          = "SetStorageClass"
      storage_class = "NEARLINE"
    }}
  }}

  labels = {{
    environment = var.environment
    app         = var.app_name
  }}
}}

# Outputs
output "cloud_run_url" {{
  description = "Cloud Run service URL"
  value       = google_cloud_run_v2_service.api.uri
}}

output "static_bucket" {{
  description = "Static assets bucket name"
  value       = google_storage_bucket.static.name
}}

output "service_account" {{
  description = "Cloud Run service account email"
  value       = google_service_account.cloud_run.email
}}
"""

    def _terraform_gke_microservices(self) -> str:
        """Generate Terraform for GKE microservices pattern."""
        return f"""terraform {{
  required_version = ">= 1.0"
  required_providers {{
    google = {{
      source  = "hashicorp/google"
      version = "~> 5.0"
    }}
  }}
}}

provider "google" {{
  project = var.project_id
  region  = var.region
}}

variable "project_id" {{
  description = "GCP project ID"
  type        = string
}}

variable "region" {{
  description = "GCP region"
  type        = string
  default     = "{self.region}"
}}

variable "environment" {{
  description = "Environment name"
  type        = string
  default     = "dev"
}}

variable "app_name" {{
  description = "Application name"
  type        = string
  default     = "{self.app_name}"
}}

# Enable required APIs
resource "google_project_service" "apis" {{
  for_each = toset([
    "container.googleapis.com",
    "sqladmin.googleapis.com",
    "redis.googleapis.com",
    "servicenetworking.googleapis.com",
    "secretmanager.googleapis.com",
  ])
  project = var.project_id
  service = each.value
}}

# VPC Network
resource "google_compute_network" "main" {{
  name                    = "${{var.app_name}}-vpc"
  auto_create_subnetworks = false
}}

resource "google_compute_subnetwork" "main" {{
  name          = "${{var.app_name}}-subnet"
  ip_cidr_range = "10.0.0.0/20"
  region        = var.region
  network       = google_compute_network.main.id

  secondary_ip_range {{
    range_name    = "pods"
    ip_cidr_range = "10.4.0.0/14"
  }}

  secondary_ip_range {{
    range_name    = "services"
    ip_cidr_range = "10.8.0.0/20"
  }}
}}

# GKE Autopilot Cluster
resource "google_container_cluster" "main" {{
  name     = "${{var.environment}}-${{var.app_name}}-cluster"
  location = var.region

  enable_autopilot = true

  network    = google_compute_network.main.name
  subnetwork = google_compute_subnetwork.main.name

  ip_allocation_policy {{
    cluster_secondary_range_name  = "pods"
    services_secondary_range_name = "services"
  }}

  release_channel {{
    channel = "REGULAR"
  }}

  depends_on = [google_project_service.apis["container.googleapis.com"]]
}}

# Private Services Access for Cloud SQL
resource "google_compute_global_address" "private_ip" {{
  name          = "private-ip-range"
  purpose       = "VPC_PEERING"
  address_type  = "INTERNAL"
  prefix_length = 16
  network       = google_compute_network.main.id
}}

resource "google_service_networking_connection" "private_vpc" {{
  network                 = google_compute_network.main.id
  service                 = "servicenetworking.googleapis.com"
  reserved_peering_ranges = [google_compute_global_address.private_ip.name]
}}

# Cloud SQL PostgreSQL
resource "google_sql_database_instance" "main" {{
  name             = "${{var.environment}}-${{var.app_name}}-db"
  database_version = "POSTGRES_15"
  region           = var.region

  settings {{
    tier              = "db-custom-2-8192"
    availability_type = "REGIONAL"

    backup_configuration {{
      enabled                        = true
      start_time                     = "02:00"
      point_in_time_recovery_enabled = true
    }}

    ip_configuration {{
      ipv4_enabled    = false
      private_network = google_compute_network.main.id
    }}

    disk_autoresize = true
  }}

  depends_on = [google_service_networking_connection.private_vpc]
}}

resource "google_sql_database" "app" {{
  name     = var.app_name
  instance = google_sql_database_instance.main.name
}}

# Memorystore Redis
resource "google_redis_instance" "cache" {{
  name           = "${{var.environment}}-${{var.app_name}}-cache"
  tier           = "BASIC"
  memory_size_gb = 1
  region         = var.region
  redis_version  = "REDIS_7_0"

  authorized_network = google_compute_network.main.id

  depends_on = [google_project_service.apis["redis.googleapis.com"]]

  labels = {{
    environment = var.environment
    app         = var.app_name
  }}
}}

# Outputs
output "cluster_name" {{
  description = "GKE cluster name"
  value       = google_container_cluster.main.name
}}

output "cloud_sql_connection" {{
  description = "Cloud SQL connection name"
  value       = google_sql_database_instance.main.connection_name
}}

output "redis_host" {{
  description = "Memorystore Redis host"
  value       = google_redis_instance.cache.host
}}
"""


def main():
    parser = argparse.ArgumentParser(
        description='GCP Deployment Manager - Generates gcloud CLI scripts and Terraform configurations'
    )
    parser.add_argument(
        '--app-name', '-a',
        type=str,
        required=True,
        help='Application name'
    )
    parser.add_argument(
        '--pattern', '-p',
        type=str,
        choices=['serverless_web', 'gke_microservices', 'data_pipeline'],
        default='serverless_web',
        help='Architecture pattern (default: serverless_web)'
    )
    parser.add_argument(
        '--region', '-r',
        type=str,
        default='us-central1',
        help='GCP region (default: us-central1)'
    )
    parser.add_argument(
        '--project-id',
        type=str,
        default='my-project',
        help='GCP project ID (default: my-project)'
    )
    parser.add_argument(
        '--format', '-f',
        type=str,
        choices=['gcloud', 'terraform', 'both'],
        default='both',
        help='Output format (default: both)'
    )
    parser.add_argument(
        '--output', '-o',
        type=str,
        help='Output directory for generated files'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output as JSON format'
    )

    args = parser.parse_args()

    requirements = {
        'pattern': args.pattern,
        'region': args.region,
        'project_id': args.project_id
    }

    manager = DeploymentManager(args.app_name, requirements)

    if args.json:
        output = {}
        if args.format in ('gcloud', 'both'):
            output['gcloud_script'] = manager.generate_gcloud_script()
        if args.format in ('terraform', 'both'):
            output['terraform_config'] = manager.generate_terraform_configuration()
        print(json.dumps(output, indent=2))
    elif args.output:
        import os
        os.makedirs(args.output, exist_ok=True)

        if args.format in ('gcloud', 'both'):
            gcloud_path = os.path.join(args.output, 'deploy.sh')
            with open(gcloud_path, 'w') as f:
                f.write(manager.generate_gcloud_script())
            os.chmod(gcloud_path, 0o755)
            print(f"gcloud script written to {gcloud_path}")

        if args.format in ('terraform', 'both'):
            tf_path = os.path.join(args.output, 'main.tf')
            with open(tf_path, 'w') as f:
                f.write(manager.generate_terraform_configuration())
            print(f"Terraform config written to {tf_path}")
    else:
        if args.format in ('gcloud', 'both'):
            print("# ===== gcloud CLI Script =====")
            print(manager.generate_gcloud_script())

        if args.format in ('terraform', 'both'):
            print("# ===== Terraform Configuration =====")
            print(manager.generate_terraform_configuration())


if __name__ == '__main__':
    main()
