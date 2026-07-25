"""
GCP architecture design and service recommendation module.
Generates architecture patterns based on application requirements.
"""

import argparse
import json
import sys
from typing import Dict, List, Any
from enum import Enum


class ApplicationType(Enum):
    """Types of applications supported."""
    WEB_APP = "web_application"
    MOBILE_BACKEND = "mobile_backend"
    DATA_PIPELINE = "data_pipeline"
    MICROSERVICES = "microservices"
    SAAS_PLATFORM = "saas_platform"
    ML_PLATFORM = "ml_platform"


class ArchitectureDesigner:
    """Design GCP architectures based on requirements."""

    def __init__(self, requirements: Dict[str, Any]):
        """
        Initialize with application requirements.

        Args:
            requirements: Dictionary containing app type, traffic, budget, etc.
        """
        self.app_type = requirements.get('application_type', 'web_application')
        self.expected_users = requirements.get('expected_users', 1000)
        self.requests_per_second = requirements.get('requests_per_second', 10)
        self.budget_monthly = requirements.get('budget_monthly_usd', 500)
        self.team_size = requirements.get('team_size', 3)
        self.gcp_experience = requirements.get('gcp_experience', 'beginner')
        self.compliance_needs = requirements.get('compliance', [])
        self.data_size_gb = requirements.get('data_size_gb', 10)

    def recommend_architecture_pattern(self) -> Dict[str, Any]:
        """
        Recommend architecture pattern based on requirements.

        Returns:
            Dictionary with recommended pattern and services
        """
        if self.app_type in ['web_application', 'saas_platform']:
            if self.expected_users < 10000:
                return self._serverless_web_architecture()
            elif self.expected_users < 100000:
                return self._gke_microservices_architecture()
            else:
                return self._multi_region_architecture()

        elif self.app_type == 'mobile_backend':
            return self._serverless_mobile_backend()

        elif self.app_type == 'data_pipeline':
            return self._data_pipeline_architecture()

        elif self.app_type == 'microservices':
            return self._gke_microservices_architecture()

        elif self.app_type == 'ml_platform':
            return self._ml_platform_architecture()

        else:
            return self._serverless_web_architecture()

    def _serverless_web_architecture(self) -> Dict[str, Any]:
        """Serverless web application pattern using Cloud Run."""
        return {
            'pattern_name': 'Serverless Web Application',
            'description': 'Fully serverless architecture with Cloud Run and Firestore',
            'use_case': 'SaaS platforms, low to medium traffic websites, MVPs',
            'services': {
                'frontend': {
                    'service': 'Cloud Storage + Cloud CDN',
                    'purpose': 'Static website hosting with global CDN',
                    'configuration': {
                        'bucket': 'Website bucket with public access',
                        'cdn': 'Cloud CDN with custom domain and HTTPS',
                        'caching': 'Cache-Control headers, edge caching'
                    }
                },
                'api': {
                    'service': 'Cloud Run',
                    'purpose': 'Containerized API backend with auto-scaling',
                    'configuration': {
                        'cpu': '1 vCPU',
                        'memory': '512 Mi',
                        'min_instances': '0 (scale to zero)',
                        'max_instances': '10',
                        'concurrency': '80 requests per instance',
                        'timeout': '300 seconds'
                    }
                },
                'database': {
                    'service': 'Firestore',
                    'purpose': 'NoSQL document database with real-time sync',
                    'configuration': {
                        'mode': 'Native mode',
                        'location': 'Regional or multi-region',
                        'security_rules': 'Firestore security rules',
                        'backup': 'Scheduled exports to Cloud Storage'
                    }
                },
                'authentication': {
                    'service': 'Identity Platform',
                    'purpose': 'User authentication and authorization',
                    'configuration': {
                        'providers': 'Email/password, Google, Apple, OIDC',
                        'mfa': 'SMS or TOTP multi-factor authentication',
                        'token_expiration': '1 hour access, 30 days refresh'
                    }
                },
                'cicd': {
                    'service': 'Cloud Build',
                    'purpose': 'Automated build and deployment from Git',
                    'configuration': {
                        'source': 'GitHub or Cloud Source Repositories',
                        'build': 'Automatic on commit',
                        'environments': 'dev, staging, production'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': self._calculate_serverless_cost(),
                'breakdown': {
                    'Cloud CDN': '5-20 USD',
                    'Cloud Run': '5-25 USD',
                    'Firestore': '5-30 USD',
                    'Identity Platform': '0-10 USD (free tier: 50k MAU)',
                    'Cloud Storage': '1-5 USD'
                }
            },
            'pros': [
                'No server management',
                'Auto-scaling with scale-to-zero',
                'Pay only for what you use',
                'No cold starts with min instances',
                'Container-based (no runtime restrictions)'
            ],
            'cons': [
                'Vendor lock-in to GCP',
                'Regional availability considerations',
                'Debugging distributed systems complex',
                'Firestore query limitations vs SQL'
            ],
            'scaling_characteristics': {
                'users_supported': '1k - 100k',
                'requests_per_second': '100 - 10,000',
                'scaling_method': 'Automatic (Cloud Run auto-scaling)'
            }
        }

    def _gke_microservices_architecture(self) -> Dict[str, Any]:
        """GKE-based microservices architecture."""
        return {
            'pattern_name': 'Microservices on GKE',
            'description': 'Kubernetes-native architecture with managed services',
            'use_case': 'SaaS platforms, complex microservices, enterprise applications',
            'services': {
                'load_balancer': {
                    'service': 'Cloud Load Balancing',
                    'purpose': 'Global HTTP(S) load balancing',
                    'configuration': {
                        'type': 'External Application Load Balancer',
                        'ssl': 'Google-managed SSL certificate',
                        'health_checks': '/health endpoint, 10s interval',
                        'cdn': 'Cloud CDN enabled for static content'
                    }
                },
                'compute': {
                    'service': 'GKE Autopilot',
                    'purpose': 'Managed Kubernetes for containerized workloads',
                    'configuration': {
                        'mode': 'Autopilot (fully managed node provisioning)',
                        'scaling': 'Horizontal Pod Autoscaler',
                        'networking': 'VPC-native with Alias IPs',
                        'workload_identity': 'Enabled for secure service account binding'
                    }
                },
                'database': {
                    'service': 'Cloud SQL (PostgreSQL)',
                    'purpose': 'Managed relational database',
                    'configuration': {
                        'tier': 'db-custom-2-8192 (2 vCPU, 8 GB RAM)',
                        'high_availability': 'Regional with automatic failover',
                        'read_replicas': '1-2 for read scaling',
                        'backup': 'Automated daily backups, 7-day retention',
                        'encryption': 'Customer-managed encryption key (CMEK)'
                    }
                },
                'cache': {
                    'service': 'Memorystore (Redis)',
                    'purpose': 'Session storage, application caching',
                    'configuration': {
                        'tier': 'Basic (1 GB) or Standard (HA)',
                        'version': 'Redis 7.0',
                        'eviction_policy': 'allkeys-lru'
                    }
                },
                'messaging': {
                    'service': 'Pub/Sub',
                    'purpose': 'Asynchronous messaging between services',
                    'configuration': {
                        'topics': 'Per-domain event topics',
                        'subscriptions': 'Pull or push delivery',
                        'dead_letter': 'Dead letter topic after 5 retries',
                        'ordering': 'Ordering keys for ordered delivery'
                    }
                },
                'storage': {
                    'service': 'Cloud Storage',
                    'purpose': 'User uploads, backups, logs',
                    'configuration': {
                        'storage_class': 'Standard with lifecycle policies',
                        'versioning': 'Enabled for important buckets',
                        'lifecycle': 'Transition to Nearline after 30 days'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': self._calculate_gke_cost(),
                'breakdown': {
                    'Cloud Load Balancing': '20-40 USD',
                    'GKE Autopilot': '75-250 USD',
                    'Cloud SQL': '80-250 USD',
                    'Memorystore': '30-80 USD',
                    'Pub/Sub': '5-20 USD',
                    'Cloud Storage': '5-20 USD'
                }
            },
            'pros': [
                'Kubernetes ecosystem compatibility',
                'Fine-grained scaling control',
                'Multi-cloud portability',
                'Rich service mesh (Anthos Service Mesh)',
                'Managed node provisioning with Autopilot'
            ],
            'cons': [
                'Higher baseline costs than serverless',
                'Kubernetes learning curve',
                'More operational complexity',
                'GKE management fee ($74.40/month per cluster)'
            ],
            'scaling_characteristics': {
                'users_supported': '10k - 500k',
                'requests_per_second': '1,000 - 50,000',
                'scaling_method': 'HPA + Cluster Autoscaler'
            }
        }

    def _serverless_mobile_backend(self) -> Dict[str, Any]:
        """Serverless mobile backend with Firebase."""
        return {
            'pattern_name': 'Serverless Mobile Backend',
            'description': 'Mobile-first backend with Firebase and Cloud Functions',
            'use_case': 'Mobile apps, real-time applications, offline-first apps',
            'services': {
                'api': {
                    'service': 'Cloud Functions (2nd gen)',
                    'purpose': 'Event-driven API handlers',
                    'configuration': {
                        'runtime': 'Node.js 20 or Python 3.12',
                        'memory': '256 MB - 1 GB',
                        'timeout': '60 seconds',
                        'concurrency': 'Up to 1000 concurrent'
                    }
                },
                'database': {
                    'service': 'Firestore',
                    'purpose': 'Real-time NoSQL database with offline sync',
                    'configuration': {
                        'mode': 'Native mode',
                        'multi_region': 'nam5 or eur3 for HA',
                        'security_rules': 'Client-side access control',
                        'indexes': 'Composite indexes for queries'
                    }
                },
                'file_storage': {
                    'service': 'Cloud Storage (Firebase)',
                    'purpose': 'User uploads (images, videos, documents)',
                    'configuration': {
                        'access': 'Firebase Security Rules',
                        'resumable_uploads': 'Enabled for large files',
                        'cdn': 'Automatic via Firebase Hosting CDN'
                    }
                },
                'authentication': {
                    'service': 'Firebase Authentication',
                    'purpose': 'User management and federation',
                    'configuration': {
                        'providers': 'Email, Google, Apple, Phone',
                        'anonymous_auth': 'Enabled for guest access',
                        'custom_claims': 'Role-based access control',
                        'multi_tenancy': 'Supported via Identity Platform'
                    }
                },
                'push_notifications': {
                    'service': 'Firebase Cloud Messaging (FCM)',
                    'purpose': 'Push notifications to mobile devices',
                    'configuration': {
                        'platforms': 'iOS (APNs), Android, Web',
                        'topics': 'Topic-based group messaging',
                        'analytics': 'Notification delivery tracking'
                    }
                },
                'analytics': {
                    'service': 'Google Analytics (Firebase)',
                    'purpose': 'User analytics and event tracking',
                    'configuration': {
                        'events': 'Custom and automatic events',
                        'audiences': 'User segmentation',
                        'bigquery_export': 'Raw event export to BigQuery'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': 40 + (self.expected_users * 0.004),
                'breakdown': {
                    'Cloud Functions': '5-30 USD',
                    'Firestore': '10-50 USD',
                    'Cloud Storage': '5-20 USD',
                    'Identity Platform': '0-15 USD',
                    'FCM': '0 USD (free)',
                    'Analytics': '0 USD (free)'
                }
            },
            'pros': [
                'Real-time data sync built-in',
                'Offline-first support',
                'Firebase SDKs for iOS/Android/Web',
                'Free tier covers most MVPs',
                'Rapid development with Firebase console'
            ],
            'cons': [
                'Firestore query limitations',
                'Vendor lock-in to Firebase/GCP',
                'Cost scaling can be unpredictable',
                'Limited server-side control'
            ],
            'scaling_characteristics': {
                'users_supported': '1k - 1M',
                'requests_per_second': '100 - 100,000',
                'scaling_method': 'Automatic (Firebase managed)'
            }
        }

    def _data_pipeline_architecture(self) -> Dict[str, Any]:
        """Serverless data pipeline with BigQuery."""
        return {
            'pattern_name': 'Serverless Data Pipeline',
            'description': 'Scalable data ingestion, processing, and analytics',
            'use_case': 'Analytics, IoT data, log processing, ETL, data warehousing',
            'services': {
                'ingestion': {
                    'service': 'Pub/Sub',
                    'purpose': 'Real-time event and data ingestion',
                    'configuration': {
                        'throughput': 'Unlimited (auto-scaling)',
                        'retention': '7 days (configurable to 31 days)',
                        'ordering': 'Ordering keys for ordered delivery',
                        'dead_letter': 'Dead letter topic for failed messages'
                    }
                },
                'processing': {
                    'service': 'Dataflow (Apache Beam)',
                    'purpose': 'Stream and batch data processing',
                    'configuration': {
                        'mode': 'Streaming or batch',
                        'autoscaling': 'Horizontal autoscaling',
                        'workers': f'{max(1, self.data_size_gb // 20)} initial workers',
                        'sdk': 'Python or Java Apache Beam SDK'
                    }
                },
                'warehouse': {
                    'service': 'BigQuery',
                    'purpose': 'Serverless data warehouse and analytics',
                    'configuration': {
                        'pricing': 'On-demand ($6.25/TB queried) or slots',
                        'partitioning': 'By ingestion time or custom field',
                        'clustering': 'Up to 4 clustering columns',
                        'streaming_insert': 'Real-time data availability'
                    }
                },
                'storage': {
                    'service': 'Cloud Storage (Data Lake)',
                    'purpose': 'Raw data lake and archival storage',
                    'configuration': {
                        'format': 'Parquet or Avro (columnar)',
                        'partitioning': 'By date (year/month/day)',
                        'lifecycle': 'Transition to Coldline after 90 days',
                        'catalog': 'Dataplex for data governance'
                    }
                },
                'visualization': {
                    'service': 'Looker / Looker Studio',
                    'purpose': 'Business intelligence dashboards',
                    'configuration': {
                        'source': 'BigQuery direct connection',
                        'refresh': 'Real-time or scheduled',
                        'sharing': 'Embedded or web dashboards'
                    }
                },
                'orchestration': {
                    'service': 'Cloud Composer (Airflow)',
                    'purpose': 'Workflow orchestration for batch pipelines',
                    'configuration': {
                        'environment': 'Cloud Composer 2 (auto-scaling)',
                        'dags': 'Python DAG definitions',
                        'scheduling': 'Cron-based scheduling'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': self._calculate_data_pipeline_cost(),
                'breakdown': {
                    'Pub/Sub': '5-30 USD',
                    'Dataflow': '20-150 USD',
                    'BigQuery': '10-100 USD (on-demand)',
                    'Cloud Storage': '5-30 USD',
                    'Looker Studio': '0 USD (free)',
                    'Cloud Composer': '300+ USD (if used)'
                }
            },
            'pros': [
                'Fully serverless data stack',
                'BigQuery scales to petabytes',
                'Real-time and batch in same pipeline',
                'Cost-effective with on-demand pricing',
                'ML integration via BigQuery ML'
            ],
            'cons': [
                'Dataflow has steep learning curve (Beam SDK)',
                'BigQuery costs based on data scanned',
                'Cloud Composer expensive for small workloads',
                'Schema evolution requires planning'
            ],
            'scaling_characteristics': {
                'events_per_second': '1,000 - 10,000,000',
                'data_volume': '1 GB - 1 PB per day',
                'scaling_method': 'Automatic (all services auto-scale)'
            }
        }

    def _ml_platform_architecture(self) -> Dict[str, Any]:
        """ML platform architecture with Vertex AI."""
        return {
            'pattern_name': 'ML Platform',
            'description': 'End-to-end machine learning platform',
            'use_case': 'Model training, serving, MLOps, feature engineering',
            'services': {
                'ml_platform': {
                    'service': 'Vertex AI',
                    'purpose': 'Training, tuning, and serving ML models',
                    'configuration': {
                        'training': 'Custom or AutoML training jobs',
                        'prediction': 'Online or batch prediction endpoints',
                        'pipelines': 'Vertex AI Pipelines for MLOps',
                        'feature_store': 'Vertex AI Feature Store'
                    }
                },
                'data': {
                    'service': 'BigQuery',
                    'purpose': 'Feature engineering and data exploration',
                    'configuration': {
                        'ml': 'BigQuery ML for in-warehouse models',
                        'export': 'Export to Cloud Storage for training',
                        'feature_engineering': 'SQL-based transformations'
                    }
                },
                'storage': {
                    'service': 'Cloud Storage',
                    'purpose': 'Datasets, model artifacts, experiment logs',
                    'configuration': {
                        'buckets': 'Separate buckets for data/models/logs',
                        'versioning': 'Enabled for model artifacts',
                        'lifecycle': 'Archive old experiment data'
                    }
                },
                'triggers': {
                    'service': 'Cloud Functions',
                    'purpose': 'Event-driven preprocessing and triggers',
                    'configuration': {
                        'triggers': 'Cloud Storage, Pub/Sub, Scheduler',
                        'preprocessing': 'Data validation and transforms',
                        'notifications': 'Training completion alerts'
                    }
                },
                'monitoring': {
                    'service': 'Vertex AI Model Monitoring',
                    'purpose': 'Detect data drift and model degradation',
                    'configuration': {
                        'skew_detection': 'Training-serving skew alerts',
                        'drift_detection': 'Feature drift monitoring',
                        'alerting': 'Cloud Monitoring integration'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': 200 + (self.data_size_gb * 2),
                'breakdown': {
                    'Vertex AI Training': '50-500 USD (GPU dependent)',
                    'Vertex AI Prediction': '30-200 USD',
                    'BigQuery': '20-100 USD',
                    'Cloud Storage': '10-50 USD',
                    'Cloud Functions': '5-20 USD'
                }
            },
            'pros': [
                'End-to-end ML lifecycle management',
                'AutoML for rapid prototyping',
                'Integrated with BigQuery and Cloud Storage',
                'Managed model serving with autoscaling',
                'Built-in experiment tracking'
            ],
            'cons': [
                'GPU costs can escalate quickly',
                'Vertex AI pricing is complex',
                'Limited customization vs self-managed',
                'Vendor lock-in for model artifacts'
            ],
            'scaling_characteristics': {
                'training': 'Multi-GPU, distributed training',
                'prediction': '1 - 1000+ replicas',
                'scaling_method': 'Automatic endpoint scaling'
            }
        }

    def _multi_region_architecture(self) -> Dict[str, Any]:
        """Multi-region high availability architecture."""
        return {
            'pattern_name': 'Multi-Region High Availability',
            'description': 'Global deployment with disaster recovery',
            'use_case': 'Global applications, 99.99% uptime, compliance',
            'services': {
                'dns': {
                    'service': 'Cloud DNS',
                    'purpose': 'Global DNS with health-checked routing',
                    'configuration': {
                        'routing_policy': 'Geolocation or weighted routing',
                        'health_checks': 'HTTP health checks per region',
                        'failover': 'Automatic DNS failover'
                    }
                },
                'cdn': {
                    'service': 'Cloud CDN',
                    'purpose': 'Edge caching and acceleration',
                    'configuration': {
                        'origins': 'Multiple regional backends',
                        'cache_modes': 'CACHE_ALL_STATIC or USE_ORIGIN_HEADERS',
                        'edge_locations': 'Global (100+ locations)'
                    }
                },
                'compute': {
                    'service': 'Multi-region GKE or Cloud Run',
                    'purpose': 'Active-active deployment across regions',
                    'configuration': {
                        'regions': 'us-central1 (primary), europe-west1 (secondary)',
                        'deployment': 'Cloud Deploy for multi-region rollout',
                        'traffic_split': 'Global Load Balancer with traffic management'
                    }
                },
                'database': {
                    'service': 'Cloud Spanner or Firestore multi-region',
                    'purpose': 'Globally consistent database',
                    'configuration': {
                        'spanner': 'Multi-region config (nam-eur-asia1)',
                        'firestore': 'Multi-region location (nam5, eur3)',
                        'consistency': 'Strong consistency (Spanner) or eventual (Firestore)',
                        'replication': 'Automatic cross-region replication'
                    }
                },
                'storage': {
                    'service': 'Cloud Storage (dual-region or multi-region)',
                    'purpose': 'Geo-redundant object storage',
                    'configuration': {
                        'location': 'Dual-region (us-central1+us-east1) or multi-region (US)',
                        'turbo_replication': '15-minute RPO with turbo replication',
                        'versioning': 'Enabled for critical data'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': self._calculate_gke_cost() * 2.0,
                'breakdown': {
                    'Cloud DNS': '5-15 USD',
                    'Cloud CDN': '20-100 USD',
                    'Compute (2 regions)': '150-500 USD',
                    'Cloud Spanner': '500-2000 USD (multi-region)',
                    'Data transfer (cross-region)': '50-200 USD'
                }
            },
            'pros': [
                'Global low latency',
                'High availability (99.99%+)',
                'Disaster recovery built-in',
                'Data sovereignty compliance',
                'Automatic failover'
            ],
            'cons': [
                '2x+ costs vs single region',
                'Cloud Spanner is expensive',
                'Complex deployment pipeline',
                'Cross-region data transfer costs',
                'Operational overhead'
            ],
            'scaling_characteristics': {
                'users_supported': '100k - 100M',
                'requests_per_second': '10,000 - 10,000,000',
                'scaling_method': 'Per-region auto-scaling + global load balancing'
            }
        }

    def _calculate_serverless_cost(self) -> float:
        """Estimate serverless architecture cost."""
        requests_per_month = self.requests_per_second * 2_592_000
        cloud_run_cost = max(5, (requests_per_month / 1_000_000) * 0.40)
        firestore_cost = max(5, self.data_size_gb * 0.18)
        cdn_cost = max(5, self.expected_users * 0.008)
        storage_cost = max(1, self.data_size_gb * 0.02)

        total = cloud_run_cost + firestore_cost + cdn_cost + storage_cost
        return min(total, self.budget_monthly)

    def _calculate_gke_cost(self) -> float:
        """Estimate GKE microservices architecture cost."""
        gke_management = 74.40  # Autopilot cluster fee
        pod_cost = max(2, self.expected_users // 5000) * 35
        cloud_sql_cost = 120  # db-custom-2-8192 baseline
        memorystore_cost = 35  # Basic 1 GB
        lb_cost = 25

        total = gke_management + pod_cost + cloud_sql_cost + memorystore_cost + lb_cost
        return min(total, self.budget_monthly)

    def _calculate_data_pipeline_cost(self) -> float:
        """Estimate data pipeline cost."""
        pubsub_cost = max(5, self.data_size_gb * 0.5)
        dataflow_cost = max(20, self.data_size_gb * 1.5)
        bigquery_cost = max(10, self.data_size_gb * 0.02 * 6.25)
        storage_cost = self.data_size_gb * 0.02

        total = pubsub_cost + dataflow_cost + bigquery_cost + storage_cost
        return min(total, self.budget_monthly)

    def generate_service_checklist(self) -> list:
        """Generate implementation checklist for recommended architecture."""
        architecture = self.recommend_architecture_pattern()

        checklist = [
            {
                'phase': 'Planning',
                'tasks': [
                    'Review architecture pattern and services',
                    'Estimate costs using GCP Pricing Calculator',
                    'Define environment strategy (dev, staging, prod)',
                    'Set up GCP Organization and projects',
                    'Define labeling strategy for resources'
                ]
            },
            {
                'phase': 'Foundation',
                'tasks': [
                    'Create VPC with subnets (if using GKE/Compute)',
                    'Configure Cloud NAT for private resources',
                    'Set up IAM roles and service accounts',
                    'Enable Cloud Audit Logs',
                    'Configure Organization policies'
                ]
            },
            {
                'phase': 'Core Services',
                'tasks': [
                    f"Deploy {service['service']}"
                    for service in architecture['services'].values()
                ]
            },
            {
                'phase': 'Security',
                'tasks': [
                    'Configure firewall rules and VPC Service Controls',
                    'Enable encryption (Cloud KMS) for all services',
                    'Set up Cloud Armor WAF rules',
                    'Configure Secret Manager for credentials',
                    'Enable Security Command Center'
                ]
            },
            {
                'phase': 'Monitoring',
                'tasks': [
                    'Create Cloud Monitoring dashboards',
                    'Set up alerting policies for critical metrics',
                    'Configure notification channels (email, Slack, PagerDuty)',
                    'Enable Cloud Trace for distributed tracing',
                    'Set up log-based metrics and log sinks'
                ]
            },
            {
                'phase': 'CI/CD',
                'tasks': [
                    'Set up Cloud Build triggers',
                    'Configure automated testing',
                    'Implement canary or rolling deployments',
                    'Set up rollback procedures',
                    'Document deployment process'
                ]
            }
        ]

        return checklist


def main():
    parser = argparse.ArgumentParser(
        description='GCP Architecture Designer - Recommends GCP services based on workload requirements'
    )
    parser.add_argument(
        '--input', '-i',
        type=str,
        help='Path to JSON file with application requirements'
    )
    parser.add_argument(
        '--output', '-o',
        type=str,
        help='Path to write design output JSON'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output as JSON format'
    )
    parser.add_argument(
        '--app-type',
        type=str,
        choices=['web_application', 'mobile_backend', 'data_pipeline',
                 'microservices', 'saas_platform', 'ml_platform'],
        default='web_application',
        help='Application type (default: web_application)'
    )
    parser.add_argument(
        '--users',
        type=int,
        default=1000,
        help='Expected number of users (default: 1000)'
    )
    parser.add_argument(
        '--budget',
        type=float,
        default=500,
        help='Monthly budget in USD (default: 500)'
    )

    args = parser.parse_args()

    if args.input:
        try:
            with open(args.input, 'r') as f:
                requirements = json.load(f)
        except FileNotFoundError:
            print(f"Error: File '{args.input}' not found.", file=sys.stderr)
            sys.exit(1)
        except json.JSONDecodeError:
            print(f"Error: File '{args.input}' is not valid JSON.", file=sys.stderr)
            sys.exit(1)
    else:
        requirements = {
            'application_type': args.app_type,
            'expected_users': args.users,
            'budget_monthly_usd': args.budget
        }

    designer = ArchitectureDesigner(requirements)
    result = designer.recommend_architecture_pattern()
    checklist = designer.generate_service_checklist()

    output = {
        'architecture': result,
        'implementation_checklist': checklist
    }

    if args.output:
        with open(args.output, 'w') as f:
            json.dump(output, f, indent=2)
        print(f"Design written to {args.output}")
    elif args.json:
        print(json.dumps(output, indent=2))
    else:
        print(f"\nRecommended Pattern: {result['pattern_name']}")
        print(f"Description: {result['description']}")
        print(f"Use Case: {result['use_case']}")
        print(f"\nServices:")
        for name, svc in result['services'].items():
            print(f"  - {name}: {svc['service']} ({svc['purpose']})")
        print(f"\nEstimated Monthly Cost: ${result['estimated_cost']['monthly_usd']:.2f}")
        print(f"\nPros: {', '.join(result['pros'])}")
        print(f"Cons: {', '.join(result['cons'])}")


if __name__ == '__main__':
    main()
