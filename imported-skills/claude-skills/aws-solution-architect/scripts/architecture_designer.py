"""
AWS architecture design and service recommendation module.
Generates architecture patterns based on application requirements.
"""

from typing import Dict, List, Any, Optional
from enum import Enum


class ApplicationType(Enum):
    """Types of applications supported."""
    WEB_APP = "web_application"
    MOBILE_BACKEND = "mobile_backend"
    DATA_PIPELINE = "data_pipeline"
    MICROSERVICES = "microservices"
    SAAS_PLATFORM = "saas_platform"
    IOT_PLATFORM = "iot_platform"


class ArchitectureDesigner:
    """Design AWS architectures based on requirements."""

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
        self.aws_experience = requirements.get('aws_experience', 'beginner')
        self.compliance_needs = requirements.get('compliance', [])
        self.data_size_gb = requirements.get('data_size_gb', 10)

    def recommend_architecture_pattern(self) -> Dict[str, Any]:
        """
        Recommend architecture pattern based on requirements.

        Returns:
            Dictionary with recommended pattern and services
        """
        # Determine pattern based on app type and scale
        if self.app_type in ['web_application', 'saas_platform']:
            if self.expected_users < 10000:
                return self._serverless_web_architecture()
            elif self.expected_users < 100000:
                return self._modern_three_tier_architecture()
            else:
                return self._multi_region_architecture()

        elif self.app_type == 'mobile_backend':
            return self._serverless_mobile_backend()

        elif self.app_type == 'data_pipeline':
            return self._event_driven_data_pipeline()

        elif self.app_type == 'microservices':
            return self._event_driven_microservices()

        elif self.app_type == 'iot_platform':
            return self._iot_architecture()

        else:
            return self._serverless_web_architecture()  # Default

    def _serverless_web_architecture(self) -> Dict[str, Any]:
        """Serverless web application pattern."""
        return {
            'pattern_name': 'Serverless Web Application',
            'description': 'Fully serverless architecture with zero server management',
            'use_case': 'SaaS platforms, low to medium traffic websites, MVPs',
            'services': {
                'frontend': {
                    'service': 'S3 + CloudFront',
                    'purpose': 'Static website hosting with global CDN',
                    'configuration': {
                        's3_bucket': 'website-bucket',
                        'cloudfront_distribution': 'HTTPS with custom domain',
                        'caching': 'Cache-Control headers, edge caching'
                    }
                },
                'api': {
                    'service': 'API Gateway + Lambda',
                    'purpose': 'REST API backend with auto-scaling',
                    'configuration': {
                        'api_type': 'REST API',
                        'authorization': 'Cognito User Pools or API Keys',
                        'throttling': f'{self.requests_per_second * 10} requests/second',
                        'lambda_memory': '512 MB (optimize based on testing)',
                        'lambda_timeout': '10 seconds'
                    }
                },
                'database': {
                    'service': 'DynamoDB',
                    'purpose': 'NoSQL database with pay-per-request pricing',
                    'configuration': {
                        'billing_mode': 'PAY_PER_REQUEST',
                        'backup': 'Point-in-time recovery enabled',
                        'encryption': 'KMS encryption at rest'
                    }
                },
                'authentication': {
                    'service': 'Cognito',
                    'purpose': 'User authentication and authorization',
                    'configuration': {
                        'user_pools': 'Email/password + social providers',
                        'mfa': 'Optional MFA with SMS or TOTP',
                        'token_expiration': '1 hour access, 30 days refresh'
                    }
                },
                'cicd': {
                    'service': 'AWS Amplify or CodePipeline',
                    'purpose': 'Automated deployment from Git',
                    'configuration': {
                        'source': 'GitHub or CodeCommit',
                        'build': 'Automatic on commit',
                        'environments': 'dev, staging, production'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': self._calculate_serverless_cost(),
                'breakdown': {
                    'CloudFront': '10-30 USD',
                    'Lambda': '5-20 USD',
                    'API Gateway': '10-40 USD',
                    'DynamoDB': '5-30 USD',
                    'Cognito': '0-10 USD (free tier: 50k MAU)',
                    'S3': '1-5 USD'
                }
            },
            'pros': [
                'No server management',
                'Auto-scaling built-in',
                'Pay only for what you use',
                'Fast to deploy and iterate',
                'High availability by default'
            ],
            'cons': [
                'Cold start latency (100-500ms)',
                'Vendor lock-in to AWS',
                'Debugging distributed systems complex',
                'Learning curve for serverless patterns'
            ],
            'scaling_characteristics': {
                'users_supported': '1k - 100k',
                'requests_per_second': '100 - 10,000',
                'scaling_method': 'Automatic (Lambda concurrency)'
            }
        }

    def _modern_three_tier_architecture(self) -> Dict[str, Any]:
        """Traditional three-tier with modern AWS services."""
        return {
            'pattern_name': 'Modern Three-Tier Application',
            'description': 'Classic architecture with containers and managed services',
            'use_case': 'Traditional web apps, e-commerce, content management',
            'services': {
                'load_balancer': {
                    'service': 'Application Load Balancer (ALB)',
                    'purpose': 'Distribute traffic across instances',
                    'configuration': {
                        'scheme': 'internet-facing',
                        'target_type': 'ECS tasks or EC2 instances',
                        'health_checks': '/health endpoint, 30s interval',
                        'ssl': 'ACM certificate for HTTPS'
                    }
                },
                'compute': {
                    'service': 'ECS Fargate or EC2 Auto Scaling',
                    'purpose': 'Run containerized applications',
                    'configuration': {
                        'container_platform': 'ECS Fargate (serverless containers)',
                        'task_definition': '512 MB memory, 0.25 vCPU (start small)',
                        'auto_scaling': f'2-{max(4, self.expected_users // 5000)} tasks',
                        'deployment': 'Rolling update, 50% at a time'
                    }
                },
                'database': {
                    'service': 'RDS Aurora (MySQL/PostgreSQL)',
                    'purpose': 'Managed relational database',
                    'configuration': {
                        'instance_class': 'db.t3.medium or db.t4g.medium',
                        'multi_az': 'Yes (high availability)',
                        'read_replicas': '1-2 for read scaling',
                        'backup_retention': '7 days',
                        'encryption': 'KMS encryption enabled'
                    }
                },
                'cache': {
                    'service': 'ElastiCache Redis',
                    'purpose': 'Session storage, application caching',
                    'configuration': {
                        'node_type': 'cache.t3.micro or cache.t4g.micro',
                        'replication': 'Multi-AZ with automatic failover',
                        'eviction_policy': 'allkeys-lru'
                    }
                },
                'cdn': {
                    'service': 'CloudFront',
                    'purpose': 'Cache static assets globally',
                    'configuration': {
                        'origins': 'ALB (dynamic), S3 (static)',
                        'caching': 'Cache based on headers/cookies',
                        'compression': 'Gzip compression enabled'
                    }
                },
                'storage': {
                    'service': 'S3',
                    'purpose': 'User uploads, backups, logs',
                    'configuration': {
                        'storage_class': 'S3 Standard with lifecycle policies',
                        'versioning': 'Enabled for important buckets',
                        'lifecycle': 'Transition to IA after 30 days'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': self._calculate_three_tier_cost(),
                'breakdown': {
                    'ALB': '20-30 USD',
                    'ECS Fargate': '50-200 USD',
                    'RDS Aurora': '100-300 USD',
                    'ElastiCache': '30-80 USD',
                    'CloudFront': '10-50 USD',
                    'S3': '10-30 USD'
                }
            },
            'pros': [
                'Proven architecture pattern',
                'Easy to understand and debug',
                'Flexible scaling options',
                'Support for complex applications',
                'Managed services reduce operational burden'
            ],
            'cons': [
                'Higher baseline costs',
                'More complex than serverless',
                'Requires more operational knowledge',
                'Manual scaling configuration needed'
            ],
            'scaling_characteristics': {
                'users_supported': '10k - 500k',
                'requests_per_second': '1,000 - 50,000',
                'scaling_method': 'Auto Scaling based on CPU/memory/requests'
            }
        }

    def _serverless_mobile_backend(self) -> Dict[str, Any]:
        """Serverless mobile backend with GraphQL."""
        return {
            'pattern_name': 'Serverless Mobile Backend',
            'description': 'Mobile-first backend with GraphQL and real-time features',
            'use_case': 'Mobile apps, single-page apps, offline-first applications',
            'services': {
                'api': {
                    'service': 'AppSync (GraphQL)',
                    'purpose': 'Flexible GraphQL API with real-time subscriptions',
                    'configuration': {
                        'api_type': 'GraphQL',
                        'authorization': 'Cognito User Pools + API Keys',
                        'resolvers': 'Direct DynamoDB or Lambda',
                        'subscriptions': 'WebSocket for real-time updates',
                        'caching': 'Server-side caching (1 hour TTL)'
                    }
                },
                'database': {
                    'service': 'DynamoDB',
                    'purpose': 'Fast NoSQL database with global tables',
                    'configuration': {
                        'billing_mode': 'PAY_PER_REQUEST (on-demand)',
                        'global_tables': 'Multi-region if needed',
                        'streams': 'Enabled for change data capture',
                        'ttl': 'Automatic expiration for temporary data'
                    }
                },
                'file_storage': {
                    'service': 'S3 + CloudFront',
                    'purpose': 'User uploads (images, videos, documents)',
                    'configuration': {
                        'access': 'Signed URLs or Cognito credentials',
                        'lifecycle': 'Intelligent-Tiering for cost optimization',
                        'cdn': 'CloudFront for fast global delivery'
                    }
                },
                'authentication': {
                    'service': 'Cognito',
                    'purpose': 'User management and federation',
                    'configuration': {
                        'identity_providers': 'Email, Google, Apple, Facebook',
                        'mfa': 'SMS or TOTP',
                        'groups': 'Admin, premium, free tiers',
                        'custom_attributes': 'User metadata storage'
                    }
                },
                'push_notifications': {
                    'service': 'SNS Mobile Push',
                    'purpose': 'Push notifications to mobile devices',
                    'configuration': {
                        'platforms': 'iOS (APNs), Android (FCM)',
                        'topics': 'Group notifications by topic',
                        'delivery_status': 'CloudWatch Logs for tracking'
                    }
                },
                'analytics': {
                    'service': 'Pinpoint',
                    'purpose': 'User analytics and engagement',
                    'configuration': {
                        'events': 'Custom events tracking',
                        'campaigns': 'Targeted messaging',
                        'segments': 'User segmentation'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': 50 + (self.expected_users * 0.005),
                'breakdown': {
                    'AppSync': '5-40 USD',
                    'DynamoDB': '10-50 USD',
                    'Cognito': '0-15 USD',
                    'S3 + CloudFront': '10-40 USD',
                    'SNS': '1-10 USD',
                    'Pinpoint': '10-30 USD'
                }
            },
            'pros': [
                'Single GraphQL endpoint',
                'Real-time subscriptions built-in',
                'Offline-first capabilities',
                'Auto-generated mobile SDK',
                'Flexible querying (no over/under fetching)'
            ],
            'cons': [
                'GraphQL learning curve',
                'Complex queries can be expensive',
                'Debugging subscriptions challenging',
                'Limited to AWS AppSync features'
            ],
            'scaling_characteristics': {
                'users_supported': '1k - 1M',
                'requests_per_second': '100 - 100,000',
                'scaling_method': 'Automatic (AppSync managed)'
            }
        }

    def _event_driven_microservices(self) -> Dict[str, Any]:
        """Event-driven microservices architecture."""
        return {
            'pattern_name': 'Event-Driven Microservices',
            'description': 'Loosely coupled services with event bus',
            'use_case': 'Complex business workflows, asynchronous processing',
            'services': {
                'event_bus': {
                    'service': 'EventBridge',
                    'purpose': 'Central event routing between services',
                    'configuration': {
                        'bus_type': 'Custom event bus',
                        'rules': 'Route events by type/source',
                        'targets': 'Lambda, SQS, Step Functions',
                        'archive': 'Event replay capability'
                    }
                },
                'compute': {
                    'service': 'Lambda + ECS Fargate (hybrid)',
                    'purpose': 'Service implementation',
                    'configuration': {
                        'lambda': 'Lightweight services, event handlers',
                        'fargate': 'Long-running services, heavy processing',
                        'auto_scaling': 'Lambda (automatic), Fargate (target tracking)'
                    }
                },
                'queues': {
                    'service': 'SQS',
                    'purpose': 'Decouple services, handle failures',
                    'configuration': {
                        'queue_type': 'Standard (high throughput) or FIFO (ordering)',
                        'dlq': 'Dead letter queue after 3 retries',
                        'visibility_timeout': '30 seconds (adjust per service)',
                        'retention': '4 days'
                    }
                },
                'orchestration': {
                    'service': 'Step Functions',
                    'purpose': 'Complex workflows, saga patterns',
                    'configuration': {
                        'type': 'Standard (long-running) or Express (high volume)',
                        'error_handling': 'Retry, catch, rollback logic',
                        'timeouts': 'Per-state timeouts',
                        'logging': 'CloudWatch Logs integration'
                    }
                },
                'database': {
                    'service': 'DynamoDB (per service)',
                    'purpose': 'Each microservice owns its data',
                    'configuration': {
                        'pattern': 'Database per service',
                        'streams': 'DynamoDB Streams for change events',
                        'backup': 'Point-in-time recovery'
                    }
                },
                'api_gateway': {
                    'service': 'API Gateway',
                    'purpose': 'Unified API facade',
                    'configuration': {
                        'integration': 'Lambda proxy or HTTP proxy',
                        'authentication': 'Cognito or Lambda authorizer',
                        'rate_limiting': 'Per-client throttling'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': 100 + (self.expected_users * 0.01),
                'breakdown': {
                    'EventBridge': '5-20 USD',
                    'Lambda': '20-100 USD',
                    'SQS': '1-10 USD',
                    'Step Functions': '10-50 USD',
                    'DynamoDB': '30-150 USD',
                    'API Gateway': '10-40 USD'
                }
            },
            'pros': [
                'Loose coupling between services',
                'Independent scaling and deployment',
                'Failure isolation',
                'Technology diversity possible',
                'Easy to test individual services'
            ],
            'cons': [
                'Operational complexity',
                'Distributed tracing required',
                'Eventual consistency challenges',
                'Network latency between services',
                'More moving parts to monitor'
            ],
            'scaling_characteristics': {
                'users_supported': '10k - 10M',
                'requests_per_second': '1,000 - 1,000,000',
                'scaling_method': 'Per-service auto-scaling'
            }
        }

    def _event_driven_data_pipeline(self) -> Dict[str, Any]:
        """Real-time data processing pipeline."""
        return {
            'pattern_name': 'Real-Time Data Pipeline',
            'description': 'Scalable data ingestion and processing',
            'use_case': 'Analytics, IoT data, log processing, ETL',
            'services': {
                'ingestion': {
                    'service': 'Kinesis Data Streams',
                    'purpose': 'Real-time data ingestion',
                    'configuration': {
                        'shards': f'{max(1, self.data_size_gb // 10)} shards',
                        'retention': '24 hours (extend to 7 days if needed)',
                        'encryption': 'KMS encryption'
                    }
                },
                'processing': {
                    'service': 'Lambda or Kinesis Analytics',
                    'purpose': 'Transform and enrich data',
                    'configuration': {
                        'lambda_concurrency': 'Match shard count',
                        'batch_size': '100-500 records per invocation',
                        'error_handling': 'DLQ for failed records'
                    }
                },
                'storage': {
                    'service': 'S3 Data Lake',
                    'purpose': 'Long-term storage and analytics',
                    'configuration': {
                        'format': 'Parquet (compressed, columnar)',
                        'partitioning': 'By date (year/month/day/hour)',
                        'lifecycle': 'Transition to Glacier after 90 days',
                        'catalog': 'AWS Glue Data Catalog'
                    }
                },
                'analytics': {
                    'service': 'Athena',
                    'purpose': 'SQL queries on S3 data',
                    'configuration': {
                        'query_results': 'Store in separate S3 bucket',
                        'workgroups': 'Separate dev and prod',
                        'cost_controls': 'Query limits per workgroup'
                    }
                },
                'visualization': {
                    'service': 'QuickSight',
                    'purpose': 'Business intelligence dashboards',
                    'configuration': {
                        'source': 'Athena or direct S3',
                        'refresh': 'Hourly or daily',
                        'sharing': 'Embedded dashboards or web access'
                    }
                },
                'alerting': {
                    'service': 'CloudWatch + SNS',
                    'purpose': 'Monitor metrics and alerts',
                    'configuration': {
                        'metrics': 'Custom metrics from processing',
                        'alarms': 'Threshold-based alerts',
                        'notifications': 'Email, Slack, PagerDuty'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': self._calculate_data_pipeline_cost(),
                'breakdown': {
                    'Kinesis': '15-100 USD (per shard)',
                    'Lambda': '10-50 USD',
                    'S3': '10-50 USD',
                    'Athena': '5-30 USD (per TB scanned)',
                    'QuickSight': '9-18 USD per user',
                    'Glue': '5-20 USD'
                }
            },
            'pros': [
                'Real-time processing capability',
                'Scales to millions of events',
                'Cost-effective long-term storage',
                'SQL analytics on raw data',
                'Serverless architecture'
            ],
            'cons': [
                'Kinesis shard management required',
                'Athena costs based on data scanned',
                'Schema evolution complexity',
                'Cold data queries can be slow'
            ],
            'scaling_characteristics': {
                'events_per_second': '1,000 - 1,000,000',
                'data_volume': '1 GB - 1 PB per day',
                'scaling_method': 'Add Kinesis shards, partition S3 data'
            }
        }

    def _iot_architecture(self) -> Dict[str, Any]:
        """IoT platform architecture."""
        return {
            'pattern_name': 'IoT Platform',
            'description': 'Scalable IoT device management and data processing',
            'use_case': 'Connected devices, sensors, smart devices',
            'services': {
                'device_management': {
                    'service': 'IoT Core',
                    'purpose': 'Device connectivity and management',
                    'configuration': {
                        'protocol': 'MQTT over TLS',
                        'thing_registry': 'Device metadata storage',
                        'device_shadow': 'Desired and reported state',
                        'rules_engine': 'Route messages to services'
                    }
                },
                'device_provisioning': {
                    'service': 'IoT Device Management',
                    'purpose': 'Fleet provisioning and updates',
                    'configuration': {
                        'fleet_indexing': 'Search devices',
                        'jobs': 'OTA firmware updates',
                        'bulk_operations': 'Manage device groups'
                    }
                },
                'data_processing': {
                    'service': 'IoT Analytics',
                    'purpose': 'Process and analyze IoT data',
                    'configuration': {
                        'channels': 'Ingest device data',
                        'pipelines': 'Transform and enrich',
                        'data_store': 'Time-series storage',
                        'notebooks': 'Jupyter notebooks for analysis'
                    }
                },
                'time_series_db': {
                    'service': 'Timestream',
                    'purpose': 'Store time-series metrics',
                    'configuration': {
                        'memory_store': 'Recent data (hours)',
                        'magnetic_store': 'Historical data (years)',
                        'retention': 'Auto-tier based on age'
                    }
                },
                'real_time_alerts': {
                    'service': 'IoT Events',
                    'purpose': 'Detect and respond to events',
                    'configuration': {
                        'detector_models': 'Define alert conditions',
                        'actions': 'SNS, Lambda, SQS',
                        'state_tracking': 'Per-device state machines'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': 50 + (self.expected_users * 0.1),  # Expected_users = device count
                'breakdown': {
                    'IoT Core': '10-100 USD (per million messages)',
                    'IoT Analytics': '5-50 USD',
                    'Timestream': '10-80 USD',
                    'IoT Events': '1-20 USD',
                    'Data transfer': '10-50 USD'
                }
            },
            'pros': [
                'Built for IoT scale',
                'Secure device connectivity',
                'Managed device lifecycle',
                'Time-series optimized',
                'Real-time event detection'
            ],
            'cons': [
                'IoT-specific pricing model',
                'MQTT protocol required',
                'Regional limitations',
                'Complexity for simple use cases'
            ],
            'scaling_characteristics': {
                'devices_supported': '100 - 10,000,000',
                'messages_per_second': '1,000 - 100,000',
                'scaling_method': 'Automatic (managed service)'
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
                    'service': 'Route 53',
                    'purpose': 'Global traffic routing',
                    'configuration': {
                        'routing_policy': 'Geolocation or latency-based',
                        'health_checks': 'Active monitoring with failover',
                        'failover': 'Automatic to secondary region'
                    }
                },
                'cdn': {
                    'service': 'CloudFront',
                    'purpose': 'Edge caching and acceleration',
                    'configuration': {
                        'origins': 'Multiple regions (primary + secondary)',
                        'origin_failover': 'Automatic failover',
                        'edge_locations': 'Global (400+ locations)'
                    }
                },
                'compute': {
                    'service': 'Multi-region Lambda or ECS',
                    'purpose': 'Active-active deployment',
                    'configuration': {
                        'regions': 'us-east-1 (primary), eu-west-1 (secondary)',
                        'deployment': 'Blue/Green in each region',
                        'traffic_split': '70/30 or 50/50'
                    }
                },
                'database': {
                    'service': 'DynamoDB Global Tables or Aurora Global',
                    'purpose': 'Multi-region replication',
                    'configuration': {
                        'replication': 'Sub-second replication lag',
                        'read_locality': 'Read from nearest region',
                        'write_forwarding': 'Aurora Global write forwarding',
                        'conflict_resolution': 'Last writer wins'
                    }
                },
                'storage': {
                    'service': 'S3 Cross-Region Replication',
                    'purpose': 'Replicate data across regions',
                    'configuration': {
                        'replication': 'Async replication to secondary',
                        'versioning': 'Required for CRR',
                        'replication_time_control': '15 minutes SLA'
                    }
                }
            },
            'estimated_cost': {
                'monthly_usd': self._calculate_three_tier_cost() * 1.8,
                'breakdown': {
                    'Route 53': '10-30 USD',
                    'CloudFront': '20-100 USD',
                    'Compute (2 regions)': '100-500 USD',
                    'Database (Global Tables)': '200-800 USD',
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
                '1.5-2x costs vs single region',
                'Complex deployment pipeline',
                'Data consistency challenges',
                'More operational overhead',
                'Cross-region data transfer costs'
            ],
            'scaling_characteristics': {
                'users_supported': '100k - 100M',
                'requests_per_second': '10,000 - 10,000,000',
                'scaling_method': 'Per-region auto-scaling + global routing'
            }
        }

    def _calculate_serverless_cost(self) -> float:
        """Estimate serverless architecture cost."""
        requests_per_month = self.requests_per_second * 2_592_000  # 30 days
        lambda_cost = (requests_per_month / 1_000_000) * 0.20  # $0.20 per 1M requests
        api_gateway_cost = (requests_per_month / 1_000_000) * 3.50  # $3.50 per 1M requests
        dynamodb_cost = max(5, self.data_size_gb * 0.25)  # $0.25 per GB/month
        cloudfront_cost = max(10, self.expected_users * 0.01)

        total = lambda_cost + api_gateway_cost + dynamodb_cost + cloudfront_cost
        return min(total, self.budget_monthly)  # Cap at budget

    def _calculate_three_tier_cost(self) -> float:
        """Estimate three-tier architecture cost."""
        fargate_tasks = max(2, self.expected_users // 5000)
        fargate_cost = fargate_tasks * 30  # ~$30 per task/month
        rds_cost = 150  # db.t3.medium baseline
        elasticache_cost = 40  # cache.t3.micro
        alb_cost = 25

        total = fargate_cost + rds_cost + elasticache_cost + alb_cost
        return min(total, self.budget_monthly)

    def _calculate_data_pipeline_cost(self) -> float:
        """Estimate data pipeline cost."""
        shards = max(1, self.data_size_gb // 10)
        kinesis_cost = shards * 15  # $15 per shard/month
        s3_cost = self.data_size_gb * 0.023  # $0.023 per GB/month
        lambda_cost = 20  # Processing
        athena_cost = 15  # Queries

        total = kinesis_cost + s3_cost + lambda_cost + athena_cost
        return min(total, self.budget_monthly)

    def generate_service_checklist(self) -> List[Dict[str, Any]]:
        """Generate implementation checklist for recommended architecture."""
        architecture = self.recommend_architecture_pattern()

        checklist = [
            {
                'phase': 'Planning',
                'tasks': [
                    'Review architecture pattern and services',
                    'Estimate costs using AWS Pricing Calculator',
                    'Define environment strategy (dev, staging, prod)',
                    'Set up AWS Organization and accounts',
                    'Define tagging strategy for resources'
                ]
            },
            {
                'phase': 'Foundation',
                'tasks': [
                    'Create VPC with public/private subnets',
                    'Configure NAT Gateway or VPC endpoints',
                    'Set up IAM roles and policies',
                    'Enable CloudTrail for audit logging',
                    'Configure AWS Config for compliance'
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
                    'Configure security groups and NACLs',
                    'Enable encryption (KMS) for all services',
                    'Set up AWS WAF rules',
                    'Configure Secrets Manager',
                    'Enable GuardDuty for threat detection'
                ]
            },
            {
                'phase': 'Monitoring',
                'tasks': [
                    'Create CloudWatch dashboards',
                    'Set up alarms for critical metrics',
                    'Configure SNS topics for notifications',
                    'Enable X-Ray for distributed tracing',
                    'Set up log aggregation and retention'
                ]
            },
            {
                'phase': 'CI/CD',
                'tasks': [
                    'Set up CodePipeline or GitHub Actions',
                    'Configure automated testing',
                    'Implement blue/green deployment',
                    'Set up rollback procedures',
                    'Document deployment process'
                ]
            }
        ]

        return checklist
