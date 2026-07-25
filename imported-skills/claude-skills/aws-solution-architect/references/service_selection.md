# AWS Service Selection Guide

Quick reference for choosing the right AWS service based on requirements.

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
| Event-driven, short tasks (<15 min) | Lambda |
| Containerized apps, predictable traffic | ECS Fargate |
| Custom configs, GPU/FPGA | EC2 |
| Simple container from source | App Runner |
| Kubernetes workloads | EKS |
| Batch processing | AWS Batch |

### Lambda

**Best for:** Event-driven functions, API backends, scheduled tasks

```
Limits:
- Execution: 15 minutes max
- Memory: 128 MB - 10 GB
- Package: 50 MB (zip), 10 GB (container)
- Concurrency: 1000 default (soft limit)

Pricing: $0.20 per 1M requests + compute time
```

**Use when:**
- Variable/unpredictable traffic
- Pay-per-use is important
- No server management desired
- Short-duration operations

**Avoid when:**
- Long-running processes (>15 min)
- Low-latency requirements (<50ms)
- Heavy compute (consider Fargate)

### ECS Fargate

**Best for:** Containerized applications, microservices

```
Limits:
- vCPU: 0.25 - 16
- Memory: 0.5 GB - 120 GB
- Storage: 20 GB - 200 GB ephemeral

Pricing: Per vCPU-hour + GB-hour
```

**Use when:**
- Containerized applications
- Predictable traffic patterns
- Long-running processes
- Need more control than Lambda

### EC2

**Best for:** Custom configurations, specialized hardware

```
Instance Types:
- General: t3, m6i
- Compute: c6i
- Memory: r6i
- GPU: p4d, g5
- Storage: i3, d3
```

**Use when:**
- Need GPU/FPGA
- Windows applications
- Specific instance configurations
- Reserved capacity makes sense

---

## Database Services

### Decision Matrix

| Data Type | Query Pattern | Scale | Recommended |
|-----------|--------------|-------|-------------|
| Key-value | Simple lookups | Any | DynamoDB |
| Document | Flexible queries | <1TB | DocumentDB |
| Relational | Complex joins | Variable | Aurora Serverless |
| Relational | High volume | Fixed | Aurora Standard |
| Time-series | Time-based | Any | Timestream |
| Graph | Relationships | Any | Neptune |

### DynamoDB

**Best for:** Key-value and document data, serverless applications

```
Limits:
- Item size: 400 KB max
- Partition key: 2048 bytes
- Sort key: 1024 bytes
- GSI: 20 per table

Pricing:
- On-demand: $1.25 per million writes, $0.25 per million reads
- Provisioned: Per RCU/WCU
```

**Data Modeling Example:**

```
# Single-table design for e-commerce
PK                  SK                  Attributes
USER#123            PROFILE             {name, email, ...}
USER#123            ORDER#456           {total, status, ...}
USER#123            ORDER#456#ITEM#1    {product, qty, ...}
PRODUCT#789         METADATA            {name, price, ...}
```

### Aurora

**Best for:** Relational data with complex queries

| Edition | Use Case | Scaling |
|---------|----------|---------|
| Aurora Serverless v2 | Variable workloads | 0.5-128 ACUs, auto |
| Aurora Standard | Predictable workloads | Instance-based |
| Aurora Global | Multi-region | Cross-region replication |

```
Limits:
- Storage: 128 TB max
- Replicas: 15 read replicas
- Connections: Instance-dependent

Pricing:
- Serverless: $0.12 per ACU-hour
- Standard: Instance + storage + I/O
```

### Comparison: DynamoDB vs Aurora

| Factor | DynamoDB | Aurora |
|--------|----------|--------|
| Query flexibility | Limited (key-based) | Full SQL |
| Scaling | Instant, unlimited | Minutes, up to limits |
| Consistency | Eventually/Strong | ACID |
| Cost model | Per-request | Per-hour |
| Operational | Zero management | Some management |

---

## Storage Services

### S3 Storage Classes

| Class | Access Pattern | Retrieval | Cost (GB/mo) |
|-------|---------------|-----------|--------------|
| Standard | Frequent | Instant | $0.023 |
| Intelligent-Tiering | Unknown | Instant | $0.023 + monitoring |
| Standard-IA | Infrequent (30+ days) | Instant | $0.0125 |
| One Zone-IA | Infrequent, single AZ | Instant | $0.01 |
| Glacier Instant | Archive, instant access | Instant | $0.004 |
| Glacier Flexible | Archive | Minutes-hours | $0.0036 |
| Glacier Deep Archive | Long-term archive | 12-48 hours | $0.00099 |

### Lifecycle Policy Example

```json
{
  "Rules": [
    {
      "ID": "Archive old data",
      "Status": "Enabled",
      "Transitions": [
        {
          "Days": 30,
          "StorageClass": "STANDARD_IA"
        },
        {
          "Days": 90,
          "StorageClass": "GLACIER"
        },
        {
          "Days": 365,
          "StorageClass": "DEEP_ARCHIVE"
        }
      ],
      "Expiration": {
        "Days": 2555
      }
    }
  ]
}
```

### Block and File Storage

| Service | Use Case | Access |
|---------|----------|--------|
| EBS | EC2 block storage | Single instance |
| EFS | Shared file system | Multiple instances |
| FSx for Lustre | HPC workloads | High throughput |
| FSx for Windows | Windows apps | SMB protocol |

---

## Messaging and Events

### Decision Matrix

| Pattern | Service | Use Case |
|---------|---------|----------|
| Event routing | EventBridge | Microservices, SaaS integration |
| Pub/sub | SNS | Fan-out notifications |
| Queue | SQS | Decoupling, buffering |
| Streaming | Kinesis | Real-time analytics |
| Message broker | Amazon MQ | Legacy migrations |

### EventBridge

**Best for:** Event-driven architectures, SaaS integration

```python
# EventBridge rule pattern
{
    "source": ["orders.service"],
    "detail-type": ["OrderCreated"],
    "detail": {
        "total": [{"numeric": [">=", 100]}]
    }
}
```

### SQS

**Best for:** Decoupling services, handling load spikes

| Feature | Standard | FIFO |
|---------|----------|------|
| Throughput | Unlimited | 3000 msg/sec |
| Ordering | Best effort | Guaranteed |
| Delivery | At least once | Exactly once |
| Deduplication | No | Yes |

```python
# SQS with dead letter queue
import boto3

sqs = boto3.client('sqs')

def process_with_dlq(queue_url, dlq_url, max_retries=3):
    response = sqs.receive_message(
        QueueUrl=queue_url,
        MaxNumberOfMessages=10,
        WaitTimeSeconds=20,
        AttributeNames=['ApproximateReceiveCount']
    )

    for message in response.get('Messages', []):
        receive_count = int(message['Attributes']['ApproximateReceiveCount'])

        try:
            process(message)
            sqs.delete_message(QueueUrl=queue_url, ReceiptHandle=message['ReceiptHandle'])
        except Exception as e:
            if receive_count >= max_retries:
                sqs.send_message(QueueUrl=dlq_url, MessageBody=message['Body'])
                sqs.delete_message(QueueUrl=queue_url, ReceiptHandle=message['ReceiptHandle'])
```

### Kinesis

**Best for:** Real-time streaming data, analytics

| Service | Use Case |
|---------|----------|
| Data Streams | Custom processing |
| Data Firehose | Direct to S3/Redshift |
| Data Analytics | SQL on streams |
| Video Streams | Video ingestion |

---

## API and Integration

### API Gateway vs AppSync

| Factor | API Gateway | AppSync |
|--------|-------------|---------|
| Protocol | REST, WebSocket | GraphQL |
| Real-time | WebSocket setup | Built-in subscriptions |
| Caching | Response caching | Field-level caching |
| Integration | Lambda, HTTP, AWS | Lambda, DynamoDB, HTTP |
| Pricing | Per request | Per request + data |

### API Gateway Configuration

```yaml
# Throttling and caching
Resources:
  ApiGateway:
    Type: AWS::ApiGateway::RestApi
    Properties:
      Name: my-api

  ApiStage:
    Type: AWS::ApiGateway::Stage
    Properties:
      StageName: prod
      MethodSettings:
        - HttpMethod: "*"
          ResourcePath: "/*"
          ThrottlingBurstLimit: 500
          ThrottlingRateLimit: 1000
          CachingEnabled: true
          CacheTtlInSeconds: 300
```

### Step Functions

**Best for:** Workflow orchestration, long-running processes

```json
{
  "StartAt": "ProcessOrder",
  "States": {
    "ProcessOrder": {
      "Type": "Task",
      "Resource": "arn:aws:lambda:...:processOrder",
      "Next": "CheckInventory"
    },
    "CheckInventory": {
      "Type": "Choice",
      "Choices": [
        {
          "Variable": "$.inStock",
          "BooleanEquals": true,
          "Next": "ShipOrder"
        }
      ],
      "Default": "BackOrder"
    },
    "ShipOrder": {
      "Type": "Task",
      "Resource": "arn:aws:lambda:...:shipOrder",
      "End": true
    },
    "BackOrder": {
      "Type": "Task",
      "Resource": "arn:aws:lambda:...:backOrder",
      "End": true
    }
  }
}
```

---

## Networking

### VPC Components

| Component | Purpose |
|-----------|---------|
| VPC | Isolated network |
| Subnet | Network segment (public/private) |
| Internet Gateway | Public internet access |
| NAT Gateway | Private subnet outbound |
| VPC Endpoint | Private AWS service access |
| Transit Gateway | VPC interconnection |

### VPC Design Pattern

```
VPC: 10.0.0.0/16

Public Subnets (AZ a, b, c):
  10.0.1.0/24, 10.0.2.0/24, 10.0.3.0/24
  - ALB, NAT Gateway, Bastion

Private Subnets (AZ a, b, c):
  10.0.11.0/24, 10.0.12.0/24, 10.0.13.0/24
  - Application servers, Lambda

Database Subnets (AZ a, b, c):
  10.0.21.0/24, 10.0.22.0/24, 10.0.23.0/24
  - RDS, ElastiCache
```

### VPC Endpoints (Cost Savings)

```yaml
# Interface endpoint for Secrets Manager
SecretsManagerEndpoint:
  Type: AWS::EC2::VPCEndpoint
  Properties:
    VpcId: !Ref VPC
    ServiceName: !Sub com.amazonaws.${AWS::Region}.secretsmanager
    VpcEndpointType: Interface
    SubnetIds: !Ref PrivateSubnets
    SecurityGroupIds:
      - !Ref EndpointSecurityGroup
```

---

## Security and Identity

### IAM Best Practices

```json
// Least privilege policy example
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Effect": "Allow",
      "Action": [
        "dynamodb:GetItem",
        "dynamodb:PutItem",
        "dynamodb:Query"
      ],
      "Resource": "arn:aws:dynamodb:us-east-1:123456789:table/users",
      "Condition": {
        "ForAllValues:StringEquals": {
          "dynamodb:LeadingKeys": ["${aws:userid}"]
        }
      }
    }
  ]
}
```

### Secrets Manager vs Parameter Store

| Factor | Secrets Manager | Parameter Store |
|--------|-----------------|-----------------|
| Auto-rotation | Built-in | Manual |
| Cross-account | Yes | Limited |
| Pricing | $0.40/secret/month | Free (standard) |
| Use case | Credentials, API keys | Config, non-secrets |

### Cognito Configuration

```yaml
UserPool:
  Type: AWS::Cognito::UserPool
  Properties:
    UserPoolName: my-app-users
    AutoVerifiedAttributes:
      - email
    MfaConfiguration: OPTIONAL
    EnabledMfas:
      - SOFTWARE_TOKEN_MFA
    Policies:
      PasswordPolicy:
        MinimumLength: 12
        RequireLowercase: true
        RequireUppercase: true
        RequireNumbers: true
        RequireSymbols: true
    AccountRecoverySetting:
      RecoveryMechanisms:
        - Name: verified_email
          Priority: 1
```
