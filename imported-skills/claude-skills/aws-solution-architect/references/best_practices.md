# AWS Best Practices for Startups

Production-ready practices for serverless, cost optimization, security, and operational excellence.

---

## Table of Contents

- [Serverless Best Practices](#serverless-best-practices)
- [Cost Optimization](#cost-optimization)
- [Security Hardening](#security-hardening)
- [Scalability Patterns](#scalability-patterns)
- [DevOps and Reliability](#devops-and-reliability)
- [Common Pitfalls](#common-pitfalls)

---

## Serverless Best Practices

### Lambda Function Design

#### 1. Keep Functions Stateless

Store state externally in DynamoDB, S3, or ElastiCache.

```python
# BAD: Function-level state
cache = {}

def handler(event, context):
    if event['key'] in cache:
        return cache[event['key']]
    # ...

# GOOD: External state
import boto3
dynamodb = boto3.resource('dynamodb')
table = dynamodb.Table('cache')

def handler(event, context):
    response = table.get_item(Key={'pk': event['key']})
    if 'Item' in response:
        return response['Item']['value']
    # ...
```

#### 2. Implement Idempotency

Handle retries gracefully with unique request IDs.

```python
import boto3
import hashlib

dynamodb = boto3.resource('dynamodb')
idempotency_table = dynamodb.Table('idempotency')

def handler(event, context):
    # Generate idempotency key
    idempotency_key = hashlib.sha256(
        f"{event['orderId']}-{event['action']}".encode()
    ).hexdigest()

    # Check if already processed
    try:
        response = idempotency_table.get_item(Key={'pk': idempotency_key})
        if 'Item' in response:
            return response['Item']['result']
    except Exception:
        pass

    # Process request
    result = process_order(event)

    # Store result for idempotency
    idempotency_table.put_item(
        Item={
            'pk': idempotency_key,
            'result': result,
            'ttl': int(time.time()) + 86400  # 24h TTL
        }
    )

    return result
```

#### 3. Optimize Cold Starts

```python
# Initialize outside handler (reused across invocations)
import boto3
from aws_xray_sdk.core import patch_all

# SDK initialization happens once
dynamodb = boto3.resource('dynamodb')
table = dynamodb.Table('my-table')
patch_all()

def handler(event, context):
    # Handler code uses pre-initialized resources
    return table.get_item(Key={'pk': event['id']})
```

**Cold Start Reduction Techniques:**
- Use provisioned concurrency for critical paths
- Minimize package size (use layers for dependencies)
- Choose interpreted languages (Python, Node.js) over compiled
- Avoid VPC unless necessary (adds 6-10 sec cold start)

#### 4. Set Appropriate Timeouts

```yaml
# Lambda configuration
Functions:
  ApiHandler:
    Timeout: 10  # Shorter for synchronous APIs
    MemorySize: 512

  BackgroundProcessor:
    Timeout: 300  # Longer for async processing
    MemorySize: 1024
```

**Timeout Guidelines:**
- API handlers: 10-30 seconds
- Event processors: 60-300 seconds
- Use Step Functions for >15 minute workflows

---

## Cost Optimization

### 1. Right-Sizing Strategy

```bash
# Check EC2 utilization
aws cloudwatch get-metric-statistics \
  --namespace AWS/EC2 \
  --metric-name CPUUtilization \
  --dimensions Name=InstanceId,Value=i-1234567890abcdef0 \
  --start-time $(date -d '7 days ago' -u +"%Y-%m-%dT%H:%M:%SZ") \
  --end-time $(date -u +"%Y-%m-%dT%H:%M:%SZ") \
  --period 3600 \
  --statistics Average
```

**Right-Sizing Rules:**
- <10% CPU average: Downsize instance
- >80% CPU average: Consider upgrade or horizontal scaling
- Review every month for the first 6 months

### 2. Savings Plans and Reserved Instances

| Commitment | Savings | Best For |
|------------|---------|----------|
| No Upfront, 1-year | 20-30% | Unknown future |
| Partial Upfront, 1-year | 30-40% | Moderate confidence |
| All Upfront, 3-year | 50-60% | Stable workloads |

```bash
# Check Savings Plans recommendations
aws cost-explorer get-savings-plans-purchase-recommendation \
  --savings-plans-type COMPUTE_SP \
  --term-in-years ONE_YEAR \
  --payment-option NO_UPFRONT \
  --lookback-period-in-days THIRTY_DAYS
```

### 3. S3 Lifecycle Policies

```json
{
  "Rules": [
    {
      "ID": "Transition to cheaper storage",
      "Status": "Enabled",
      "Filter": {
        "Prefix": "logs/"
      },
      "Transitions": [
        { "Days": 30, "StorageClass": "STANDARD_IA" },
        { "Days": 90, "StorageClass": "GLACIER" }
      ],
      "Expiration": { "Days": 365 }
    }
  ]
}
```

### 4. Lambda Memory Optimization

Test different memory settings to find optimal cost/performance.

```python
# Use AWS Lambda Power Tuning
# https://github.com/alexcasalboni/aws-lambda-power-tuning

# Example results:
# 128 MB: 2000ms, $0.000042
# 512 MB: 500ms, $0.000042
# 1024 MB: 300ms, $0.000050

# Optimal: 512 MB (same cost, 4x faster)
```

### 5. NAT Gateway Alternatives

```
NAT Gateway: $0.045/hour + $0.045/GB = ~$32/month + data

Alternatives:
1. VPC Endpoints: $0.01/hour = ~$7.30/month (for AWS services)
2. NAT Instance: t3.nano = ~$3.80/month (limited throughput)
3. No NAT: Use VPC endpoints + Lambda outside VPC
```

### 6. CloudWatch Log Retention

```yaml
# Set retention policies to avoid unbounded growth
LogGroup:
  Type: AWS::Logs::LogGroup
  Properties:
    LogGroupName: /aws/lambda/my-function
    RetentionInDays: 14  # 7, 14, 30, 60, 90, etc.
```

**Retention Guidelines:**
- Development: 7 days
- Production non-critical: 30 days
- Production critical: 90 days
- Compliance requirements: As specified

---

## Security Hardening

### 1. IAM Least Privilege

```json
// BAD: Overly permissive
{
  "Effect": "Allow",
  "Action": "dynamodb:*",
  "Resource": "*"
}

// GOOD: Specific actions and resources
{
  "Effect": "Allow",
  "Action": [
    "dynamodb:GetItem",
    "dynamodb:PutItem",
    "dynamodb:Query"
  ],
  "Resource": [
    "arn:aws:dynamodb:us-east-1:123456789:table/users",
    "arn:aws:dynamodb:us-east-1:123456789:table/users/index/*"
  ]
}
```

### 2. Encryption Configuration

```yaml
# Enable encryption everywhere
Resources:
  # DynamoDB
  Table:
    Type: AWS::DynamoDB::Table
    Properties:
      SSESpecification:
        SSEEnabled: true
        SSEType: KMS
        KMSMasterKeyId: !Ref EncryptionKey

  # S3
  Bucket:
    Type: AWS::S3::Bucket
    Properties:
      BucketEncryption:
        ServerSideEncryptionConfiguration:
          - ServerSideEncryptionByDefault:
              SSEAlgorithm: aws:kms
              KMSMasterKeyID: !Ref EncryptionKey

  # RDS
  Database:
    Type: AWS::RDS::DBInstance
    Properties:
      StorageEncrypted: true
      KmsKeyId: !Ref EncryptionKey
```

### 3. Network Isolation

```yaml
# Private subnets with VPC endpoints
Resources:
  PrivateSubnet:
    Type: AWS::EC2::Subnet
    Properties:
      MapPublicIpOnLaunch: false

  # DynamoDB Gateway Endpoint (free)
  DynamoDBEndpoint:
    Type: AWS::EC2::VPCEndpoint
    Properties:
      VpcId: !Ref VPC
      ServiceName: !Sub com.amazonaws.${AWS::Region}.dynamodb
      VpcEndpointType: Gateway
      RouteTableIds:
        - !Ref PrivateRouteTable

  # Secrets Manager Interface Endpoint
  SecretsEndpoint:
    Type: AWS::EC2::VPCEndpoint
    Properties:
      VpcId: !Ref VPC
      ServiceName: !Sub com.amazonaws.${AWS::Region}.secretsmanager
      VpcEndpointType: Interface
      PrivateDnsEnabled: true
```

### 4. Secrets Management

```python
# Never hardcode secrets
import boto3
import json

def get_secret(secret_name):
    client = boto3.client('secretsmanager')
    response = client.get_secret_value(SecretId=secret_name)
    return json.loads(response['SecretString'])

# Usage
db_creds = get_secret('prod/database/credentials')
connection = connect(
    host=db_creds['host'],
    user=db_creds['username'],
    password=db_creds['password']
)
```

### 5. API Protection

```yaml
# WAF + API Gateway
WebACL:
  Type: AWS::WAFv2::WebACL
  Properties:
    DefaultAction:
      Allow: {}
    Rules:
      - Name: RateLimit
        Priority: 1
        Action:
          Block: {}
        Statement:
          RateBasedStatement:
            Limit: 2000
            AggregateKeyType: IP
        VisibilityConfig:
          SampledRequestsEnabled: true
          CloudWatchMetricsEnabled: true
          MetricName: RateLimitRule

      - Name: AWSManagedRulesCommonRuleSet
        Priority: 2
        OverrideAction:
          None: {}
        Statement:
          ManagedRuleGroupStatement:
            VendorName: AWS
            Name: AWSManagedRulesCommonRuleSet
```

### 6. Audit Logging

```yaml
# Enable CloudTrail for all API calls
CloudTrail:
  Type: AWS::CloudTrail::Trail
  Properties:
    IsMultiRegionTrail: true
    IsLogging: true
    S3BucketName: !Ref AuditLogsBucket
    IncludeGlobalServiceEvents: true
    EnableLogFileValidation: true
    EventSelectors:
      - ReadWriteType: All
        IncludeManagementEvents: true
```

---

## Scalability Patterns

### 1. Horizontal vs Vertical Scaling

```
Horizontal (preferred):
- Add more Lambda concurrent executions
- Add more Fargate tasks
- Add more DynamoDB capacity

Vertical (when necessary):
- Increase Lambda memory
- Upgrade RDS instance
- Larger EC2 instances
```

### 2. Database Sharding

```python
# Partition by tenant ID
def get_table_for_tenant(tenant_id):
    shard = hash(tenant_id) % NUM_SHARDS
    return f"data-shard-{shard}"

# Or use DynamoDB single-table design with partition keys
def get_partition_key(tenant_id, entity_type, entity_id):
    return f"TENANT#{tenant_id}#{entity_type}#{entity_id}"
```

### 3. Caching Layers

```
Edge (CloudFront):     Global, static content, TTL: hours-days
Application (Redis):   Regional, session/query cache, TTL: minutes-hours
Database (DAX):        DynamoDB-specific, TTL: minutes
```

```python
# ElastiCache Redis caching pattern
import redis
import json

cache = redis.Redis(host='cache.abc123.cache.amazonaws.com', port=6379)

def get_user(user_id):
    # Check cache first
    cached = cache.get(f"user:{user_id}")
    if cached:
        return json.loads(cached)

    # Fetch from database
    user = db.get_user(user_id)

    # Cache for 5 minutes
    cache.setex(f"user:{user_id}", 300, json.dumps(user))

    return user
```

### 4. Auto-Scaling Configuration

```yaml
# ECS Service Auto-scaling
AutoScalingTarget:
  Type: AWS::ApplicationAutoScaling::ScalableTarget
  Properties:
    MaxCapacity: 10
    MinCapacity: 2
    ResourceId: !Sub service/${Cluster}/${Service.Name}
    ScalableDimension: ecs:service:DesiredCount
    ServiceNamespace: ecs

ScalingPolicy:
  Type: AWS::ApplicationAutoScaling::ScalingPolicy
  Properties:
    PolicyType: TargetTrackingScaling
    TargetTrackingScalingPolicyConfiguration:
      PredefinedMetricSpecification:
        PredefinedMetricType: ECSServiceAverageCPUUtilization
      TargetValue: 70
      ScaleInCooldown: 300
      ScaleOutCooldown: 60
```

---

## DevOps and Reliability

### 1. Infrastructure as Code

```bash
# Version control all infrastructure
git init
git add .
git commit -m "Initial infrastructure setup"

# Use separate stacks per environment
cdk deploy --context environment=dev
cdk deploy --context environment=staging
cdk deploy --context environment=production
```

### 2. Blue/Green Deployments

```yaml
# CodeDeploy Blue/Green for ECS
DeploymentGroup:
  Type: AWS::CodeDeploy::DeploymentGroup
  Properties:
    DeploymentConfigName: CodeDeployDefault.ECSAllAtOnce
    DeploymentStyle:
      DeploymentType: BLUE_GREEN
      DeploymentOption: WITH_TRAFFIC_CONTROL
    BlueGreenDeploymentConfiguration:
      DeploymentReadyOption:
        ActionOnTimeout: CONTINUE_DEPLOYMENT
        WaitTimeInMinutes: 0
      TerminateBlueInstancesOnDeploymentSuccess:
        Action: TERMINATE
        TerminationWaitTimeInMinutes: 5
```

### 3. Health Checks

```python
# Application health endpoint
from flask import Flask, jsonify
import boto3

app = Flask(__name__)

@app.route('/health')
def health():
    checks = {
        'database': check_database(),
        'cache': check_cache(),
        'external_api': check_external_api()
    }

    status = 'healthy' if all(checks.values()) else 'unhealthy'
    code = 200 if status == 'healthy' else 503

    return jsonify({'status': status, 'checks': checks}), code

def check_database():
    try:
        # Quick connectivity test
        db.execute('SELECT 1')
        return True
    except Exception:
        return False
```

### 4. Monitoring Setup

```yaml
# CloudWatch Dashboard
Dashboard:
  Type: AWS::CloudWatch::Dashboard
  Properties:
    DashboardName: production-overview
    DashboardBody: |
      {
        "widgets": [
          {
            "type": "metric",
            "properties": {
              "metrics": [
                ["AWS/Lambda", "Invocations", "FunctionName", "api-handler"],
                [".", "Errors", ".", "."],
                [".", "Duration", ".", ".", {"stat": "p99"}]
              ],
              "period": 60,
              "title": "Lambda Metrics"
            }
          }
        ]
      }

# Critical Alarms
ErrorAlarm:
  Type: AWS::CloudWatch::Alarm
  Properties:
    AlarmName: high-error-rate
    MetricName: Errors
    Namespace: AWS/Lambda
    Statistic: Sum
    Period: 60
    EvaluationPeriods: 3
    Threshold: 10
    ComparisonOperator: GreaterThanThreshold
    AlarmActions:
      - !Ref AlertTopic
```

---

## Common Pitfalls

### Technical Debt

| Pitfall | Solution |
|---------|----------|
| Over-engineering early | Start simple, scale when needed |
| Under-monitoring | Set up CloudWatch from day one |
| Ignoring costs | Enable Cost Explorer and billing alerts |
| Single region only | Plan for multi-region from start |

### Security Mistakes

| Mistake | Prevention |
|---------|------------|
| Public S3 buckets | Block public access, use bucket policies |
| Overly permissive IAM | Never use "*", specify resources |
| Hardcoded credentials | Use Secrets Manager, IAM roles |
| Unencrypted data | Enable encryption by default |

### Performance Issues

| Issue | Solution |
|-------|----------|
| No caching | Add CloudFront, ElastiCache early |
| Inefficient queries | Use indexes, avoid DynamoDB scans |
| Large Lambda packages | Use layers, minimize dependencies |
| N+1 queries | Implement DataLoader, batch operations |

### Cost Surprises

| Surprise | Prevention |
|----------|------------|
| Undeleted resources | Tag everything, review weekly |
| Data transfer costs | Keep traffic in same AZ/region |
| NAT Gateway charges | Use VPC endpoints for AWS services |
| Log accumulation | Set CloudWatch retention policies |
