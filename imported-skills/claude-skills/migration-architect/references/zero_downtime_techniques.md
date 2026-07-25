# Zero-Downtime Migration Techniques

## Overview

Zero-downtime migrations are critical for maintaining business continuity and user experience during system changes. This guide provides comprehensive techniques, patterns, and implementation strategies for achieving true zero-downtime migrations across different system components.

## Core Principles

### 1. Backward Compatibility
Every change must be backward compatible until all clients have migrated to the new version.

### 2. Incremental Changes
Break large changes into smaller, independent increments that can be deployed and validated separately.

### 3. Feature Flags
Use feature toggles to control the rollout of new functionality without code deployments.

### 4. Graceful Degradation
Ensure systems continue to function even when some components are unavailable or degraded.

## Database Zero-Downtime Techniques

### Schema Evolution Without Downtime

#### 1. Additive Changes Only
**Principle:** Only add new elements; never remove or modify existing ones directly.

```sql
-- ✅ Good: Additive change
ALTER TABLE users ADD COLUMN middle_name VARCHAR(50);

-- ❌ Bad: Breaking change
ALTER TABLE users DROP COLUMN email;
```

#### 2. Multi-Phase Schema Evolution

**Phase 1: Expand**
```sql
-- Add new column alongside existing one
ALTER TABLE users ADD COLUMN email_address VARCHAR(255);

-- Add index concurrently (PostgreSQL)
CREATE INDEX CONCURRENTLY idx_users_email_address ON users(email_address);
```

**Phase 2: Dual Write (Application Code)**
```python
class UserService:
    def create_user(self, name, email):
        # Write to both old and new columns
        user = User(
            name=name,
            email=email,           # Old column
            email_address=email    # New column
        )
        return user.save()
    
    def update_email(self, user_id, new_email):
        # Update both columns
        user = User.objects.get(id=user_id)
        user.email = new_email
        user.email_address = new_email
        user.save()
        return user
```

**Phase 3: Backfill Data**
```sql
-- Backfill existing data (in batches)
UPDATE users 
SET email_address = email 
WHERE email_address IS NULL 
  AND id BETWEEN ? AND ?;
```

**Phase 4: Switch Reads**
```python
class UserService:
    def get_user_email(self, user_id):
        user = User.objects.get(id=user_id)
        # Switch to reading from new column
        return user.email_address or user.email
```

**Phase 5: Contract**
```sql
-- After validation, remove old column
ALTER TABLE users DROP COLUMN email;
-- Rename new column if needed
ALTER TABLE users RENAME COLUMN email_address TO email;
```

### 3. Online Schema Changes

#### PostgreSQL Techniques

```sql
-- Safe column addition
ALTER TABLE orders ADD COLUMN status_new VARCHAR(20) DEFAULT 'pending';

-- Safe index creation
CREATE INDEX CONCURRENTLY idx_orders_status_new ON orders(status_new);

-- Safe constraint addition (after data validation)
ALTER TABLE orders ADD CONSTRAINT check_status_new 
CHECK (status_new IN ('pending', 'processing', 'completed', 'cancelled'));
```

#### MySQL Techniques

```sql
-- Use pt-online-schema-change for large tables
pt-online-schema-change \
  --alter "ADD COLUMN status VARCHAR(20) DEFAULT 'pending'" \
  --execute \
  D=mydb,t=orders

-- Online DDL (MySQL 5.6+)
ALTER TABLE orders 
ADD COLUMN priority INT DEFAULT 1,
ALGORITHM=INPLACE, 
LOCK=NONE;
```

### 4. Data Migration Strategies

#### Chunked Data Migration

```python
class DataMigrator:
    def __init__(self, source_table, target_table, chunk_size=1000):
        self.source_table = source_table
        self.target_table = target_table
        self.chunk_size = chunk_size
    
    def migrate_data(self):
        last_id = 0
        total_migrated = 0
        
        while True:
            # Get next chunk
            chunk = self.get_chunk(last_id, self.chunk_size)
            
            if not chunk:
                break
            
            # Transform and migrate chunk
            for record in chunk:
                transformed = self.transform_record(record)
                self.insert_or_update(transformed)
            
            last_id = chunk[-1]['id']
            total_migrated += len(chunk)
            
            # Brief pause to avoid overwhelming the database
            time.sleep(0.1)
            
            self.log_progress(total_migrated)
        
        return total_migrated
    
    def get_chunk(self, last_id, limit):
        return db.execute(f"""
            SELECT * FROM {self.source_table}
            WHERE id > %s
            ORDER BY id
            LIMIT %s
        """, (last_id, limit))
```

#### Change Data Capture (CDC)

```python
class CDCProcessor:
    def __init__(self):
        self.kafka_consumer = KafkaConsumer('db_changes')
        self.target_db = TargetDatabase()
    
    def process_changes(self):
        for message in self.kafka_consumer:
            change = json.loads(message.value)
            
            if change['operation'] == 'INSERT':
                self.handle_insert(change)
            elif change['operation'] == 'UPDATE':
                self.handle_update(change)
            elif change['operation'] == 'DELETE':
                self.handle_delete(change)
    
    def handle_insert(self, change):
        transformed_data = self.transform_data(change['after'])
        self.target_db.insert(change['table'], transformed_data)
    
    def handle_update(self, change):
        key = change['key']
        transformed_data = self.transform_data(change['after'])
        self.target_db.update(change['table'], key, transformed_data)
```

## Application Zero-Downtime Techniques

### 1. Blue-Green Deployments

#### Infrastructure Setup

```yaml
# Blue Environment (Current Production)
apiVersion: apps/v1
kind: Deployment
metadata:
  name: app-blue
  labels:
    version: blue
    app: myapp
spec:
  replicas: 3
  selector:
    matchLabels:
      app: myapp
      version: blue
  template:
    metadata:
      labels:
        app: myapp
        version: blue
    spec:
      containers:
      - name: app
        image: myapp:1.0.0
        ports:
        - containerPort: 8080
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 5
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 15
          periodSeconds: 10

---
# Green Environment (New Version)
apiVersion: apps/v1
kind: Deployment
metadata:
  name: app-green
  labels:
    version: green
    app: myapp
spec:
  replicas: 3
  selector:
    matchLabels:
      app: myapp
      version: green
  template:
    metadata:
      labels:
        app: myapp
        version: green
    spec:
      containers:
      - name: app
        image: myapp:2.0.0
        ports:
        - containerPort: 8080
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 5
```

#### Service Switching

```yaml
# Service (switches between blue and green)
apiVersion: v1
kind: Service
metadata:
  name: app-service
spec:
  selector:
    app: myapp
    version: blue  # Switch to 'green' for deployment
  ports:
  - port: 80
    targetPort: 8080
  type: LoadBalancer
```

#### Automated Deployment Script

```bash
#!/bin/bash

# Blue-Green Deployment Script
NAMESPACE="production"
APP_NAME="myapp"
NEW_IMAGE="myapp:2.0.0"

# Determine current and target environments
CURRENT_VERSION=$(kubectl get service $APP_NAME-service -o jsonpath='{.spec.selector.version}')

if [ "$CURRENT_VERSION" = "blue" ]; then
    TARGET_VERSION="green"
else
    TARGET_VERSION="blue"
fi

echo "Current version: $CURRENT_VERSION"
echo "Target version: $TARGET_VERSION"

# Update target environment with new image
kubectl set image deployment/$APP_NAME-$TARGET_VERSION app=$NEW_IMAGE

# Wait for rollout to complete
kubectl rollout status deployment/$APP_NAME-$TARGET_VERSION --timeout=300s

# Run health checks
echo "Running health checks..."
TARGET_IP=$(kubectl get service $APP_NAME-$TARGET_VERSION -o jsonpath='{.status.loadBalancer.ingress[0].ip}')

for i in {1..30}; do
    if curl -f http://$TARGET_IP/health; then
        echo "Health check passed"
        break
    fi
    
    if [ $i -eq 30 ]; then
        echo "Health check failed after 30 attempts"
        exit 1
    fi
    
    sleep 2
done

# Switch traffic to new version
kubectl patch service $APP_NAME-service -p '{"spec":{"selector":{"version":"'$TARGET_VERSION'"}}}'

echo "Traffic switched to $TARGET_VERSION"

# Monitor for 5 minutes
echo "Monitoring new version..."
sleep 300

# Check if rollback is needed
ERROR_RATE=$(curl -s "http://monitoring.company.com/api/error_rate?service=$APP_NAME" | jq '.error_rate')

if (( $(echo "$ERROR_RATE > 0.05" | bc -l) )); then
    echo "Error rate too high ($ERROR_RATE), rolling back..."
    kubectl patch service $APP_NAME-service -p '{"spec":{"selector":{"version":"'$CURRENT_VERSION'"}}}'
    exit 1
fi

echo "Deployment successful!"
```

### 2. Canary Deployments

#### Progressive Canary with Istio

```yaml
# Destination Rule
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: myapp-destination
spec:
  host: myapp
  subsets:
  - name: v1
    labels:
      version: v1
  - name: v2
    labels:
      version: v2

---
# Virtual Service for Canary
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: myapp-canary
spec:
  hosts:
  - myapp
  http:
  - match:
    - headers:
        canary:
          exact: "true"
    route:
    - destination:
        host: myapp
        subset: v2
  - route:
    - destination:
        host: myapp
        subset: v1
      weight: 95
    - destination:
        host: myapp
        subset: v2
      weight: 5
```

#### Automated Canary Controller

```python
class CanaryController:
    def __init__(self, istio_client, prometheus_client):
        self.istio = istio_client
        self.prometheus = prometheus_client
        self.canary_weight = 5
        self.max_weight = 100
        self.weight_increment = 5
        self.validation_window = 300  # 5 minutes
    
    async def deploy_canary(self, app_name, new_version):
        """Deploy new version using canary strategy"""
        
        # Start with small percentage
        await self.update_traffic_split(app_name, self.canary_weight)
        
        while self.canary_weight < self.max_weight:
            # Monitor metrics for validation window
            await asyncio.sleep(self.validation_window)
            
            # Check canary health
            if not await self.is_canary_healthy(app_name, new_version):
                await self.rollback_canary(app_name)
                raise Exception("Canary deployment failed health checks")
            
            # Increase traffic to canary
            self.canary_weight = min(
                self.canary_weight + self.weight_increment,
                self.max_weight
            )
            
            await self.update_traffic_split(app_name, self.canary_weight)
            
            print(f"Canary traffic increased to {self.canary_weight}%")
        
        print("Canary deployment completed successfully")
    
    async def is_canary_healthy(self, app_name, version):
        """Check if canary version is healthy"""
        
        # Check error rate
        error_rate = await self.prometheus.query(
            f'rate(http_requests_total{{app="{app_name}", version="{version}", status=~"5.."}}'
            f'[5m]) / rate(http_requests_total{{app="{app_name}", version="{version}"}}[5m])'
        )
        
        if error_rate > 0.05:  # 5% error rate threshold
            return False
        
        # Check response time
        p95_latency = await self.prometheus.query(
            f'histogram_quantile(0.95, rate(http_request_duration_seconds_bucket'
            f'{{app="{app_name}", version="{version}"}}[5m]))'
        )
        
        if p95_latency > 2.0:  # 2 second p95 threshold
            return False
        
        return True
    
    async def update_traffic_split(self, app_name, canary_weight):
        """Update Istio virtual service with new traffic split"""
        
        stable_weight = 100 - canary_weight
        
        virtual_service = {
            "apiVersion": "networking.istio.io/v1beta1",
            "kind": "VirtualService",
            "metadata": {"name": f"{app_name}-canary"},
            "spec": {
                "hosts": [app_name],
                "http": [{
                    "route": [
                        {
                            "destination": {"host": app_name, "subset": "stable"},
                            "weight": stable_weight
                        },
                        {
                            "destination": {"host": app_name, "subset": "canary"},
                            "weight": canary_weight
                        }
                    ]
                }]
            }
        }
        
        await self.istio.apply_virtual_service(virtual_service)
```

### 3. Rolling Updates

#### Kubernetes Rolling Update Strategy

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rolling-update-app
spec:
  replicas: 10
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 2         # Can have 2 extra pods during update
      maxUnavailable: 1   # At most 1 pod can be unavailable
  selector:
    matchLabels:
      app: rolling-update-app
  template:
    metadata:
      labels:
        app: rolling-update-app
    spec:
      containers:
      - name: app
        image: myapp:2.0.0
        ports:
        - containerPort: 8080
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 2
          timeoutSeconds: 1
          successThreshold: 1
          failureThreshold: 3
        livenessProbe:
          httpGet:
            path: /live
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 10
```

#### Custom Rolling Update Controller

```python
class RollingUpdateController:
    def __init__(self, k8s_client):
        self.k8s = k8s_client
        self.max_surge = 2
        self.max_unavailable = 1
        
    async def rolling_update(self, deployment_name, new_image):
        """Perform rolling update with custom logic"""
        
        deployment = await self.k8s.get_deployment(deployment_name)
        total_replicas = deployment.spec.replicas
        
        # Calculate batch size
        batch_size = min(self.max_surge, total_replicas // 5)  # Update 20% at a time
        
        updated_pods = []
        
        for i in range(0, total_replicas, batch_size):
            batch_end = min(i + batch_size, total_replicas)
            
            # Update batch of pods
            for pod_index in range(i, batch_end):
                old_pod = await self.get_pod_by_index(deployment_name, pod_index)
                
                # Create new pod with new image
                new_pod = await self.create_updated_pod(old_pod, new_image)
                
                # Wait for new pod to be ready
                await self.wait_for_pod_ready(new_pod.metadata.name)
                
                # Remove old pod
                await self.k8s.delete_pod(old_pod.metadata.name)
                
                updated_pods.append(new_pod)
                
                # Brief pause between pod updates
                await asyncio.sleep(2)
            
            # Validate batch health before continuing
            if not await self.validate_batch_health(updated_pods[-batch_size:]):
                # Rollback batch
                await self.rollback_batch(updated_pods[-batch_size:])
                raise Exception("Rolling update failed validation")
            
            print(f"Updated {batch_end}/{total_replicas} pods")
        
        print("Rolling update completed successfully")
```

## Load Balancer and Traffic Management

### 1. Weighted Routing

#### NGINX Configuration

```nginx
upstream backend {
    # Old version - 80% traffic
    server old-app-1:8080 weight=4;
    server old-app-2:8080 weight=4;
    
    # New version - 20% traffic
    server new-app-1:8080 weight=1;
    server new-app-2:8080 weight=1;
}

server {
    listen 80;
    location / {
        proxy_pass http://backend;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        
        # Health check headers
        proxy_set_header X-Health-Check-Timeout 5s;
    }
}
```

#### HAProxy Configuration

```haproxy
backend app_servers
    balance roundrobin
    option httpchk GET /health
    
    # Old version servers
    server old-app-1 old-app-1:8080 check weight 80
    server old-app-2 old-app-2:8080 check weight 80
    
    # New version servers
    server new-app-1 new-app-1:8080 check weight 20
    server new-app-2 new-app-2:8080 check weight 20

frontend app_frontend
    bind *:80
    default_backend app_servers
    
    # Custom health check endpoint
    acl health_check path_beg /health
    http-request return status 200 content-type text/plain string "OK" if health_check
```

### 2. Circuit Breaker Implementation

```python
class CircuitBreaker:
    def __init__(self, failure_threshold=5, recovery_timeout=60, expected_exception=Exception):
        self.failure_threshold = failure_threshold
        self.recovery_timeout = recovery_timeout
        self.expected_exception = expected_exception
        self.failure_count = 0
        self.last_failure_time = None
        self.state = 'CLOSED'  # CLOSED, OPEN, HALF_OPEN
        
    def call(self, func, *args, **kwargs):
        """Execute function with circuit breaker protection"""
        
        if self.state == 'OPEN':
            if self._should_attempt_reset():
                self.state = 'HALF_OPEN'
            else:
                raise CircuitBreakerOpenException("Circuit breaker is OPEN")
        
        try:
            result = func(*args, **kwargs)
            self._on_success()
            return result
        except self.expected_exception as e:
            self._on_failure()
            raise
    
    def _should_attempt_reset(self):
        return (
            self.last_failure_time and
            time.time() - self.last_failure_time >= self.recovery_timeout
        )
    
    def _on_success(self):
        self.failure_count = 0
        self.state = 'CLOSED'
    
    def _on_failure(self):
        self.failure_count += 1
        self.last_failure_time = time.time()
        
        if self.failure_count >= self.failure_threshold:
            self.state = 'OPEN'

# Usage with service migration
@CircuitBreaker(failure_threshold=3, recovery_timeout=30)
def call_new_service(request):
    return new_service.process(request)

def handle_request(request):
    try:
        return call_new_service(request)
    except CircuitBreakerOpenException:
        # Fallback to old service
        return old_service.process(request)
```

## Monitoring and Validation

### 1. Health Check Implementation

```python
class HealthChecker:
    def __init__(self):
        self.checks = []
        
    def add_check(self, name, check_func, timeout=5):
        self.checks.append({
            'name': name,
            'func': check_func,
            'timeout': timeout
        })
    
    async def run_checks(self):
        """Run all health checks and return status"""
        results = {}
        overall_status = 'healthy'
        
        for check in self.checks:
            try:
                result = await asyncio.wait_for(
                    check['func'](),
                    timeout=check['timeout']
                )
                results[check['name']] = {
                    'status': 'healthy',
                    'result': result
                }
            except asyncio.TimeoutError:
                results[check['name']] = {
                    'status': 'unhealthy',
                    'error': 'timeout'
                }
                overall_status = 'unhealthy'
            except Exception as e:
                results[check['name']] = {
                    'status': 'unhealthy',
                    'error': str(e)
                }
                overall_status = 'unhealthy'
        
        return {
            'status': overall_status,
            'checks': results,
            'timestamp': datetime.utcnow().isoformat()
        }

# Example health checks
health_checker = HealthChecker()

async def database_check():
    """Check database connectivity"""
    result = await db.execute("SELECT 1")
    return result is not None

async def external_api_check():
    """Check external API availability"""
    response = await http_client.get("https://api.example.com/health")
    return response.status_code == 200

async def memory_check():
    """Check memory usage"""
    memory_usage = psutil.virtual_memory().percent
    if memory_usage > 90:
        raise Exception(f"Memory usage too high: {memory_usage}%")
    return f"Memory usage: {memory_usage}%"

health_checker.add_check("database", database_check)
health_checker.add_check("external_api", external_api_check)
health_checker.add_check("memory", memory_check)
```

### 2. Readiness vs Liveness Probes

```yaml
# Kubernetes Pod with proper health checks
apiVersion: v1
kind: Pod
metadata:
  name: app-pod
spec:
  containers:
  - name: app
    image: myapp:2.0.0
    ports:
    - containerPort: 8080
    
    # Readiness probe - determines if pod should receive traffic
    readinessProbe:
      httpGet:
        path: /ready
        port: 8080
      initialDelaySeconds: 5
      periodSeconds: 3
      timeoutSeconds: 2
      successThreshold: 1
      failureThreshold: 3
    
    # Liveness probe - determines if pod should be restarted
    livenessProbe:
      httpGet:
        path: /live
        port: 8080
      initialDelaySeconds: 30
      periodSeconds: 10
      timeoutSeconds: 5
      successThreshold: 1
      failureThreshold: 3
    
    # Startup probe - gives app time to start before other probes
    startupProbe:
      httpGet:
        path: /startup
        port: 8080
      initialDelaySeconds: 10
      periodSeconds: 5
      timeoutSeconds: 3
      successThreshold: 1
      failureThreshold: 30  # Allow up to 150 seconds for startup
```

### 3. Metrics and Alerting

```python
class MigrationMetrics:
    def __init__(self, prometheus_client):
        self.prometheus = prometheus_client
        
        # Define custom metrics
        self.migration_progress = Counter(
            'migration_progress_total',
            'Total migration operations completed',
            ['operation', 'status']
        )
        
        self.migration_duration = Histogram(
            'migration_operation_duration_seconds',
            'Time spent on migration operations',
            ['operation']
        )
        
        self.system_health = Gauge(
            'system_health_score',
            'Overall system health score (0-1)',
            ['component']
        )
        
        self.traffic_split = Gauge(
            'traffic_split_percentage',
            'Percentage of traffic going to each version',
            ['version']
        )
    
    def record_migration_step(self, operation, status, duration=None):
        """Record completion of a migration step"""
        self.migration_progress.labels(operation=operation, status=status).inc()
        
        if duration:
            self.migration_duration.labels(operation=operation).observe(duration)
    
    def update_health_score(self, component, score):
        """Update health score for a component"""
        self.system_health.labels(component=component).set(score)
    
    def update_traffic_split(self, version_weights):
        """Update traffic split metrics"""
        for version, weight in version_weights.items():
            self.traffic_split.labels(version=version).set(weight)

# Usage in migration
metrics = MigrationMetrics(prometheus_client)

def perform_migration_step(operation):
    start_time = time.time()
    
    try:
        # Perform migration operation
        result = execute_migration_operation(operation)
        
        # Record success
        duration = time.time() - start_time
        metrics.record_migration_step(operation, 'success', duration)
        
        return result
        
    except Exception as e:
        # Record failure
        duration = time.time() - start_time
        metrics.record_migration_step(operation, 'failure', duration)
        raise
```

## Rollback Strategies

### 1. Immediate Rollback Triggers

```python
class AutoRollbackSystem:
    def __init__(self, metrics_client, deployment_client):
        self.metrics = metrics_client
        self.deployment = deployment_client
        self.rollback_triggers = {
            'error_rate_spike': {
                'threshold': 0.05,  # 5% error rate
                'window': 300,      # 5 minutes
                'auto_rollback': True
            },
            'latency_increase': {
                'threshold': 2.0,   # 2x baseline latency
                'window': 600,      # 10 minutes
                'auto_rollback': False  # Manual confirmation required
            },
            'availability_drop': {
                'threshold': 0.95,  # Below 95% availability
                'window': 120,      # 2 minutes
                'auto_rollback': True
            }
        }
    
    async def monitor_and_rollback(self, deployment_name):
        """Monitor deployment and trigger rollback if needed"""
        
        while True:
            for trigger_name, config in self.rollback_triggers.items():
                if await self.check_trigger(trigger_name, config):
                    if config['auto_rollback']:
                        await self.execute_rollback(deployment_name, trigger_name)
                    else:
                        await self.alert_for_manual_rollback(deployment_name, trigger_name)
            
            await asyncio.sleep(30)  # Check every 30 seconds
    
    async def check_trigger(self, trigger_name, config):
        """Check if rollback trigger condition is met"""
        
        current_value = await self.metrics.get_current_value(trigger_name)
        baseline_value = await self.metrics.get_baseline_value(trigger_name)
        
        if trigger_name == 'error_rate_spike':
            return current_value > config['threshold']
        elif trigger_name == 'latency_increase':
            return current_value > baseline_value * config['threshold']
        elif trigger_name == 'availability_drop':
            return current_value < config['threshold']
        
        return False
    
    async def execute_rollback(self, deployment_name, reason):
        """Execute automatic rollback"""
        
        print(f"Executing automatic rollback for {deployment_name}. Reason: {reason}")
        
        # Get previous revision
        previous_revision = await self.deployment.get_previous_revision(deployment_name)
        
        # Perform rollback
        await self.deployment.rollback_to_revision(deployment_name, previous_revision)
        
        # Notify stakeholders
        await self.notify_rollback_executed(deployment_name, reason)
```

### 2. Data Rollback Strategies

```sql
-- Point-in-time recovery setup
-- Create restore point before migration
SELECT pg_create_restore_point('pre_migration_' || to_char(now(), 'YYYYMMDD_HH24MISS'));

-- Rollback using point-in-time recovery
-- (This would be executed on a separate recovery instance)
-- recovery.conf:
-- recovery_target_name = 'pre_migration_20240101_120000'
-- recovery_target_action = 'promote'
```

```python
class DataRollbackManager:
    def __init__(self, database_client, backup_service):
        self.db = database_client
        self.backup = backup_service
    
    async def create_rollback_point(self, migration_id):
        """Create a rollback point before migration"""
        
        rollback_point = {
            'migration_id': migration_id,
            'timestamp': datetime.utcnow(),
            'backup_location': None,
            'schema_snapshot': None
        }
        
        # Create database backup
        backup_path = await self.backup.create_backup(
            f"pre_migration_{migration_id}_{int(time.time())}"
        )
        rollback_point['backup_location'] = backup_path
        
        # Capture schema snapshot
        schema_snapshot = await self.capture_schema_snapshot()
        rollback_point['schema_snapshot'] = schema_snapshot
        
        # Store rollback point metadata
        await self.store_rollback_metadata(rollback_point)
        
        return rollback_point
    
    async def execute_rollback(self, migration_id):
        """Execute data rollback to specified point"""
        
        rollback_point = await self.get_rollback_metadata(migration_id)
        
        if not rollback_point:
            raise Exception(f"No rollback point found for migration {migration_id}")
        
        # Stop application traffic
        await self.stop_application_traffic()
        
        try:
            # Restore from backup
            await self.backup.restore_from_backup(
                rollback_point['backup_location']
            )
            
            # Validate data integrity
            await self.validate_data_integrity(
                rollback_point['schema_snapshot']
            )
            
            # Update application configuration
            await self.update_application_config(rollback_point)
            
            # Resume application traffic
            await self.resume_application_traffic()
            
            print(f"Data rollback completed successfully for migration {migration_id}")
            
        except Exception as e:
            # If rollback fails, we have a serious problem
            await self.escalate_rollback_failure(migration_id, str(e))
            raise
```

## Best Practices Summary

### 1. Pre-Migration Checklist
- [ ] Comprehensive backup strategy in place
- [ ] Rollback procedures tested in staging
- [ ] Monitoring and alerting configured
- [ ] Health checks implemented
- [ ] Feature flags configured
- [ ] Team communication plan established
- [ ] Load balancer configuration prepared
- [ ] Database connection pooling optimized

### 2. During Migration
- [ ] Monitor key metrics continuously
- [ ] Validate each phase before proceeding
- [ ] Maintain detailed logs of all actions
- [ ] Keep stakeholders informed of progress
- [ ] Have rollback trigger ready
- [ ] Monitor user experience metrics
- [ ] Watch for performance degradation
- [ ] Validate data consistency

### 3. Post-Migration
- [ ] Continue monitoring for 24-48 hours
- [ ] Validate all business processes
- [ ] Update documentation
- [ ] Conduct post-migration retrospective
- [ ] Archive migration artifacts
- [ ] Update disaster recovery procedures
- [ ] Plan for legacy system decommissioning

### 4. Common Pitfalls to Avoid
- Don't skip testing rollback procedures
- Don't ignore performance impact
- Don't rush through validation phases
- Don't forget to communicate with stakeholders
- Don't assume health checks are sufficient
- Don't neglect data consistency validation
- Don't underestimate time requirements
- Don't overlook dependency impacts

This comprehensive guide provides the foundation for implementing zero-downtime migrations across various system components while maintaining high availability and data integrity.