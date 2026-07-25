# Migration Patterns Catalog

## Overview

This catalog provides detailed descriptions of proven migration patterns, their use cases, implementation guidelines, and best practices. Each pattern includes code examples, diagrams, and lessons learned from real-world implementations.

## Database Migration Patterns

### 1. Expand-Contract Pattern

**Use Case:** Schema evolution with zero downtime
**Complexity:** Medium
**Risk Level:** Low-Medium

#### Description
The Expand-Contract pattern allows for schema changes without downtime by following a three-phase approach:

1. **Expand:** Add new schema elements alongside existing ones
2. **Migrate:** Dual-write to both old and new schema during transition
3. **Contract:** Remove old schema elements after validation

#### Implementation Steps

```sql
-- Phase 1: Expand
ALTER TABLE users ADD COLUMN email_new VARCHAR(255);
CREATE INDEX CONCURRENTLY idx_users_email_new ON users(email_new);

-- Phase 2: Migrate (Application Code)
-- Write to both columns during transition period
INSERT INTO users (name, email, email_new) VALUES (?, ?, ?);

-- Backfill existing data
UPDATE users SET email_new = email WHERE email_new IS NULL;

-- Phase 3: Contract (after validation)
ALTER TABLE users DROP COLUMN email;
ALTER TABLE users RENAME COLUMN email_new TO email;
```

#### Pros and Cons
**Pros:**
- Zero downtime deployments
- Safe rollback at any point
- Gradual transition with validation

**Cons:**
- Increased storage during transition
- More complex application logic
- Extended migration timeline

### 2. Parallel Schema Pattern

**Use Case:** Major database restructuring
**Complexity:** High
**Risk Level:** Medium

#### Description
Run new and old schemas in parallel, using feature flags to gradually route traffic to the new schema while maintaining the ability to rollback quickly.

#### Implementation Example

```python
class DatabaseRouter:
    def __init__(self, feature_flag_service):
        self.feature_flags = feature_flag_service
        self.old_db = OldDatabaseConnection()
        self.new_db = NewDatabaseConnection()
    
    def route_query(self, user_id, query_type):
        if self.feature_flags.is_enabled("new_schema", user_id):
            return self.new_db.execute(query_type)
        else:
            return self.old_db.execute(query_type)
    
    def dual_write(self, data):
        # Write to both databases for consistency
        success_old = self.old_db.write(data)
        success_new = self.new_db.write(transform_data(data))
        
        if not (success_old and success_new):
            # Handle partial failures
            self.handle_dual_write_failure(data, success_old, success_new)
```

#### Best Practices
- Implement data consistency checks between schemas
- Use circuit breakers for automatic failover
- Monitor performance impact of dual writes
- Plan for data reconciliation processes

### 3. Event Sourcing Migration

**Use Case:** Migrating systems with complex business logic
**Complexity:** High
**Risk Level:** Medium-High

#### Description
Capture all changes as events during migration, enabling replay and reconciliation capabilities.

#### Event Store Schema
```sql
CREATE TABLE migration_events (
    event_id UUID PRIMARY KEY,
    aggregate_id UUID NOT NULL,
    event_type VARCHAR(100) NOT NULL,
    event_data JSONB NOT NULL,
    event_version INTEGER NOT NULL,
    occurred_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    processed_at TIMESTAMP WITH TIME ZONE
);
```

#### Migration Event Handler
```python
class MigrationEventHandler:
    def __init__(self, old_store, new_store):
        self.old_store = old_store
        self.new_store = new_store
        self.event_log = []
    
    def handle_update(self, entity_id, old_data, new_data):
        # Log the change as an event
        event = MigrationEvent(
            entity_id=entity_id,
            event_type="entity_migrated",
            old_data=old_data,
            new_data=new_data,
            timestamp=datetime.now()
        )
        
        self.event_log.append(event)
        
        # Apply to new store
        success = self.new_store.update(entity_id, new_data)
        
        if not success:
            # Mark for retry
            event.status = "failed"
            self.schedule_retry(event)
        
        return success
    
    def replay_events(self, from_timestamp=None):
        """Replay events for reconciliation"""
        events = self.get_events_since(from_timestamp)
        for event in events:
            self.apply_event(event)
```

## Service Migration Patterns

### 1. Strangler Fig Pattern

**Use Case:** Legacy system replacement
**Complexity:** Medium-High
**Risk Level:** Medium

#### Description
Gradually replace legacy functionality by intercepting calls and routing them to new services, eventually "strangling" the legacy system.

#### Implementation Architecture

```yaml
# API Gateway Configuration
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: user-service-migration
spec:
  http:
  - match:
    - headers:
        migration-flag:
          exact: "new"
    route:
    - destination:
        host: user-service-v2
  - route:
    - destination:
        host: user-service-v1
```

#### Strangler Proxy Implementation

```python
class StranglerProxy:
    def __init__(self):
        self.legacy_service = LegacyUserService()
        self.new_service = NewUserService()
        self.feature_flags = FeatureFlagService()
    
    def handle_request(self, request):
        route = self.determine_route(request)
        
        if route == "new":
            return self.handle_with_new_service(request)
        elif route == "both":
            return self.handle_with_both_services(request)
        else:
            return self.handle_with_legacy_service(request)
    
    def determine_route(self, request):
        user_id = request.get('user_id')
        
        if self.feature_flags.is_enabled("new_user_service", user_id):
            if self.feature_flags.is_enabled("dual_write", user_id):
                return "both"
            else:
                return "new"
        else:
            return "legacy"
```

### 2. Parallel Run Pattern

**Use Case:** Risk mitigation for critical services
**Complexity:** Medium
**Risk Level:** Low-Medium

#### Description
Run both old and new services simultaneously, comparing outputs to validate correctness before switching traffic.

#### Implementation

```python
class ParallelRunManager:
    def __init__(self):
        self.primary_service = PrimaryService()
        self.candidate_service = CandidateService()
        self.comparator = ResponseComparator()
        self.metrics = MetricsCollector()
    
    async def parallel_execute(self, request):
        # Execute both services concurrently
        primary_task = asyncio.create_task(
            self.primary_service.process(request)
        )
        candidate_task = asyncio.create_task(
            self.candidate_service.process(request)
        )
        
        # Always wait for primary
        primary_result = await primary_task
        
        try:
            # Wait for candidate with timeout
            candidate_result = await asyncio.wait_for(
                candidate_task, timeout=5.0
            )
            
            # Compare results
            comparison = self.comparator.compare(
                primary_result, candidate_result
            )
            
            # Record metrics
            self.metrics.record_comparison(comparison)
            
        except asyncio.TimeoutError:
            self.metrics.record_timeout("candidate")
        except Exception as e:
            self.metrics.record_error("candidate", str(e))
        
        # Always return primary result
        return primary_result
```

### 3. Blue-Green Deployment Pattern

**Use Case:** Zero-downtime service updates
**Complexity:** Low-Medium
**Risk Level:** Low

#### Description
Maintain two identical production environments (blue and green), switching traffic between them for deployments.

#### Kubernetes Implementation

```yaml
# Blue Deployment
apiVersion: apps/v1
kind: Deployment
metadata:
  name: app-blue
  labels:
    version: blue
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
        image: myapp:v1.0.0

---
# Green Deployment
apiVersion: apps/v1
kind: Deployment
metadata:
  name: app-green
  labels:
    version: green
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
        image: myapp:v2.0.0

---
# Service (switches between blue and green)
apiVersion: v1
kind: Service
metadata:
  name: app-service
spec:
  selector:
    app: myapp
    version: blue  # Change to green for deployment
  ports:
  - port: 80
    targetPort: 8080
```

## Infrastructure Migration Patterns

### 1. Lift and Shift Pattern

**Use Case:** Quick cloud migration with minimal changes
**Complexity:** Low-Medium
**Risk Level:** Low

#### Description
Migrate applications to cloud infrastructure with minimal or no code changes, focusing on infrastructure compatibility.

#### Migration Checklist

```yaml
Pre-Migration Assessment:
  - inventory_current_infrastructure:
      - servers_and_specifications
      - network_configuration
      - storage_requirements
      - security_configurations
  - identify_dependencies:
      - database_connections
      - external_service_integrations
      - file_system_dependencies
  - assess_compatibility:
      - operating_system_versions
      - runtime_dependencies
      - license_requirements

Migration Execution:
  - provision_target_infrastructure:
      - compute_instances
      - storage_volumes
      - network_configuration
      - security_groups
  - migrate_data:
      - database_backup_restore
      - file_system_replication
      - configuration_files
  - update_configurations:
      - connection_strings
      - environment_variables
      - dns_records
  - validate_functionality:
      - application_health_checks
      - end_to_end_testing
      - performance_validation
```

### 2. Hybrid Cloud Migration

**Use Case:** Gradual cloud adoption with on-premises integration
**Complexity:** High
**Risk Level:** Medium-High

#### Description
Maintain some components on-premises while migrating others to cloud, requiring secure connectivity and data synchronization.

#### Network Architecture

```hcl
# Terraform configuration for hybrid connectivity
resource "aws_vpc" "main" {
  cidr_block           = "10.0.0.0/16"
  enable_dns_hostnames = true
  enable_dns_support   = true
}

resource "aws_vpn_gateway" "main" {
  vpc_id = aws_vpc.main.id
  
  tags = {
    Name = "hybrid-vpn-gateway"
  }
}

resource "aws_customer_gateway" "main" {
  bgp_asn    = 65000
  ip_address = var.on_premises_public_ip
  type       = "ipsec.1"
  
  tags = {
    Name = "on-premises-gateway"
  }
}

resource "aws_vpn_connection" "main" {
  vpn_gateway_id      = aws_vpn_gateway.main.id
  customer_gateway_id = aws_customer_gateway.main.id
  type                = "ipsec.1"
  static_routes_only  = true
}
```

#### Data Synchronization Pattern

```python
class HybridDataSync:
    def __init__(self):
        self.on_prem_db = OnPremiseDatabase()
        self.cloud_db = CloudDatabase()
        self.sync_log = SyncLogManager()
    
    async def bidirectional_sync(self):
        """Synchronize data between on-premises and cloud"""
        
        # Get last sync timestamp
        last_sync = self.sync_log.get_last_sync_time()
        
        # Sync on-prem changes to cloud
        on_prem_changes = self.on_prem_db.get_changes_since(last_sync)
        for change in on_prem_changes:
            await self.apply_change_to_cloud(change)
        
        # Sync cloud changes to on-prem
        cloud_changes = self.cloud_db.get_changes_since(last_sync)
        for change in cloud_changes:
            await self.apply_change_to_on_prem(change)
        
        # Handle conflicts
        conflicts = self.detect_conflicts(on_prem_changes, cloud_changes)
        for conflict in conflicts:
            await self.resolve_conflict(conflict)
        
        # Update sync timestamp
        self.sync_log.record_sync_completion()
    
    async def apply_change_to_cloud(self, change):
        """Apply on-premises change to cloud database"""
        try:
            if change.operation == "INSERT":
                await self.cloud_db.insert(change.table, change.data)
            elif change.operation == "UPDATE":
                await self.cloud_db.update(change.table, change.key, change.data)
            elif change.operation == "DELETE":
                await self.cloud_db.delete(change.table, change.key)
                
            self.sync_log.record_success(change.id, "cloud")
            
        except Exception as e:
            self.sync_log.record_failure(change.id, "cloud", str(e))
            raise
```

### 3. Multi-Cloud Migration

**Use Case:** Avoiding vendor lock-in or regulatory requirements
**Complexity:** Very High
**Risk Level:** High

#### Description
Distribute workloads across multiple cloud providers for resilience, compliance, or cost optimization.

#### Service Mesh Configuration

```yaml
# Istio configuration for multi-cloud service mesh
apiVersion: networking.istio.io/v1beta1
kind: ServiceEntry
metadata:
  name: aws-service
spec:
  hosts:
  - aws-service.company.com
  ports:
  - number: 443
    name: https
    protocol: HTTPS
  location: MESH_EXTERNAL
  resolution: DNS

---
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: multi-cloud-routing
spec:
  hosts:
  - user-service
  http:
  - match:
    - headers:
        region:
          exact: "us-east"
    route:
    - destination:
        host: aws-service.company.com
      weight: 100
  - match:
    - headers:
        region:
          exact: "eu-west"
    route:
    - destination:
        host: gcp-service.company.com
      weight: 100
  - route:  # Default routing
    - destination:
        host: user-service
        subset: local
      weight: 80
    - destination:
        host: aws-service.company.com
      weight: 20
```

## Feature Flag Patterns

### 1. Progressive Rollout Pattern

**Use Case:** Gradual feature deployment with risk mitigation
**Implementation:**

```python
class ProgressiveRollout:
    def __init__(self, feature_name):
        self.feature_name = feature_name
        self.rollout_percentage = 0
        self.user_buckets = {}
        
    def is_enabled_for_user(self, user_id):
        # Consistent user bucketing
        user_hash = hashlib.md5(f"{self.feature_name}:{user_id}".encode()).hexdigest()
        bucket = int(user_hash, 16) % 100
        
        return bucket < self.rollout_percentage
    
    def increase_rollout(self, target_percentage, step_size=10):
        """Gradually increase rollout percentage"""
        while self.rollout_percentage < target_percentage:
            self.rollout_percentage = min(
                self.rollout_percentage + step_size,
                target_percentage
            )
            
            # Monitor metrics before next increase
            yield self.rollout_percentage
            time.sleep(300)  # Wait 5 minutes between increases
```

### 2. Circuit Breaker Pattern

**Use Case:** Automatic fallback during migration issues

```python
class MigrationCircuitBreaker:
    def __init__(self, failure_threshold=5, timeout=60):
        self.failure_count = 0
        self.failure_threshold = failure_threshold
        self.timeout = timeout
        self.last_failure_time = None
        self.state = 'CLOSED'  # CLOSED, OPEN, HALF_OPEN
    
    def call_new_service(self, request):
        if self.state == 'OPEN':
            if self.should_attempt_reset():
                self.state = 'HALF_OPEN'
            else:
                return self.fallback_to_legacy(request)
        
        try:
            response = self.new_service.process(request)
            self.on_success()
            return response
        except Exception as e:
            self.on_failure()
            return self.fallback_to_legacy(request)
    
    def on_success(self):
        self.failure_count = 0
        self.state = 'CLOSED'
    
    def on_failure(self):
        self.failure_count += 1
        self.last_failure_time = time.time()
        
        if self.failure_count >= self.failure_threshold:
            self.state = 'OPEN'
    
    def should_attempt_reset(self):
        return (time.time() - self.last_failure_time) >= self.timeout
```

## Migration Anti-Patterns

### 1. Big Bang Migration (Anti-Pattern)

**Why to Avoid:**
- High risk of complete system failure
- Difficult to rollback
- Extended downtime
- All-or-nothing deployment

**Better Alternative:** Use incremental migration patterns like Strangler Fig or Parallel Run.

### 2. No Rollback Plan (Anti-Pattern)

**Why to Avoid:**
- Cannot recover from failures
- Increases business risk
- Panic-driven decisions during issues

**Better Alternative:** Always implement comprehensive rollback procedures before migration.

### 3. Insufficient Testing (Anti-Pattern)

**Why to Avoid:**
- Unknown compatibility issues
- Performance degradation
- Data corruption risks

**Better Alternative:** Implement comprehensive testing at each migration phase.

## Pattern Selection Matrix

| Migration Type | Complexity | Downtime Tolerance | Recommended Pattern |
|---------------|------------|-------------------|-------------------|
| Schema Change | Low | Zero | Expand-Contract |
| Schema Change | High | Zero | Parallel Schema |
| Service Replace | Medium | Zero | Strangler Fig |
| Service Update | Low | Zero | Blue-Green |
| Data Migration | High | Some | Event Sourcing |
| Infrastructure | Low | Some | Lift and Shift |
| Infrastructure | High | Zero | Hybrid Cloud |

## Success Metrics

### Technical Metrics
- Migration completion rate
- System availability during migration
- Performance impact (response time, throughput)
- Error rate changes
- Rollback execution time

### Business Metrics
- Customer impact score
- Revenue protection
- Time to value realization
- Stakeholder satisfaction

### Operational Metrics
- Team efficiency
- Knowledge transfer effectiveness
- Post-migration support requirements
- Documentation completeness

## Lessons Learned

### Common Pitfalls
1. **Underestimating data dependencies** - Always map all data relationships
2. **Insufficient monitoring** - Implement comprehensive observability before migration
3. **Poor communication** - Keep all stakeholders informed throughout the process
4. **Rushed timelines** - Allow adequate time for testing and validation
5. **Ignoring performance impact** - Benchmark before and after migration

### Best Practices
1. **Start with low-risk migrations** - Build confidence and experience
2. **Automate everything possible** - Reduce human error and increase repeatability
3. **Test rollback procedures** - Ensure you can recover from any failure
4. **Monitor continuously** - Use real-time dashboards and alerting
5. **Document everything** - Create comprehensive runbooks and documentation

This catalog serves as a reference for selecting appropriate migration patterns based on specific requirements, risk tolerance, and technical constraints.