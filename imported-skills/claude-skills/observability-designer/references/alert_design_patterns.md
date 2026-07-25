# Alert Design Patterns: A Guide to Effective Alerting

## Introduction

Well-designed alerts are the difference between a reliable system and 3 AM pages about non-issues. This guide provides patterns and anti-patterns for creating alerts that provide value without causing fatigue.

## Fundamental Principles

### The Golden Rules of Alerting

1. **Every alert should be actionable** - If you can't do something about it, don't alert
2. **Every alert should require human intelligence** - If a script can handle it, automate the response
3. **Every alert should be novel** - Don't alert on known, ongoing issues
4. **Every alert should represent a user-visible impact** - Internal metrics matter only if users are affected

### Alert Classification

#### Critical Alerts
- Service is completely down
- Data loss is occurring
- Security breach detected
- SLO burn rate indicates imminent SLO violation

#### Warning Alerts  
- Service degradation affecting some users
- Approaching resource limits
- Dependent service issues
- Elevated error rates within SLO

#### Info Alerts
- Deployment notifications
- Capacity planning triggers
- Configuration changes
- Maintenance windows

## Alert Design Patterns

### Pattern 1: Symptoms, Not Causes

**Good**: Alert on user-visible symptoms
```yaml
- alert: HighLatency
  expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 0.5
  for: 5m
  annotations:
    summary: "API latency is high"
    description: "95th percentile latency is {{ $value }}s, above 500ms threshold"
```

**Bad**: Alert on internal metrics that may not affect users
```yaml
- alert: HighCPU
  expr: cpu_usage > 80
  # This might not affect users at all!
```

### Pattern 2: Multi-Window Alerting

Reduce false positives by requiring sustained problems:

```yaml
- alert: ServiceDown
  expr: (
    avg_over_time(up[2m]) == 0  # Short window: immediate detection
    and
    avg_over_time(up[10m]) < 0.8  # Long window: avoid flapping
  )
  for: 1m
```

### Pattern 3: Burn Rate Alerting

Alert based on error budget consumption rate:

```yaml
# Fast burn: 2% of monthly budget in 1 hour
- alert: ErrorBudgetFastBurn  
  expr: (
    error_rate_5m > (14.4 * error_budget_slo)
    and
    error_rate_1h > (14.4 * error_budget_slo)
  )
  for: 2m
  labels:
    severity: critical
    
# Slow burn: 10% of monthly budget in 3 days
- alert: ErrorBudgetSlowBurn
  expr: (
    error_rate_6h > (1.0 * error_budget_slo)
    and  
    error_rate_3d > (1.0 * error_budget_slo)
  )
  for: 15m
  labels:
    severity: warning
```

### Pattern 4: Hysteresis

Use different thresholds for firing and resolving to prevent flapping:

```yaml
- alert: HighErrorRate
  expr: error_rate > 0.05  # Fire at 5%
  for: 5m
  
# Resolution happens automatically when error_rate < 0.03 (3%)
# This prevents flapping around the 5% threshold
```

### Pattern 5: Composite Alerts

Alert when multiple conditions indicate a problem:

```yaml
- alert: ServiceDegraded
  expr: (
    (latency_p95 > latency_threshold)
    or
    (error_rate > error_threshold)
    or 
    (availability < availability_threshold)
  ) and (
    request_rate > min_request_rate  # Only alert if we have traffic
  )
```

### Pattern 6: Contextual Alerting

Include relevant context in alerts:

```yaml
- alert: DatabaseConnections
  expr: db_connections_active / db_connections_max > 0.8
  for: 5m
  annotations:
    summary: "Database connection pool nearly exhausted"
    description: "{{ $labels.database }} has {{ $value | humanizePercentage }} connection utilization"
    runbook_url: "https://runbooks.company.com/database-connections"
    impact: "New requests may be rejected, causing 500 errors"
    suggested_action: "Check for connection leaks or increase pool size"
```

## Alert Routing and Escalation

### Routing by Impact and Urgency

#### Critical Path Services
```yaml
route:
  group_by: ['service']
  routes:
  - match:
      service: 'payment-api'
      severity: 'critical'
    receiver: 'payment-team-pager'
    continue: true
  - match:
      service: 'payment-api' 
      severity: 'warning'
    receiver: 'payment-team-slack'
```

#### Time-Based Routing
```yaml
route:
  routes:
  - match:
      severity: 'critical'
    receiver: 'oncall-pager'
  - match:
      severity: 'warning'
      time: 'business_hours'  # 9 AM - 5 PM
    receiver: 'team-slack'
  - match:
      severity: 'warning'
      time: 'after_hours'
    receiver: 'team-email'  # Lower urgency outside business hours
```

### Escalation Patterns

#### Linear Escalation
```yaml
receivers:
- name: 'primary-oncall'
  pagerduty_configs:
  - escalation_policy: 'P1-Escalation'
    # 0 min: Primary on-call
    # 5 min: Secondary on-call  
    # 15 min: Engineering manager
    # 30 min: Director of engineering
```

#### Severity-Based Escalation
```yaml
# Critical: Immediate escalation
- match:
    severity: 'critical'
  receiver: 'critical-escalation'
  
# Warning: Team-first escalation
- match:
    severity: 'warning'
  receiver: 'team-escalation'
```

## Alert Fatigue Prevention

### Grouping and Suppression

#### Time-Based Grouping
```yaml
route:
  group_wait: 30s        # Wait 30s to group similar alerts
  group_interval: 2m     # Send grouped alerts every 2 minutes
  repeat_interval: 1h    # Re-send unresolved alerts every hour
```

#### Dependent Service Suppression
```yaml
- alert: ServiceDown
  expr: up == 0
  
- alert: HighLatency
  expr: latency_p95 > 1
  # This alert is suppressed when ServiceDown is firing
  inhibit_rules:
  - source_match:
      alertname: 'ServiceDown'
    target_match:
      alertname: 'HighLatency'
    equal: ['service']
```

### Alert Throttling

```yaml
# Limit to 1 alert per 10 minutes for noisy conditions
- alert: HighMemoryUsage
  expr: memory_usage_percent > 85
  for: 10m  # Longer 'for' duration reduces noise
  annotations:
    summary: "Memory usage has been high for 10+ minutes"
```

### Smart Defaults

```yaml
# Use business logic to set intelligent thresholds
- alert: LowTraffic
  expr: request_rate < (
    avg_over_time(request_rate[7d]) * 0.1  # 10% of weekly average
  )
  # Only alert during business hours when low traffic is unusual
  for: 30m
```

## Runbook Integration

### Runbook Structure Template

```markdown
# Alert: {{ $labels.alertname }}

## Immediate Actions
1. Check service status dashboard
2. Verify if users are affected
3. Look at recent deployments/changes

## Investigation Steps
1. Check logs for errors in the last 30 minutes
2. Verify dependent services are healthy  
3. Check resource utilization (CPU, memory, disk)
4. Review recent alerts for patterns

## Resolution Actions
- If deployment-related: Consider rollback
- If resource-related: Scale up or optimize queries
- If dependency-related: Engage appropriate team

## Escalation
- Primary: @team-oncall
- Secondary: @engineering-manager  
- Emergency: @site-reliability-team
```

### Runbook Integration in Alerts

```yaml
annotations:
  runbook_url: "https://runbooks.company.com/alerts/{{ $labels.alertname }}"
  quick_debug: |
    1. curl -s https://{{ $labels.instance }}/health
    2. kubectl logs {{ $labels.pod }} --tail=50
    3. Check dashboard: https://grafana.company.com/d/service-{{ $labels.service }}
```

## Testing and Validation

### Alert Testing Strategies

#### Chaos Engineering Integration
```python
# Test that alerts fire during controlled failures
def test_alert_during_cpu_spike():
    with chaos.cpu_spike(target='payment-api', duration='2m'):
        assert wait_for_alert('HighCPU', timeout=180)
        
def test_alert_during_network_partition():
    with chaos.network_partition(target='database'):
        assert wait_for_alert('DatabaseUnreachable', timeout=60)
```

#### Historical Alert Analysis
```prometheus
# Query to find alerts that fired without incidents
count by (alertname) (
  ALERTS{alertstate="firing"}[30d]
) unless on (alertname) (
  count by (alertname) (
    incident_created{source="alert"}[30d]
  )
)
```

### Alert Quality Metrics

#### Alert Precision
```
Precision = True Positives / (True Positives + False Positives)
```

Track alerts that resulted in actual incidents vs false alarms.

#### Time to Resolution
```prometheus
# Average time from alert firing to resolution
avg_over_time(
  (alert_resolved_timestamp - alert_fired_timestamp)[30d]
) by (alertname)
```

#### Alert Fatigue Indicators
```prometheus
# Alerts per day by team
sum by (team) (
  increase(alerts_fired_total[1d])
)

# Percentage of alerts acknowledged within 15 minutes
sum(alerts_acked_within_15m) / sum(alerts_fired) * 100
```

## Advanced Patterns

### Machine Learning-Enhanced Alerting

#### Anomaly Detection
```yaml
- alert: AnomalousTraffic
  expr: |
    abs(request_rate - predict_linear(request_rate[1h], 300)) / 
    stddev_over_time(request_rate[1h]) > 3
  for: 10m
  annotations:
    summary: "Traffic pattern is anomalous"
    description: "Current traffic deviates from predicted pattern by >3 standard deviations"
```

#### Dynamic Thresholds
```yaml
- alert: DynamicHighLatency
  expr: |
    latency_p95 > (
      quantile_over_time(0.95, latency_p95[7d]) +  # Historical 95th percentile
      2 * stddev_over_time(latency_p95[7d])        # Plus 2 standard deviations
    )
```

### Business Hours Awareness

```yaml
# Different thresholds for business vs off hours
- alert: HighLatencyBusinessHours  
  expr: latency_p95 > 0.2  # Stricter during business hours
  for: 2m
  # Active 9 AM - 5 PM weekdays
  
- alert: HighLatencyOffHours
  expr: latency_p95 > 0.5  # More lenient after hours  
  for: 5m
  # Active nights and weekends
```

### Progressive Alerting

```yaml
# Escalating alert severity based on duration
- alert: ServiceLatencyElevated
  expr: latency_p95 > 0.5
  for: 5m
  labels:
    severity: info
    
- alert: ServiceLatencyHigh
  expr: latency_p95 > 0.5
  for: 15m  # Same condition, longer duration
  labels:
    severity: warning
    
- alert: ServiceLatencyCritical  
  expr: latency_p95 > 0.5
  for: 30m  # Same condition, even longer duration
  labels:
    severity: critical
```

## Anti-Patterns to Avoid

### Anti-Pattern 1: Alerting on Everything
**Problem**: Too many alerts create noise and fatigue
**Solution**: Be selective; only alert on user-impacting issues

### Anti-Pattern 2: Vague Alert Messages
**Problem**: "Service X is down" - which instance? what's the impact?
**Solution**: Include specific details and context

### Anti-Pattern 3: Alerts Without Runbooks
**Problem**: Alerts that don't explain what to do
**Solution**: Every alert must have an associated runbook

### Anti-Pattern 4: Static Thresholds
**Problem**: 80% CPU might be normal during peak hours
**Solution**: Use contextual, adaptive thresholds

### Anti-Pattern 5: Ignoring Alert Quality
**Problem**: Accepting high false positive rates
**Solution**: Regularly review and tune alert precision

## Implementation Checklist

### Pre-Implementation
- [ ] Define alert severity levels and escalation policies
- [ ] Create runbook templates
- [ ] Set up alert routing configuration
- [ ] Define SLOs that alerts will protect

### Alert Development
- [ ] Each alert has clear success criteria
- [ ] Alert conditions tested against historical data
- [ ] Runbook created and accessible
- [ ] Severity and routing configured
- [ ] Context and suggested actions included

### Post-Implementation  
- [ ] Monitor alert precision and recall
- [ ] Regular review of alert fatigue metrics
- [ ] Quarterly alert effectiveness review
- [ ] Team training on alert response procedures

### Quality Assurance
- [ ] Test alerts fire during controlled failures
- [ ] Verify alerts resolve when conditions improve
- [ ] Confirm runbooks are accurate and helpful
- [ ] Validate escalation paths work correctly

Remember: Great alerts are invisible when things work and invaluable when things break. Focus on quality over quantity, and always optimize for the human who will respond to the alert at 3 AM.