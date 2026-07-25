# SLO Cookbook: A Practical Guide to Service Level Objectives

## Introduction

Service Level Objectives (SLOs) are a key tool for managing service reliability. This cookbook provides practical guidance for implementing SLOs that actually improve system reliability rather than just creating meaningless metrics.

## Fundamentals

### The SLI/SLO/SLA Hierarchy

- **SLI (Service Level Indicator)**: A quantifiable measure of service quality
- **SLO (Service Level Objective)**: A target range of values for an SLI
- **SLA (Service Level Agreement)**: A business agreement with consequences for missing SLO targets

### Golden Rule of SLOs

**Start simple, iterate based on learning.** Your first SLOs won't be perfect, and that's okay.

## Choosing Good SLIs

### The Four Golden Signals

1. **Latency**: How long requests take to complete
2. **Traffic**: How many requests are coming in
3. **Errors**: How many requests are failing
4. **Saturation**: How "full" your service is

### SLI Selection Criteria

A good SLI should be:
- **Measurable**: You can collect data for it
- **Meaningful**: It reflects user experience
- **Controllable**: You can take action to improve it
- **Proportional**: Changes in the SLI reflect changes in user happiness

### Service Type Specific SLIs

#### HTTP APIs
- **Request latency**: P95 or P99 response time
- **Availability**: Proportion of successful requests (non-5xx)
- **Throughput**: Requests per second capacity

```prometheus
# Availability SLI
sum(rate(http_requests_total{code!~"5.."}[5m])) / sum(rate(http_requests_total[5m]))

# Latency SLI  
histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))
```

#### Batch Jobs
- **Freshness**: Age of the last successful run
- **Correctness**: Proportion of jobs completing successfully
- **Throughput**: Items processed per unit time

#### Data Pipelines
- **Data freshness**: Time since last successful update
- **Data quality**: Proportion of records passing validation
- **Processing latency**: Time from ingestion to availability

### Anti-Patterns in SLI Selection

❌ **Don't use**: CPU usage, memory usage, disk space as primary SLIs
- These are symptoms, not user-facing impacts

❌ **Don't use**: Counts instead of rates or proportions
- "Number of errors" vs "Error rate"

❌ **Don't use**: Internal metrics that users don't care about
- Queue depth, cache hit rate (unless they directly impact user experience)

## Setting SLO Targets

### The Art of Target Setting

Setting SLO targets is balancing act between:
- **User happiness**: Targets should reflect acceptable user experience
- **Business value**: Tighter SLOs cost more to maintain
- **Current performance**: Targets should be achievable but aspirational

### Target Setting Strategies

#### Historical Performance Method
1. Collect 4-6 weeks of historical data
2. Calculate the worst user-visible performance in that period
3. Set your SLO slightly better than the worst acceptable performance

#### User Journey Mapping
1. Map critical user journeys
2. Identify acceptable performance for each step
3. Work backwards to component SLOs

#### Error Budget Approach
1. Decide how much unreliability you can afford
2. Set SLO targets based on acceptable error budget consumption
3. Example: 99.9% availability = 43.8 minutes downtime per month

### SLO Target Examples by Service Criticality

#### Critical Services (Revenue Impact)
- **Availability**: 99.95% - 99.99%
- **Latency (P95)**: 100-200ms
- **Error Rate**: < 0.1%

#### High Priority Services  
- **Availability**: 99.9% - 99.95%
- **Latency (P95)**: 200-500ms
- **Error Rate**: < 0.5%

#### Standard Services
- **Availability**: 99.5% - 99.9%
- **Latency (P95)**: 500ms - 1s
- **Error Rate**: < 1%

## Error Budget Management

### What is an Error Budget?

Your error budget is the maximum amount of unreliability you can accumulate while still meeting your SLO. It's calculated as:

```
Error Budget = (1 - SLO) × Time Window
```

For a 99.9% availability SLO over 30 days:
```
Error Budget = (1 - 0.999) × 30 days = 0.001 × 30 days = 43.8 minutes
```

### Error Budget Policies

Define what happens when you consume your error budget:

#### Conservative Policy (High-Risk Services)
- **> 50% consumed**: Freeze non-critical feature releases
- **> 75% consumed**: Focus entirely on reliability improvements  
- **> 90% consumed**: Consider emergency measures (traffic shaping, etc.)

#### Balanced Policy (Standard Services)
- **> 75% consumed**: Increase focus on reliability work
- **> 90% consumed**: Pause feature work, focus on reliability

#### Aggressive Policy (Early Stage Services)
- **> 90% consumed**: Review but continue normal operations
- **100% consumed**: Evaluate SLO appropriateness

### Burn Rate Alerting

Multi-window burn rate alerts help you catch SLO violations before they become critical:

```yaml
# Fast burn: 2% budget consumed in 1 hour
- alert: FastBurnSLOViolation
  expr: (
    (1 - (sum(rate(http_requests_total{code!~"5.."}[5m])) / sum(rate(http_requests_total[5m])))) > (14.4 * 0.001)
    and
    (1 - (sum(rate(http_requests_total{code!~"5.."}[1h])) / sum(rate(http_requests_total[1h])))) > (14.4 * 0.001)
  )
  for: 2m

# Slow burn: 10% budget consumed in 3 days  
- alert: SlowBurnSLOViolation
  expr: (
    (1 - (sum(rate(http_requests_total{code!~"5.."}[6h])) / sum(rate(http_requests_total[6h])))) > (1.0 * 0.001)
    and
    (1 - (sum(rate(http_requests_total{code!~"5.."}[3d])) / sum(rate(http_requests_total[3d])))) > (1.0 * 0.001)
  )
  for: 15m
```

## Implementation Patterns

### The SLO Implementation Ladder

#### Level 1: Basic SLOs
- Choose 1-2 SLIs that matter most to users
- Set aspirational but achievable targets
- Implement basic alerting when SLOs are missed

#### Level 2: Operational SLOs
- Add burn rate alerting
- Create error budget dashboards
- Establish error budget policies
- Regular SLO review meetings

#### Level 3: Advanced SLOs
- Multi-window burn rate alerts
- Automated error budget policy enforcement
- SLO-driven incident prioritization
- Integration with CI/CD for deployment decisions

### SLO Measurement Architecture

#### Push vs Pull Metrics
- **Pull** (Prometheus): Good for infrastructure metrics, real-time alerting
- **Push** (StatsD): Good for application metrics, business events

#### Measurement Points
- **Server-side**: More reliable, easier to implement
- **Client-side**: Better reflects user experience
- **Synthetic**: Consistent, predictable, may not reflect real user experience

### SLO Dashboard Design

Essential elements for SLO dashboards:

1. **Current SLO Achievement**: Large, prominent display
2. **Error Budget Remaining**: Visual indicator (gauge, progress bar)
3. **Burn Rate**: Time series showing error budget consumption rate
4. **Historical Trends**: 4-week view of SLO achievement
5. **Alerts**: Current and recent SLO-related alerts

## Advanced Topics

### Dependency SLOs

For services with dependencies:

```
SLO_service ≤ min(SLO_inherent, ∏SLO_dependencies)
```

If your service depends on 3 other services each with 99.9% SLO:
```
Maximum_SLO = 0.999³ = 0.997 = 99.7%
```

### User Journey SLOs

Track end-to-end user experiences:

```prometheus
# Registration success rate
sum(rate(user_registration_success_total[5m])) / sum(rate(user_registration_attempts_total[5m]))

# Purchase completion latency
histogram_quantile(0.95, rate(purchase_completion_duration_seconds_bucket[5m]))
```

### SLOs for Batch Systems

Special considerations for non-request/response systems:

#### Freshness SLO
```prometheus
# Data should be no more than 4 hours old
(time() - last_successful_update_timestamp) < (4 * 3600)
```

#### Throughput SLO
```prometheus
# Should process at least 1000 items per hour
rate(items_processed_total[1h]) >= 1000
```

#### Quality SLO
```prometheus
# At least 99.5% of records should pass validation
sum(rate(records_valid_total[5m])) / sum(rate(records_processed_total[5m])) >= 0.995
```

## Common Mistakes and How to Avoid Them

### Mistake 1: Too Many SLOs
**Problem**: Drowning in metrics, losing focus
**Solution**: Start with 1-2 SLOs per service, add more only when needed

### Mistake 2: Internal Metrics as SLIs
**Problem**: Optimizing for metrics that don't impact users
**Solution**: Always ask "If this metric changes, do users notice?"

### Mistake 3: Perfectionist SLOs
**Problem**: 99.99% SLO when 99.9% would be fine
**Solution**: Higher SLOs cost exponentially more; pick the minimum acceptable level

### Mistake 4: Ignoring Error Budgets
**Problem**: Treating any SLO miss as an emergency
**Solution**: Error budgets exist to be spent; use them to balance feature velocity and reliability

### Mistake 5: Static SLOs
**Problem**: Setting SLOs once and never updating them
**Solution**: Review SLOs quarterly; adjust based on user feedback and business changes

## SLO Review Process

### Monthly SLO Review Agenda

1. **SLO Achievement Review**: Did we meet our SLOs?
2. **Error Budget Analysis**: How did we spend our error budget?
3. **Incident Correlation**: Which incidents impacted our SLOs?
4. **SLI Quality Assessment**: Are our SLIs still meaningful?
5. **Target Adjustment**: Should we change any targets?

### Quarterly SLO Health Check

1. **User Impact Validation**: Survey users about acceptable performance
2. **Business Alignment**: Do SLOs still reflect business priorities?
3. **Measurement Quality**: Are we measuring the right things?
4. **Cost/Benefit Analysis**: Are tighter SLOs worth the investment?

## Tooling and Automation

### Essential Tools

1. **Metrics Collection**: Prometheus, InfluxDB, CloudWatch
2. **Alerting**: Alertmanager, PagerDuty, OpsGenie  
3. **Dashboards**: Grafana, DataDog, New Relic
4. **SLO Platforms**: Sloth, Pyrra, Service Level Blue

### Automation Opportunities

- **Burn rate alert generation** from SLO definitions
- **Dashboard creation** from SLO specifications
- **Error budget calculation** and tracking
- **Release blocking** based on error budget consumption

## Getting Started Checklist

- [ ] Identify your service's critical user journeys
- [ ] Choose 1-2 SLIs that best reflect user experience
- [ ] Collect 4-6 weeks of baseline data
- [ ] Set initial SLO targets based on historical performance
- [ ] Implement basic SLO monitoring and alerting
- [ ] Create an SLO dashboard
- [ ] Define error budget policies
- [ ] Schedule monthly SLO reviews
- [ ] Plan for quarterly SLO health checks

Remember: SLOs are a journey, not a destination. Start simple, learn from experience, and iterate toward better reliability management.