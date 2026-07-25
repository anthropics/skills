# Dashboard Best Practices: Design for Insight and Action

## Introduction

A well-designed dashboard is like a good story - it guides you through the data with purpose and clarity. This guide provides practical patterns for creating dashboards that inform decisions and enable quick troubleshooting.

## Design Principles

### The Hierarchy of Information

#### Primary Information (Top Third)
- Service health status
- SLO achievement
- Critical alerts
- Business KPIs

#### Secondary Information (Middle Third)  
- Golden signals (latency, traffic, errors, saturation)
- Resource utilization
- Throughput and performance metrics

#### Tertiary Information (Bottom Third)
- Detailed breakdowns
- Historical trends
- Dependency status
- Debug information

### Visual Design Principles

#### Rule of 7±2
- Maximum 7±2 panels per screen
- Group related information together
- Use sections to organize complexity

#### Color Psychology
- **Red**: Critical issues, danger, immediate attention needed
- **Yellow/Orange**: Warnings, caution, degraded state
- **Green**: Healthy, normal operation, success
- **Blue**: Information, neutral metrics, capacity
- **Gray**: Disabled, unknown, or baseline states

#### Chart Selection Guide
- **Line charts**: Time series, trends, comparisons over time
- **Bar charts**: Categorical comparisons, top N lists
- **Gauges**: Single value with defined good/bad ranges
- **Stat panels**: Key metrics, percentages, counts
- **Heatmaps**: Distribution data, correlation analysis
- **Tables**: Detailed breakdowns, multi-dimensional data

## Dashboard Archetypes

### The Overview Dashboard

**Purpose**: High-level health check and business metrics
**Audience**: Executives, managers, cross-team stakeholders
**Update Frequency**: 5-15 minutes

```yaml
sections:
  - title: "Business Health"
    panels:
      - service_availability_summary
      - revenue_per_hour  
      - active_users
      - conversion_rate
      
  - title: "System Health"  
    panels:
      - critical_alerts_count
      - slo_achievement_summary
      - error_budget_remaining
      - deployment_status
```

### The SRE Operational Dashboard

**Purpose**: Real-time monitoring and incident response
**Audience**: SRE, on-call engineers
**Update Frequency**: 15-30 seconds

```yaml
sections:
  - title: "Service Status"
    panels:
      - service_up_status
      - active_incidents
      - recent_deployments
      
  - title: "Golden Signals"
    panels:
      - latency_percentiles
      - request_rate
      - error_rate  
      - resource_saturation
      
  - title: "Infrastructure"
    panels:
      - cpu_memory_utilization
      - network_io
      - disk_space
```

### The Developer Debug Dashboard

**Purpose**: Deep-dive troubleshooting and performance analysis
**Audience**: Development teams
**Update Frequency**: 30 seconds - 2 minutes

```yaml
sections:
  - title: "Application Performance"
    panels:
      - endpoint_latency_breakdown
      - database_query_performance
      - cache_hit_rates
      - queue_depths
      
  - title: "Errors and Logs"
    panels:
      - error_rate_by_endpoint
      - log_volume_by_level
      - exception_types
      - slow_queries
```

## Layout Patterns

### The F-Pattern Layout

Based on eye-tracking studies, users scan in an F-pattern:

```
[Critical Status] [SLO Summary  ] [Error Budget ]
[Latency       ] [Traffic      ] [Errors       ]
[Saturation    ] [Resource Use ] [Detailed View]
[Historical    ] [Dependencies ] [Debug Info   ]
```

### The Z-Pattern Layout  

For executive dashboards, follow the Z-pattern:

```
[Business KPIs          ] → [System Status]
      ↓                          ↓
[Trend Analysis         ] ← [Key Metrics ]
```

### Responsive Design

#### Desktop (1920x1080)
- 24-column grid
- Panels can be 6, 8, 12, or 24 units wide
- 4-6 rows visible without scrolling

#### Laptop (1366x768)
- Stack wider panels vertically
- Reduce panel heights
- Prioritize most critical information

#### Mobile (768px width)
- Single column layout
- Simplified panels
- Touch-friendly controls

## Effective Panel Design

### Stat Panels

```yaml
# Good: Clear value with context
- title: "API Availability"
  type: stat
  targets:
    - expr: avg(up{service="api"}) * 100
  field_config:
    unit: percent
    thresholds:
      steps:
        - color: red
          value: 0
        - color: yellow  
          value: 99
        - color: green
          value: 99.9
  options:
    color_mode: background
    text_mode: value_and_name
```

### Time Series Panels

```yaml  
# Good: Multiple related metrics with clear legend
- title: "Request Latency"
  type: timeseries
  targets:
    - expr: histogram_quantile(0.50, rate(http_duration_bucket[5m]))
      legend: "P50"
    - expr: histogram_quantile(0.95, rate(http_duration_bucket[5m]))
      legend: "P95"  
    - expr: histogram_quantile(0.99, rate(http_duration_bucket[5m]))
      legend: "P99"
  field_config:
    unit: ms
    custom:
      draw_style: line
      fill_opacity: 10
  options:
    legend:
      display_mode: table
      placement: bottom
      values: [min, max, mean, last]
```

### Table Panels

```yaml
# Good: Top N with relevant columns
- title: "Slowest Endpoints"
  type: table
  targets:
    - expr: topk(10, histogram_quantile(0.95, sum by (handler)(rate(http_duration_bucket[5m]))))
      format: table
      instant: true
  transformations:
    - id: organize
      options:
        exclude_by_name: 
          Time: true
        rename_by_name:
          Value: "P95 Latency (ms)"
          handler: "Endpoint"
```

## Color and Visualization Best Practices

### Threshold Configuration

```yaml
# Traffic light system with meaningful boundaries
thresholds:
  steps:
    - color: green     # Good performance
      value: null      # Default
    - color: yellow    # Degraded performance  
      value: 95        # 95th percentile of historical normal
    - color: orange    # Poor performance
      value: 99        # 99th percentile of historical normal
    - color: red       # Critical performance
      value: 99.9      # Worst case scenario
```

### Color Blind Friendly Palettes

```yaml
# Use patterns and shapes in addition to color
field_config:
  overrides:
    - matcher:
        id: byName
        options: "Critical"
      properties:
        - id: color
          value:
            mode: fixed
            fixed_color: "#d73027"  # Red-orange for protanopia
        - id: custom.draw_style
          value: "points"           # Different shape
```

### Consistent Color Semantics

- **Success/Health**: Green (#28a745)
- **Warning/Degraded**: Yellow (#ffc107)  
- **Error/Critical**: Red (#dc3545)
- **Information**: Blue (#007bff)
- **Neutral**: Gray (#6c757d)

## Time Range Strategy

### Default Time Ranges by Dashboard Type

#### Real-time Operational
- **Default**: Last 15 minutes
- **Quick options**: 5m, 15m, 1h, 4h
- **Auto-refresh**: 15-30 seconds

#### Troubleshooting  
- **Default**: Last 1 hour
- **Quick options**: 15m, 1h, 4h, 12h, 1d
- **Auto-refresh**: 1 minute

#### Business Review
- **Default**: Last 24 hours
- **Quick options**: 1d, 7d, 30d, 90d
- **Auto-refresh**: 5 minutes

#### Capacity Planning
- **Default**: Last 7 days  
- **Quick options**: 7d, 30d, 90d, 1y
- **Auto-refresh**: 15 minutes

### Time Range Annotations

```yaml
# Add context for time-based events
annotations:
  - name: "Deployments"
    datasource: "Prometheus"
    expr: "deployment_timestamp"
    title_format: "Deploy {{ version }}"
    text_format: "Deployed version {{ version }} to {{ environment }}"
    
  - name: "Incidents"  
    datasource: "Incident API"
    query: "incidents.json?service={{ service }}"
    color: "red"
```

## Interactive Features

### Template Variables

```yaml
# Service selector
- name: service
  type: query
  query: label_values(up, service)
  current:
    text: All
    value: $__all
  include_all: true
  multi: true
  
# Environment selector  
- name: environment
  type: query
  query: label_values(up{service="$service"}, environment)
  current:
    text: production
    value: production
```

### Drill-Down Links

```yaml
# Panel-level drill-downs
- title: "Error Rate"
  type: timeseries
  # ... other config ...
  options:
    data_links:
      - title: "View Error Logs"
        url: "/d/logs-dashboard?var-service=${__field.labels.service}&from=${__from}&to=${__to}"
      - title: "Error Traces"  
        url: "/d/traces-dashboard?var-service=${__field.labels.service}"
```

### Dynamic Panel Titles

```yaml
- title: "${service} - Request Rate"  # Uses template variable
  type: timeseries
  # Title updates automatically when service variable changes
```

## Performance Optimization

### Query Optimization

#### Use Recording Rules
```yaml
# Instead of complex queries in dashboards
groups:
  - name: http_requests
    rules:
      - record: http_request_rate_5m
        expr: sum(rate(http_requests_total[5m])) by (service, method, handler)
        
      - record: http_request_latency_p95_5m
        expr: histogram_quantile(0.95, sum(rate(http_request_duration_seconds_bucket[5m])) by (service, le))
```

#### Limit Data Points
```yaml
# Good: Reasonable resolution for dashboard
- expr: http_request_rate_5m[1h]
  interval: 15s  # One point every 15 seconds

# Bad: Too many points for visualization  
- expr: http_request_rate_1s[1h]  # 3600 points!
```

### Dashboard Performance

#### Panel Limits
- **Maximum panels per dashboard**: 20-30
- **Maximum queries per panel**: 10
- **Maximum time series per panel**: 50

#### Caching Strategy
```yaml
# Use appropriate cache headers
cache_timeout: 30  # Cache for 30 seconds on fast-changing panels
cache_timeout: 300 # Cache for 5 minutes on slow-changing panels
```

## Accessibility

### Screen Reader Support

```yaml
# Provide text alternatives for visual elements
- title: "Service Health Status"
  type: stat
  options:
    text_mode: value_and_name  # Includes both value and description
  field_config:
    mappings:
      - options:
          "1": 
            text: "Healthy"
            color: "green"
          "0":
            text: "Unhealthy"  
            color: "red"
```

### Keyboard Navigation

- Ensure all interactive elements are keyboard accessible
- Provide logical tab order
- Include skip links for complex dashboards

### High Contrast Mode

```yaml
# Test dashboards work in high contrast mode
theme: high_contrast
colors:
  - "#000000"  # Pure black
  - "#ffffff"  # Pure white  
  - "#ffff00"  # Pure yellow
  - "#ff0000"  # Pure red
```

## Testing and Validation

### Dashboard Testing Checklist

#### Functional Testing
- [ ] All panels load without errors
- [ ] Template variables filter correctly
- [ ] Time range changes update all panels
- [ ] Drill-down links work as expected
- [ ] Auto-refresh functions properly

#### Visual Testing
- [ ] Dashboard renders correctly on different screen sizes
- [ ] Colors are distinguishable and meaningful
- [ ] Text is readable at normal zoom levels
- [ ] Legends and labels are clear

#### Performance Testing  
- [ ] Dashboard loads in < 5 seconds
- [ ] No queries timeout under normal load
- [ ] Auto-refresh doesn't cause browser lag
- [ ] Memory usage remains reasonable

#### Usability Testing
- [ ] New team members can understand the dashboard
- [ ] Action items are clear during incidents
- [ ] Key information is quickly discoverable
- [ ] Dashboard supports common troubleshooting workflows

## Maintenance and Governance

### Dashboard Lifecycle

#### Creation
1. Define dashboard purpose and audience
2. Identify key metrics and success criteria
3. Design layout following established patterns
4. Implement with consistent styling
5. Test with real data and user scenarios

#### Maintenance
- **Weekly**: Check for broken panels or queries
- **Monthly**: Review dashboard usage analytics  
- **Quarterly**: Gather user feedback and iterate
- **Annually**: Major review and potential redesign

#### Retirement
- Archive dashboards that are no longer used
- Migrate users to replacement dashboards
- Document lessons learned

### Dashboard Standards

```yaml
# Organization dashboard standards
standards:
  naming_convention: "[Team] [Service] - [Purpose]"
  tags: [team, service_type, environment, purpose]
  refresh_intervals: [15s, 30s, 1m, 5m, 15m]
  time_ranges: [5m, 15m, 1h, 4h, 1d, 7d, 30d]
  color_scheme: "company_standard"
  max_panels_per_dashboard: 25
```

## Advanced Patterns

### Composite Dashboards

```yaml
# Dashboard that includes panels from other dashboards
- title: "Service Overview"
  type: dashlist
  targets:
    - "service-health"
    - "service-performance" 
    - "service-business-metrics"
  options:
    show_headings: true
    max_items: 10
```

### Dynamic Dashboard Generation

```python
# Generate dashboards from service definitions
def generate_service_dashboard(service_config):
    panels = []
    
    # Always include golden signals
    panels.extend(generate_golden_signals_panels(service_config))
    
    # Add service-specific panels
    if service_config.type == 'database':
        panels.extend(generate_database_panels(service_config))
    elif service_config.type == 'queue':
        panels.extend(generate_queue_panels(service_config))
        
    return {
        'title': f"{service_config.name} - Operational Dashboard",
        'panels': panels,
        'variables': generate_variables(service_config)
    }
```

### A/B Testing for Dashboards

```yaml
# Test different dashboard designs with different teams
experiment:
  name: "dashboard_layout_test"
  variants:
    - name: "traditional_layout"
      weight: 50
      config: "dashboard_v1.json"
    - name: "f_pattern_layout"  
      weight: 50
      config: "dashboard_v2.json"
  success_metrics:
    - "time_to_insight"
    - "user_satisfaction"
    - "troubleshooting_efficiency"
```

Remember: A dashboard should tell a story about your system's health and guide users toward the right actions. Focus on clarity over complexity, and always optimize for the person who will use it during a stressful incident.