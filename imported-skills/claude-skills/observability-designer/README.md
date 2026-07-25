# Observability Designer

A comprehensive toolkit for designing production-ready observability strategies including SLI/SLO frameworks, alert optimization, and dashboard generation.

## Overview

The Observability Designer skill provides three powerful Python scripts that help you create, optimize, and maintain observability systems:

- **SLO Designer**: Generate complete SLI/SLO frameworks with error budgets and burn rate alerts
- **Alert Optimizer**: Analyze and optimize existing alert configurations to reduce noise and improve effectiveness
- **Dashboard Generator**: Create comprehensive dashboard specifications with role-based layouts and drill-down paths

## Quick Start

### Prerequisites

- Python 3.7+
- No external dependencies required (uses Python standard library only)

### Basic Usage

```bash
# Generate SLO framework for a service
python3 scripts/slo_designer.py --service-type api --criticality critical --user-facing true --service-name payment-service

# Optimize existing alerts
python3 scripts/alert_optimizer.py --input assets/sample_alerts.json --analyze-only

# Generate a dashboard specification
python3 scripts/dashboard_generator.py --service-type web --name "Customer Portal" --role sre
```

## Scripts Documentation

### SLO Designer (`slo_designer.py`)

Generates comprehensive SLO frameworks based on service characteristics.

#### Features
- **Automatic SLI Selection**: Recommends appropriate SLIs based on service type
- **Target Setting**: Suggests SLO targets based on service criticality
- **Error Budget Calculation**: Computes error budgets and burn rate thresholds
- **Multi-Window Burn Rate Alerts**: Generates 4-window burn rate alerting rules
- **SLA Recommendations**: Provides customer-facing SLA guidance

#### Usage Examples

```bash
# From service definition file
python3 scripts/slo_designer.py --input assets/sample_service_api.json --output slo_framework.json

# From command line parameters
python3 scripts/slo_designer.py \
    --service-type api \
    --criticality critical \
    --user-facing true \
    --service-name payment-service \
    --output payment_slos.json

# Generate and display summary only
python3 scripts/slo_designer.py --input assets/sample_service_web.json --summary-only
```

#### Service Definition Format

```json
{
  "name": "payment-service",
  "type": "api",
  "criticality": "critical",
  "user_facing": true,
  "description": "Handles payment processing",
  "team": "payments",
  "environment": "production",
  "dependencies": [
    {
      "name": "user-service",
      "type": "api",
      "criticality": "high"
    }
  ]
}
```

#### Supported Service Types
- **api**: REST APIs, GraphQL services
- **web**: Web applications, SPAs
- **database**: Database services, data stores
- **queue**: Message queues, event streams
- **batch**: Batch processing jobs
- **ml**: Machine learning services

#### Criticality Levels
- **critical**: 99.99% availability, <100ms P95 latency, <0.1% error rate
- **high**: 99.9% availability, <200ms P95 latency, <0.5% error rate
- **medium**: 99.5% availability, <500ms P95 latency, <1% error rate
- **low**: 99% availability, <1s P95 latency, <2% error rate

### Alert Optimizer (`alert_optimizer.py`)

Analyzes existing alert configurations and provides optimization recommendations.

#### Features
- **Noise Detection**: Identifies alerts with high false positive rates
- **Coverage Analysis**: Finds gaps in monitoring coverage
- **Duplicate Detection**: Locates redundant or overlapping alerts  
- **Threshold Analysis**: Reviews alert thresholds for appropriateness
- **Fatigue Assessment**: Evaluates alert volume and routing

#### Usage Examples

```bash
# Analyze existing alerts
python3 scripts/alert_optimizer.py --input assets/sample_alerts.json --analyze-only

# Generate optimized configuration
python3 scripts/alert_optimizer.py \
    --input assets/sample_alerts.json \
    --output optimized_alerts.json

# Generate HTML report
python3 scripts/alert_optimizer.py \
    --input assets/sample_alerts.json \
    --report alert_analysis.html \
    --format html
```

#### Alert Configuration Format

```json
{
  "alerts": [
    {
      "alert": "HighLatency",
      "expr": "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 0.5",
      "for": "5m",
      "labels": {
        "severity": "warning",
        "service": "payment-service"
      },
      "annotations": {
        "summary": "High request latency detected",
        "runbook_url": "https://runbooks.company.com/high-latency"
      },
      "historical_data": {
        "fires_per_day": 2.5,
        "false_positive_rate": 0.15
      }
    }
  ],
  "services": [
    {
      "name": "payment-service",
      "criticality": "critical"
    }
  ]
}
```

#### Analysis Categories
- **Golden Signals**: Latency, traffic, errors, saturation
- **Resource Utilization**: CPU, memory, disk, network
- **Business Metrics**: Revenue, conversion, user engagement
- **Security**: Auth failures, suspicious activity
- **Availability**: Uptime, health checks

### Dashboard Generator (`dashboard_generator.py`)

Creates comprehensive dashboard specifications with role-based optimization.

#### Features
- **Role-Based Layouts**: Optimized for SRE, Developer, Executive, and Ops personas
- **Golden Signals Coverage**: Automatic inclusion of key monitoring metrics
- **Service-Type Specific Panels**: Tailored panels based on service characteristics
- **Interactive Elements**: Template variables, drill-down paths, time range controls
- **Grafana Compatibility**: Generates Grafana-compatible JSON

#### Usage Examples

```bash
# From service definition
python3 scripts/dashboard_generator.py \
    --input assets/sample_service_web.json \
    --output dashboard.json

# With specific role optimization
python3 scripts/dashboard_generator.py \
    --service-type api \
    --name "Payment Service" \
    --role developer \
    --output payment_dev_dashboard.json

# Generate Grafana-compatible JSON
python3 scripts/dashboard_generator.py \
    --input assets/sample_service_api.json \
    --output dashboard.json \
    --format grafana

# With documentation
python3 scripts/dashboard_generator.py \
    --service-type web \
    --name "Customer Portal" \
    --output portal_dashboard.json \
    --doc-output portal_docs.md
```

#### Target Roles

- **sre**: Focus on availability, latency, errors, resource utilization
- **developer**: Emphasize latency, errors, throughput, business metrics  
- **executive**: Highlight availability, business metrics, user experience
- **ops**: Priority on resource utilization, capacity, alerts, deployments

#### Panel Types
- **Stat**: Single value displays with thresholds
- **Gauge**: Resource utilization and capacity metrics
- **Timeseries**: Trend analysis and historical data
- **Table**: Top N lists and detailed breakdowns
- **Heatmap**: Distribution and correlation analysis

## Sample Data

The `assets/` directory contains sample configurations for testing:

- `sample_service_api.json`: Critical API service definition
- `sample_service_web.json`: High-priority web application definition  
- `sample_alerts.json`: Alert configuration with optimization opportunities

The `expected_outputs/` directory shows example outputs from each script:

- `sample_slo_framework.json`: Complete SLO framework for API service
- `optimized_alerts.json`: Optimized alert configuration
- `sample_dashboard.json`: SRE dashboard specification

## Best Practices

### SLO Design
- Start with 1-2 SLOs per service and iterate
- Choose SLIs that directly impact user experience
- Set targets based on user needs, not technical capabilities
- Use error budgets to balance reliability and velocity

### Alert Optimization
- Every alert must be actionable
- Alert on symptoms, not causes
- Use multi-window burn rate alerts for SLO protection
- Implement proper escalation and routing policies

### Dashboard Design  
- Follow the F-pattern for visual hierarchy
- Use consistent color semantics across dashboards
- Include drill-down paths for effective troubleshooting
- Optimize for the target role's specific needs

## Integration Patterns

### CI/CD Integration
```bash
# Generate SLOs during service onboarding
python3 scripts/slo_designer.py --input service-config.json --output slos.json

# Validate alert configurations in pipeline
python3 scripts/alert_optimizer.py --input alerts.json --analyze-only --report validation.html

# Auto-generate dashboards for new services
python3 scripts/dashboard_generator.py --input service-config.json --format grafana --output dashboard.json
```

### Monitoring Stack Integration
- **Prometheus**: Generated alert rules and recording rules
- **Grafana**: Dashboard JSON for direct import
- **Alertmanager**: Routing and escalation policies
- **PagerDuty**: Escalation configuration

### GitOps Workflow
1. Store service definitions in version control
2. Generate observability configurations in CI/CD
3. Deploy configurations via GitOps
4. Monitor effectiveness and iterate

## Advanced Usage

### Custom SLO Targets
Override default targets by including them in service definitions:

```json
{
  "name": "special-service",
  "type": "api",
  "criticality": "high",
  "custom_slos": {
    "availability_target": 0.9995,
    "latency_p95_target_ms": 150,
    "error_rate_target": 0.002
  }
}
```

### Alert Rule Templates
Use template variables for reusable alert rules:

```yaml
# Generated Prometheus alert rule
- alert: {{ service_name }}_HighLatency
  expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket{service="{{ service_name }}"}[5m])) > {{ latency_threshold }}
  for: 5m
  labels:
    severity: warning
    service: "{{ service_name }}"
```

### Dashboard Variants
Generate multiple dashboard variants for different use cases:

```bash
# SRE operational dashboard
python3 scripts/dashboard_generator.py --input service.json --role sre --output sre-dashboard.json

# Developer debugging dashboard  
python3 scripts/dashboard_generator.py --input service.json --role developer --output dev-dashboard.json

# Executive business dashboard
python3 scripts/dashboard_generator.py --input service.json --role executive --output exec-dashboard.json
```

## Troubleshooting

### Common Issues

#### Script Execution Errors
- Ensure Python 3.7+ is installed
- Check file paths and permissions
- Validate JSON syntax in input files

#### Invalid Service Definitions
- Required fields: `name`, `type`, `criticality`
- Valid service types: `api`, `web`, `database`, `queue`, `batch`, `ml`
- Valid criticality levels: `critical`, `high`, `medium`, `low`

#### Missing Historical Data
- Alert historical data is optional but improves analysis
- Include `fires_per_day` and `false_positive_rate` when available
- Use monitoring system APIs to populate historical metrics

### Debug Mode
Enable verbose logging by setting environment variable:

```bash
export DEBUG=1
python3 scripts/slo_designer.py --input service.json
```

## Contributing

### Development Setup
```bash
# Clone the repository
git clone <repository-url>
cd engineering/observability-designer

# Run tests
python3 -m pytest tests/

# Lint code
python3 -m flake8 scripts/
```

### Adding New Features
1. Follow existing code patterns and error handling
2. Include comprehensive docstrings and type hints  
3. Add test cases for new functionality
4. Update documentation and examples

## Support

For questions, issues, or feature requests:
- Check existing documentation and examples
- Review the reference materials in `references/`
- Open an issue with detailed reproduction steps
- Include sample configurations when reporting bugs

---

*This skill is part of the Claude Skills marketplace. For more information about observability best practices, see the reference documentation in the `references/` directory.*