---
name: "observability-designer"
description: "Design production-ready observability strategies combining metrics, logs, and traces. Includes SLI/SLO design, golden-signals monitoring, alert optimization. Use when adding observability to a new service, refactoring alerting that is too noisy, or designing an SLO program before scaling production load."
---

# Observability Designer (POWERFUL)

**Category:** Engineering  
**Tier:** POWERFUL  
**Description:** Design comprehensive observability strategies for production systems including SLI/SLO frameworks, alerting optimization, and dashboard generation.

## Overview

Observability Designer creates production-ready dashboards, alert configurations, and monitoring strategies across the three pillars (metrics, logs, traces).

**When NOT to use → slo-architect.** For SLO/SLI design with error-budget math, multi-window burn-rate alerting thresholds, and SLO review gates, route to `slo-architect` — it is the authoritative skill for that half. This skill's `slo_designer.py` produces a quick scaffold only. This skill's lane: dashboards (`dashboard_generator.py`) and alert-noise reduction (`alert_optimizer.py`).

## Quick Start

```bash
# Dashboard spec (Grafana JSON + docs) for a service
python3 scripts/dashboard_generator.py --service-type api --name payments --criticality critical --role sre --format grafana -o dashboard.json --doc-output dashboard.md

# Analyze an existing alert config for noise, duplicates, and coverage gaps
python3 scripts/alert_optimizer.py --input alerts.json --analyze-only --report alert_report.json
# ...then emit the optimized config once the report is reviewed:
python3 scripts/alert_optimizer.py --input alerts.json --output alerts_optimized.json

# Quick SLO scaffold (hand off to slo-architect for the real error-budget work)
python3 scripts/slo_designer.py --service-type api --criticality high --user-facing true --service-name payments -o slo_scaffold.json
```

**Verification loop:** after deploying optimized alerts, track the report's noise metrics for one on-call rotation — if the actionable-alert ratio didn't improve, re-run `--analyze-only` against the live config and iterate. Import the generated dashboard into Grafana and confirm every golden-signal panel renders with live data before closing the task.

## Core Competencies

### SLI/SLO/SLA Framework Design
- **Service Level Indicators (SLI):** Define measurable signals that indicate service health
- **Service Level Objectives (SLO):** Set reliability targets based on user experience
- **Service Level Agreements (SLA):** Establish customer-facing commitments with consequences
- **Error Budget Management:** Calculate and track error budget consumption
- **Burn Rate Alerting:** Multi-window burn rate alerts for proactive SLO protection

### Three Pillars of Observability

#### Metrics
- **Golden Signals:** Latency, traffic, errors, and saturation monitoring
- **RED Method:** Rate, Errors, and Duration for request-driven services
- **USE Method:** Utilization, Saturation, and Errors for resource monitoring
- **Business Metrics:** Revenue, user engagement, and feature adoption tracking
- **Infrastructure Metrics:** CPU, memory, disk, network, and custom resource metrics

#### Logs
- **Structured Logging:** JSON-based log formats with consistent fields
- **Log Aggregation:** Centralized log collection and indexing strategies
- **Log Levels:** Appropriate use of DEBUG, INFO, WARN, ERROR, FATAL levels
- **Correlation IDs:** Request tracing through distributed systems
- **Log Sampling:** Volume management for high-throughput systems

#### Traces
- **Distributed Tracing:** End-to-end request flow visualization
- **Span Design:** Meaningful span boundaries and metadata
- **Trace Sampling:** Intelligent sampling strategies for performance and cost
- **Service Maps:** Automatic dependency discovery through traces
- **Root Cause Analysis:** Trace-driven debugging workflows

### Dashboard Design Principles

#### Information Architecture
- **Hierarchy:** Overview → Service → Component → Instance drill-down paths
- **Golden Ratio:** 80% operational metrics, 20% exploratory metrics
- **Cognitive Load:** Maximum 7±2 panels per dashboard screen
- **User Journey:** Role-based dashboard personas (SRE, Developer, Executive)

#### Visualization Best Practices
- **Chart Selection:** Time series for trends, heatmaps for distributions, gauges for status
- **Color Theory:** Red for critical, amber for warning, green for healthy states
- **Reference Lines:** SLO targets, capacity thresholds, and historical baselines
- **Time Ranges:** Default to meaningful windows (4h for incidents, 7d for trends)

#### Panel Design
- **Metric Queries:** Efficient Prometheus/InfluxDB queries with proper aggregation
- **Alerting Integration:** Visual alert state indicators on relevant panels
- **Interactive Elements:** Template variables, drill-down links, and annotation overlays
- **Performance:** Sub-second render times through query optimization

### Alert Design and Optimization

#### Alert Classification
- **Severity Levels:** 
  - **Critical:** Service down, SLO burn rate high
  - **Warning:** Approaching thresholds, non-user-facing issues
  - **Info:** Deployment notifications, capacity planning alerts
- **Actionability:** Every alert must have a clear response action
- **Alert Routing:** Escalation policies based on severity and team ownership

#### Alert Fatigue Prevention
- **Signal vs Noise:** High precision (few false positives) over high recall
- **Hysteresis:** Different thresholds for firing and resolving alerts
- **Suppression:** Dependent alert suppression during known outages
- **Grouping:** Related alerts grouped into single notifications

#### Alert Rule Design
- **Threshold Selection:** Statistical methods for threshold determination
- **Window Functions:** Appropriate averaging windows and percentile calculations
- **Alert Lifecycle:** Clear firing conditions and automatic resolution criteria
- **Testing:** Alert rule validation against historical data

### Runbook Generation and Incident Response

#### Runbook Structure
- **Alert Context:** What the alert means and why it fired
- **Impact Assessment:** User-facing vs internal impact evaluation
- **Investigation Steps:** Ordered troubleshooting procedures with time estimates
- **Resolution Actions:** Common fixes and escalation procedures
- **Post-Incident:** Follow-up tasks and prevention measures

#### Incident Detection Patterns
- **Anomaly Detection:** Statistical methods for detecting unusual patterns
- **Composite Alerts:** Multi-signal alerts for complex failure modes
- **Predictive Alerts:** Capacity and trend-based forward-looking alerts
- **Canary Monitoring:** Early detection through progressive deployment monitoring

### Golden Signals Framework

#### Latency Monitoring
- **Request Latency:** P50, P95, P99 response time tracking
- **Queue Latency:** Time spent waiting in processing queues
- **Network Latency:** Inter-service communication delays
- **Database Latency:** Query execution and connection pool metrics

#### Traffic Monitoring
- **Request Rate:** Requests per second with burst detection
- **Bandwidth Usage:** Network throughput and capacity utilization
- **User Sessions:** Active user tracking and session duration
- **Feature Usage:** API endpoint and feature adoption metrics

#### Error Monitoring
- **Error Rate:** 4xx and 5xx HTTP response code tracking
- **Error Budget:** SLO-based error rate targets and consumption
- **Error Distribution:** Error type classification and trending
- **Silent Failures:** Detection of processing failures without HTTP errors

#### Saturation Monitoring
- **Resource Utilization:** CPU, memory, disk, and network usage
- **Queue Depth:** Processing queue length and wait times
- **Connection Pools:** Database and service connection saturation
- **Rate Limiting:** API throttling and quota exhaustion tracking

### Distributed Tracing Strategies

#### Trace Architecture
- **Sampling Strategy:** Head-based, tail-based, and adaptive sampling
- **Trace Propagation:** Context propagation across service boundaries
- **Span Correlation:** Parent-child relationship modeling
- **Trace Storage:** Retention policies and storage optimization

#### Service Instrumentation
- **Auto-Instrumentation:** Framework-based automatic trace generation
- **Manual Instrumentation:** Custom span creation for business logic
- **Baggage Handling:** Cross-cutting concern propagation
- **Performance Impact:** Instrumentation overhead measurement and optimization

### Log Aggregation Patterns

#### Collection Architecture
- **Agent Deployment:** Log shipping agent strategies (push vs pull)
- **Log Routing:** Topic-based routing and filtering
- **Parsing Strategies:** Structured vs unstructured log handling
- **Schema Evolution:** Log format versioning and migration

#### Storage and Indexing
- **Index Design:** Optimized field indexing for common query patterns
- **Retention Policies:** Time and volume-based log retention
- **Compression:** Log data compression and archival strategies
- **Search Performance:** Query optimization and result caching

### Cost Optimization for Observability

#### Data Management
- **Metric Retention:** Tiered retention based on metric importance
- **Log Sampling:** Intelligent sampling to reduce ingestion costs
- **Trace Sampling:** Cost-effective trace collection strategies
- **Data Archival:** Cold storage for historical observability data

#### Resource Optimization
- **Query Efficiency:** Optimized metric and log queries
- **Storage Costs:** Appropriate storage tiers for different data types
- **Ingestion Rate Limiting:** Controlled data ingestion to manage costs
- **Cardinality Management:** High-cardinality metric detection and mitigation

## Scripts Overview

This skill includes three powerful Python scripts for comprehensive observability design:

### 1. SLO Designer (`slo_designer.py`)
Generates complete SLI/SLO frameworks based on service characteristics:
- **Input:** Service description JSON (type, criticality, dependencies)
- **Output:** SLI definitions, SLO targets, error budgets, burn rate alerts, SLA recommendations
- **Features:** Multi-window burn rate calculations, error budget policies, alert rule generation

### 2. Alert Optimizer (`alert_optimizer.py`)
Analyzes and optimizes existing alert configurations:
- **Input:** Alert configuration JSON with rules, thresholds, and routing
- **Output:** Optimization report and improved alert configuration
- **Features:** Noise detection, coverage gaps, duplicate identification, threshold optimization

### 3. Dashboard Generator (`dashboard_generator.py`)
Creates comprehensive dashboard specifications:
- **Input:** Service/system description JSON
- **Output:** Grafana-compatible dashboard JSON and documentation
- **Features:** Golden signals coverage, RED/USE methods, drill-down paths, role-based views

## Integration Patterns

### Monitoring Stack Integration
- **Prometheus:** Metric collection and alerting rule generation
- **Grafana:** Dashboard creation and visualization configuration
- **Elasticsearch/Kibana:** Log analysis and dashboard integration
- **Jaeger/Zipkin:** Distributed tracing configuration and analysis

### CI/CD Integration
- **Pipeline Monitoring:** Build, test, and deployment observability
- **Deployment Correlation:** Release impact tracking and rollback triggers
- **Feature Flag Monitoring:** A/B test and feature rollout observability
- **Performance Regression:** Automated performance monitoring in pipelines

### Incident Management Integration
- **PagerDuty/VictorOps:** Alert routing and escalation policies
- **Slack/Teams:** Notification and collaboration integration
- **JIRA/ServiceNow:** Incident tracking and resolution workflows
- **Post-Mortem:** Automated incident analysis and improvement tracking

## Advanced Patterns

### Multi-Cloud Observability
- **Cross-Cloud Metrics:** Unified metrics across AWS, GCP, Azure
- **Network Observability:** Inter-cloud connectivity monitoring
- **Cost Attribution:** Cloud resource cost tracking and optimization
- **Compliance Monitoring:** Security and compliance posture tracking

### Microservices Observability
- **Service Mesh Integration:** Istio/Linkerd observability configuration
- **API Gateway Monitoring:** Request routing and rate limiting observability
- **Container Orchestration:** Kubernetes cluster and workload monitoring
- **Service Discovery:** Dynamic service monitoring and health checks

### Machine Learning Observability
- **Model Performance:** Accuracy, drift, and bias monitoring
- **Feature Store Monitoring:** Feature quality and freshness tracking
- **Pipeline Observability:** ML pipeline execution and performance monitoring
- **A/B Test Analysis:** Statistical significance and business impact measurement

## Best Practices

### Organizational Alignment
- **SLO Setting:** Collaborative target setting between product and engineering
- **Alert Ownership:** Clear escalation paths and team responsibilities
- **Dashboard Governance:** Centralized dashboard management and standards
- **Training Programs:** Team education on observability tools and practices

### Technical Excellence
- **Infrastructure as Code:** Observability configuration version control
- **Testing Strategy:** Alert rule testing and dashboard validation
- **Performance Monitoring:** Observability system performance tracking
- **Security Considerations:** Access control and data privacy in observability

### Continuous Improvement
- **Metrics Review:** Regular SLI/SLO effectiveness assessment
- **Alert Tuning:** Ongoing alert threshold and routing optimization
- **Dashboard Evolution:** User feedback-driven dashboard improvements
- **Tool Evaluation:** Regular assessment of observability tool effectiveness
