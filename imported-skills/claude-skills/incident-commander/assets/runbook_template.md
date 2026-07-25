# Runbook: [Service/Component Name]

**Owner:** [Team Name]
**Last Updated:** [YYYY-MM-DD]
**Reviewed By:** [Name]
**Review Cadence:** Quarterly

---

## Service Overview

| Property | Value |
|----------|-------|
| **Service** | [service-name] |
| **Repository** | [repo URL] |
| **Dashboard** | [monitoring dashboard URL] |
| **On-Call Rotation** | [PagerDuty/OpsGenie schedule URL] |
| **SLA Tier** | [Tier 1/2/3] |
| **Availability Target** | [99.9% / 99.95% / 99.99%] |
| **Dependencies** | [list upstream/downstream services] |
| **Owner Team** | [team name] |
| **Escalation Contact** | [name/email] |

### Architecture Summary

[2-3 sentence description of the service architecture. Include key components, data stores, and external dependencies.]

---

## Alert Response Decision Tree

### High Error Rate (>5%)

```
Error Rate Alert Fired
├── Check: Is this a deployment-related issue?
│   ├── YES → Go to "Recent Deployment Rollback" section
│   └── NO → Continue
├── Check: Is a downstream dependency failing?
│   ├── YES → Go to "Dependency Failure" section
│   └── NO → Continue
├── Check: Is there unusual traffic volume?
│   ├── YES → Go to "Traffic Spike" section
│   └── NO → Continue
└── Escalate: Engage on-call secondary + service owner
```

### High Latency (p99 > [threshold]ms)

```
Latency Alert Fired
├── Check: Database query latency elevated?
│   ├── YES → Go to "Database Performance" section
│   └── NO → Continue
├── Check: Connection pool utilization >80%?
│   ├── YES → Go to "Connection Pool Exhaustion" section
│   └── NO → Continue
├── Check: Memory/CPU pressure on service instances?
│   ├── YES → Go to "Resource Exhaustion" section
│   └── NO → Continue
└── Escalate: Engage on-call secondary + service owner
```

### Service Unavailable (Health Check Failing)

```
Health Check Alert Fired
├── Check: Are all instances down?
│   ├── YES → Go to "Complete Outage" section
│   └── NO → Continue
├── Check: Is only one AZ affected?
│   ├── YES → Go to "AZ Failure" section
│   └── NO → Continue
├── Check: Can instances be restarted?
│   ├── YES → Go to "Instance Restart" section
│   └── NO → Continue
└── Escalate: Declare incident, engage IC
```

---

## Common Scenarios

### Recent Deployment Rollback

**Symptoms:** Error rate spike or latency increase within 60 minutes of a deployment.

**Diagnosis:**
1. Check deployment history: `kubectl rollout history deployment/[service-name]`
2. Compare error rate timing with deployment timestamp
3. Review deployment diff for risky changes

**Mitigation:**
1. Initiate rollback: `kubectl rollout undo deployment/[service-name]`
2. Verify rollback: `kubectl rollout status deployment/[service-name]`
3. Confirm error rate returns to baseline (allow 5 minutes)
4. If rollback fails: escalate immediately

**Communication:** If customer-impacting, update status page within 5 minutes of confirming impact.

---

### Database Performance

**Symptoms:** Elevated query latency, connection pool saturation, timeout errors.

**Diagnosis:**
1. Check active queries: `SELECT * FROM pg_stat_activity WHERE state = 'active';`
2. Check for long-running queries: `SELECT pid, now() - pg_stat_activity.query_start AS duration, query FROM pg_stat_activity WHERE state != 'idle' ORDER BY duration DESC;`
3. Check connection count: `SELECT count(*) FROM pg_stat_activity;`
4. Check table bloat and vacuum status

**Mitigation:**
1. Kill long-running queries if identified: `SELECT pg_terminate_backend([pid]);`
2. If connection pool exhausted: increase pool size via config (requires restart)
3. If read replica available: redirect read traffic
4. If write-heavy: identify and defer non-critical writes

**Escalation Trigger:** If query latency >10s for >5 minutes, escalate to DBA on-call.

---

### Connection Pool Exhaustion

**Symptoms:** Connection timeout errors, pool utilization >90%, requests queuing.

**Diagnosis:**
1. Check pool metrics: current size, active connections, waiting requests
2. Check for connection leaks: connections held >30s without activity
3. Review recent config changes or deployments

**Mitigation:**
1. Increase pool size (if infrastructure allows): update config, rolling restart
2. Kill idle connections exceeding timeout
3. If caused by leak: identify and restart affected instances
4. Enable connection pool auto-scaling if available

**Prevention:** Pool utilization alerting at 70% (warning) and 85% (critical).

---

### Dependency Failure

**Symptoms:** Errors correlated with downstream service failures, circuit breakers tripping.

**Diagnosis:**
1. Check dependency status dashboards
2. Verify circuit breaker state: open/half-open/closed
3. Check for correlation with dependency deployments or incidents
4. Test dependency health endpoints directly

**Mitigation:**
1. If circuit breaker not tripping: verify timeout/threshold configuration
2. Enable graceful degradation (serve cached/default responses)
3. If critical path: engage dependency team via incident process
4. If non-critical path: disable feature flag for affected functionality

**Communication:** Coordinate with dependency team IC if both services have active incidents.

---

### Traffic Spike

**Symptoms:** Sudden traffic increase beyond normal patterns, resource saturation.

**Diagnosis:**
1. Check traffic source: organic growth vs. bot traffic vs. DDoS
2. Review rate limiting effectiveness
3. Check auto-scaling status and capacity

**Mitigation:**
1. If bot/DDoS: enable rate limiting, engage security team
2. If organic: trigger manual scale-up, increase auto-scaling limits
3. Enable request queuing or load shedding if at capacity
4. Consider feature flag toggles to reduce per-request cost

---

### Complete Outage

**Symptoms:** All instances unreachable, health checks failing across AZs.

**Diagnosis:**
1. Check infrastructure status (AWS/GCP status page)
2. Verify network connectivity and DNS resolution
3. Check for infrastructure-level incidents (region outage)
4. Review recent infrastructure changes (Terraform, network config)

**Mitigation:**
1. If infra provider issue: activate disaster recovery plan
2. If DNS issue: update DNS records, reduce TTL
3. If deployment corruption: redeploy last known good version
4. If data corruption: engage data recovery procedures

**Escalation:** Immediately declare SEV1 incident. Engage infrastructure team and management.

---

### Instance Restart

**Symptoms:** Individual instances unhealthy, OOM kills, process crashes.

**Diagnosis:**
1. Check instance logs for crash reason
2. Review memory/CPU usage patterns before crash
3. Check for memory leaks or resource exhaustion
4. Verify configuration consistency across instances

**Mitigation:**
1. Restart unhealthy instances: `kubectl delete pod [pod-name]`
2. If recurring: cordon node and migrate workloads
3. If memory leak: schedule immediate patch with increased memory limit
4. Monitor for recurrence after restart

---

### AZ Failure

**Symptoms:** All instances in one availability zone failing, others healthy.

**Diagnosis:**
1. Confirm AZ-specific failure vs. instance-specific issues
2. Check cloud provider AZ status
3. Verify load balancer is routing around failed AZ

**Mitigation:**
1. Ensure load balancer marks AZ instances as unhealthy
2. Scale up remaining AZs to handle redirected traffic
3. If auto-scaling: verify it's responding to increased load
4. Monitor remaining AZs for cascade effects

---

## Key Metrics & Dashboards

| Metric | Normal Range | Warning | Critical | Dashboard |
|--------|-------------|---------|----------|-----------|
| Error Rate | <0.1% | >1% | >5% | [link] |
| p99 Latency | <200ms | >500ms | >2000ms | [link] |
| CPU Usage | <60% | >75% | >90% | [link] |
| Memory Usage | <70% | >80% | >90% | [link] |
| DB Pool Usage | <50% | >70% | >85% | [link] |
| Request Rate | [baseline]±20% | ±50% | ±100% | [link] |

---

## Escalation Contacts

| Level | Contact | When |
|-------|---------|------|
| L1: On-Call Primary | [name/rotation] | First responder |
| L2: On-Call Secondary | [name/rotation] | Primary unavailable or needs help |
| L3: Service Owner | [name] | Complex issues, architectural decisions |
| L4: Engineering Manager | [name] | SEV1/SEV2, customer impact, resource needs |
| L5: VP Engineering | [name] | SEV1 >30 min, major customer/revenue impact |

---

## Maintenance Procedures

### Planned Maintenance Checklist

- [ ] Maintenance window scheduled and communicated (72 hours advance for Tier 1)
- [ ] Status page updated with planned maintenance notice
- [ ] Rollback plan documented and tested
- [ ] On-call notified of maintenance window
- [ ] Customer notification sent (if SLA-impacting)
- [ ] Post-maintenance verification plan ready

### Health Verification After Changes

1. Check all health endpoints return 200
2. Verify error rate returns to baseline within 5 minutes
3. Confirm latency within normal range
4. Run synthetic transaction test
5. Monitor for 15 minutes before declaring success

---

## Revision History

| Date | Author | Change |
|------|--------|--------|
| [YYYY-MM-DD] | [Name] | Initial version |
| [YYYY-MM-DD] | [Name] | [Description of update] |

---

*This runbook should be reviewed quarterly and updated after every incident that reveals missing procedures. The on-call engineer should be able to follow this document without prior context about the service. If any section requires tribal knowledge to execute, it needs to be expanded.*
