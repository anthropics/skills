# Production Runbook

**Piano Training Platform Operations Manual**

Quick reference guide for common operational tasks and incident response procedures.

---

## Quick Links

- [Emergency Procedures](#emergency-procedures)
- [Daily Operations](#daily-operations)
- [Deployment Procedures](#deployment-procedures)
- [Incident Response](#incident-response)
- [Maintenance Tasks](#maintenance-tasks)

---

## Emergency Procedures

### 🚨 CRITICAL: Site Down

**Symptoms:** Health checks failing, users cannot access site

**Immediate Actions:**

```bash
# 1. Check service status
ssh user@piano-tutor.com
docker ps --filter "label=com.piano-tutor.environment=production"

# 2. Check logs for errors
docker-compose -f docker-compose.production.yml logs --tail=100 | grep -i error

# 3. Quick restart
docker-compose -f docker-compose.production.yml restart

# 4. If restart doesn't work, rollback
export DEPLOYMENT_COLOR=blue  # switch to previous version
docker-compose -f docker-compose.production.yml -p piano-tutor-blue up -d
sudo nginx -s reload

# 5. Verify
curl https://piano-tutor.com/health
```

**Post-Incident:**
1. Document what happened in incident log
2. Create GitHub issue with root cause analysis
3. Update monitoring alerts if needed

---

### 🔴 Database Connection Failure

**Symptoms:** Backend returns 500 errors, "database connection" in logs

**Actions:**

```bash
# 1. Check database health
docker exec piano-tutor-db-production pg_isready -U piano_tutor

# 2. Check database logs
docker logs piano-tutor-db-production --tail=100

# 3. Check connection pool
curl http://localhost:8000/health/detailed | jq '.database'

# 4. Restart database if needed
docker-compose -f docker-compose.production.yml restart postgres

# 5. Wait for backend to reconnect (30 seconds)
sleep 30

# 6. Verify
curl http://localhost:8000/health/ready
```

**If database won't start:**
```bash
# Check disk space
df -h

# Check database data directory
ls -lh /var/lib/piano-tutor/postgres/

# Check for corrupted data files
docker exec piano-tutor-db-production pg_checksums -D /var/lib/postgresql/data

# If corrupted, restore from backup
./scripts/restore_database.sh /opt/backups/latest/dump.sql.gz
```

---

### 🟡 High CPU/Memory Usage

**Symptoms:** Slow response times, high resource usage alerts

**Actions:**

```bash
# 1. Identify resource hog
docker stats --no-stream | sort -k 3 -h

# 2. Check for runaway processes
docker exec piano-tutor-backend-blue ps aux | sort -k 3 -h

# 3. Check for stuck Celery tasks
docker exec piano-tutor-celery-blue celery -A app.celery.tasks inspect active

# 4. Scale down if needed
docker-compose -f docker-compose.production.yml restart celery-worker

# 5. Clear cache if memory issue
docker exec piano-tutor-redis-production redis-cli FLUSHDB

# 6. Restart services one at a time
docker-compose -f docker-compose.production.yml restart backend
docker-compose -f docker-compose.production.yml restart frontend
```

---

## Daily Operations

### Morning Health Check

Run daily at start of business day:

```bash
#!/bin/bash
# Daily health check script

echo "=== Piano Tutor Daily Health Check $(date) ==="

# 1. Service Status
echo -e "\n[Services]"
ssh user@piano-tutor.com "docker ps --filter 'label=com.piano-tutor.environment=production' --format 'table {{.Names}}\t{{.Status}}'"

# 2. Health Endpoints
echo -e "\n[Health Checks]"
curl -s https://piano-tutor.com/health | jq '.status'
curl -s https://api.piano-tutor.com/health/ready | jq '.status'

# 3. Resource Usage
echo -e "\n[Resources]"
ssh user@piano-tutor.com "docker stats --no-stream --format 'table {{.Name}}\t{{.CPUPerc}}\t{{.MemPerc}}'"

# 4. Disk Space
echo -e "\n[Disk Space]"
ssh user@piano-tutor.com "df -h /var/lib/piano-tutor"

# 5. Error Count (last 24h)
echo -e "\n[Errors - Last 24h]"
ssh user@piano-tutor.com "docker logs piano-tutor-backend-blue --since 24h 2>&1 | grep -i error | wc -l"

# 6. Active Users (from cache)
echo -e "\n[Active Users]"
ssh user@piano-tutor.com "docker exec piano-tutor-redis-production redis-cli DBSIZE"

echo -e "\n=== Health Check Complete ==="
```

**Expected Output:**
- All services: `Up` status
- Health checks: `healthy` / `ready`
- CPU: < 60%
- Memory: < 70%
- Disk: < 80%
- Errors: < 10 in 24h

**Alert if:**
- Any service is `Restarting` or `Exited`
- Health checks return `not_ready`
- CPU > 80% sustained
- Memory > 85%
- Disk > 90%
- Errors > 50 in 24h

---

### Monitor Real-time Metrics

```bash
# Watch logs in real-time
docker-compose -f docker-compose.production.yml logs -f --tail=50

# Monitor resource usage
watch -n 5 'docker stats --no-stream'

# Monitor active requests
watch -n 2 'curl -s http://localhost:8000/health/detailed | jq ".database, .cache"'

# Monitor error rate
watch -n 10 'docker logs piano-tutor-backend-blue --since 1m 2>&1 | grep -c ERROR'
```

---

## Deployment Procedures

### Standard Production Deployment

**Pre-Deployment Checklist:**
- [ ] Code reviewed and approved
- [ ] All tests passing (CI/CD green)
- [ ] Staging deployment successful
- [ ] Database migrations reviewed
- [ ] Backup completed
- [ ] Rollback plan ready
- [ ] Change window scheduled
- [ ] Team notified

**Deployment Steps:**

```bash
# 1. Create release tag
git tag -a v1.0.1 -m "Release v1.0.1 - Bug fixes and performance improvements"
git push origin v1.0.1

# GitHub Actions will automatically:
# - Build Docker images
# - Run security scans
# - Deploy to production (Blue-Green)
# - Run smoke tests
# - Monitor for 5 minutes

# 2. Monitor deployment
gh run watch

# 3. Verify deployment
curl https://piano-tutor.com/health
curl https://api.piano-tutor.com/health/ready

# 4. Check version
curl https://api.piano-tutor.com/health | jq '.version'

# 5. Monitor for 15 minutes
watch -n 30 'curl -s https://api.piano-tutor.com/health/detailed | jq ".status, .system.cpu_percent, .system.memory.percent"'

# 6. Check error logs
ssh user@piano-tutor.com "docker logs piano-tutor-backend-green --since 15m 2>&1 | grep -i error"
```

**Post-Deployment:**
- [ ] Verify version deployed
- [ ] Check error logs (should be minimal)
- [ ] Verify metrics dashboard
- [ ] Test critical user flows
- [ ] Update deployment log
- [ ] Notify team of completion

---

### Emergency Hotfix Deployment

**When:** Critical bug affecting users, must deploy ASAP

```bash
# 1. Create hotfix branch from current production tag
git checkout v1.0.0
git checkout -b hotfix/critical-bug-fix

# 2. Make minimal fix
# ... edit files ...

# 3. Test locally
npm run test
npm run build

# 4. Commit and tag
git commit -m "hotfix: Fix critical authentication bug"
git tag -a v1.0.1 -m "Hotfix: Critical authentication bug"
git push origin v1.0.1

# 5. Monitor automated deployment
gh run watch

# 6. Manual deployment if automation fails
ssh user@piano-tutor.com
cd /opt/piano-tutor
export VERSION=v1.0.1
export DEPLOYMENT_COLOR=green
docker-compose -f docker-compose.production.yml pull
docker-compose -f docker-compose.production.yml -p piano-tutor-green up -d

# 7. Verify immediately
curl https://piano-tutor.com/health
# Test the specific bug fix

# 8. Switch traffic
sudo nginx -s reload
docker-compose -f docker-compose.production.yml -p piano-tutor-blue down

# 9. Merge hotfix back to main
git checkout main
git merge hotfix/critical-bug-fix
git push origin main
```

---

## Incident Response

### Incident Severity Levels

**P0 - Critical:**
- Complete site outage
- Data loss or corruption
- Security breach
- Response time: Immediate

**P1 - High:**
- Major feature broken
- Performance degradation >50%
- Affects >50% of users
- Response time: <15 minutes

**P2 - Medium:**
- Minor feature broken
- Affects <50% of users
- Workaround available
- Response time: <1 hour

**P3 - Low:**
- Cosmetic issues
- Documentation errors
- Affects <10% of users
- Response time: Next business day

---

### P0 Incident Response Procedure

**1. Acknowledge & Assess (0-5 min)**
```bash
# Alert received - acknowledge immediately
# Post in #incidents channel: "P0 incident acknowledged, investigating"

# Quick assessment
curl https://piano-tutor.com/health
ssh user@piano-tutor.com
docker ps
docker-compose -f docker-compose.production.yml logs --tail=100
```

**2. Communicate (5-10 min)**
```
# Post status update:
"P0 Incident Update:
- Issue: [brief description]
- Impact: [user-facing impact]
- Current Status: Investigating
- ETA: [estimate if possible]
- Updates every 15 min"
```

**3. Mitigate (10-30 min)**
```bash
# Option A: Quick restart
docker-compose -f docker-compose.production.yml restart

# Option B: Rollback to previous version
export DEPLOYMENT_COLOR=blue
docker-compose -f docker-compose.production.yml -p piano-tutor-blue up -d
sudo nginx -s reload

# Option C: Enable maintenance mode
# (if need time to fix without user impact)
```

**4. Verify & Monitor (30-45 min)**
```bash
# Verify fix
curl https://piano-tutor.com/health
curl https://api.piano-tutor.com/health/ready

# Monitor for 15 minutes
watch -n 30 'curl -s https://api.piano-tutor.com/health/detailed | jq'

# Check error rate
docker logs piano-tutor-backend-blue --since 15m 2>&1 | grep -c ERROR
```

**5. Post-Incident (45-60 min)**
```
# Final status update:
"P0 Incident Resolved:
- Root Cause: [brief description]
- Fix Applied: [what was done]
- Verification: All health checks passing
- Post-Mortem: [link to document]
- Prevention: [steps to prevent recurrence]"

# Create post-mortem document
# Schedule blameless post-mortem meeting within 48h
```

---

## Maintenance Tasks

### Weekly Tasks

**1. Review Logs (Monday)**
```bash
# Check for recurring errors
ssh user@piano-tutor.com "docker logs piano-tutor-backend-blue --since 7d 2>&1" | grep -i error | sort | uniq -c | sort -rn | head -20

# Check slow queries
docker exec -it piano-tutor-db-production psql -U piano_tutor -c "
SELECT query, calls, total_time/calls as avg_time
FROM pg_stat_statements
WHERE calls > 100
ORDER BY avg_time DESC
LIMIT 10;"
```

**2. Database Maintenance (Wednesday)**
```bash
# Vacuum and analyze
docker exec piano-tutor-db-production psql -U piano_tutor -c "VACUUM ANALYZE;"

# Reindex if needed
docker exec piano-tutor-db-production psql -U piano_tutor -c "REINDEX DATABASE piano_tutor;"

# Check bloat
docker exec piano-tutor-db-production psql -U piano_tutor -c "
SELECT schemaname, tablename,
pg_size_pretty(pg_total_relation_size(schemaname||'.'||tablename)) AS size
FROM pg_tables
WHERE schemaname NOT IN ('pg_catalog', 'information_schema')
ORDER BY pg_total_relation_size(schemaname||'.'||tablename) DESC
LIMIT 10;"
```

**3. Cache Optimization (Friday)**
```bash
# Check cache hit rate
docker exec piano-tutor-redis-production redis-cli INFO stats | grep keyspace

# Clear expired keys
docker exec piano-tutor-redis-production redis-cli --scan --pattern "temp:*" | xargs docker exec piano-tutor-redis-production redis-cli DEL

# Check memory usage
docker exec piano-tutor-redis-production redis-cli INFO memory
```

---

### Monthly Tasks

**1. Security Updates (1st of month)**
```bash
# Update base images
docker pull python:3.11-slim
docker pull node:20-alpine
docker pull postgres:15-alpine
docker pull redis:7-alpine
docker pull nginx:1.25-alpine

# Rebuild application images
git pull origin main
docker-compose -f docker-compose.production.yml build --no-cache

# Deploy during maintenance window
```

**2. Certificate Renewal (15th of month)**
```bash
# Check certificate expiry
sudo certbot certificates

# Renew if needed (auto-renew should handle this)
sudo certbot renew

# Copy to application
sudo cp /etc/letsencrypt/live/piano-tutor.com/fullchain.pem /opt/piano-tutor/ssl/cert.pem
sudo cp /etc/letsencrypt/live/piano-tutor.com/privkey.pem /opt/piano-tutor/ssl/key.pem

# Reload nginx
docker-compose -f docker-compose.production.yml restart nginx
```

**3. Backup Verification (Last Sunday)**
```bash
# Test latest backup
LATEST_BACKUP=$(ls -t /opt/backups/*.tar.gz | head -1)
echo "Testing backup: $LATEST_BACKUP"

# Extract to temp location
mkdir -p /tmp/backup-test
tar -xzf $LATEST_BACKUP -C /tmp/backup-test

# Verify database backup
gunzip -c /tmp/backup-test/*/dump.sql.gz | head -100

# Cleanup
rm -rf /tmp/backup-test

echo "Backup verification complete"
```

---

## Performance Optimization

### Database Optimization

```bash
# Analyze query performance
docker exec -it piano-tutor-db-production psql -U piano_tutor -c "
SELECT query, calls, total_time, mean_time,
       100.0 * total_time / SUM(total_time) OVER() AS percentage
FROM pg_stat_statements
ORDER BY total_time DESC
LIMIT 20;"

# Add indexes for slow queries
# Review and add as needed based on above output

# Update statistics
docker exec piano-tutor-db-production psql -U piano_tutor -c "ANALYZE;"
```

### Cache Optimization

```bash
# Identify cache hit rate
docker exec piano-tutor-redis-production redis-cli INFO stats | grep keyspace_hits

# Adjust TTL for frequently accessed data
# Review application cache configuration

# Warm cache after deployment
curl -X POST https://api.piano-tutor.com/admin/cache/warm
```

---

## Monitoring Setup

### Prometheus + Grafana (Optional)

```bash
# Add to docker-compose.production.yml
services:
  prometheus:
    image: prom/prometheus
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"

  grafana:
    image: grafana/grafana
    volumes:
      - grafana-data:/var/lib/grafana
    ports:
      - "3001:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=<strong-password>
```

**Configure Prometheus to scrape:**
- `http://backend:8000/metrics`
- `http://frontend:80/metrics`
- Docker metrics
- Node exporter

---

## Contacts & Escalation

**On-Call Rotation:**
- Week 1: DevOps Team A
- Week 2: DevOps Team B
- Week 3: DevOps Team C

**Escalation Path:**
1. On-call engineer (respond within 15 min)
2. Lead DevOps (if no response in 30 min)
3. CTO (for P0 incidents lasting >1 hour)

**Communication Channels:**
- #incidents (Slack) - All incidents
- #deployments (Slack) - Deployment notifications
- ops@piano-tutor.com - Email escalations

---

**Last Updated**: 2025-10-25
**Version**: 1.0.0
**Maintained By**: DevOps Team
