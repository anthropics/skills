# Production Deployment Guide

**Piano Training Platform - v1.0**

This guide provides comprehensive instructions for deploying, monitoring, and maintaining the Piano Training Platform in production environments.

---

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Initial Setup](#initial-setup)
3. [Deployment Workflows](#deployment-workflows)
4. [Environment Configuration](#environment-configuration)
5. [Health Checks](#health-checks)
6. [Monitoring](#monitoring)
7. [Troubleshooting](#troubleshooting)
8. [Rollback Procedures](#rollback-procedures)

---

## Prerequisites

### Infrastructure Requirements

**Staging Environment:**
- 2 CPU cores, 4GB RAM minimum
- 50GB SSD storage
- Ubuntu 20.04+ or equivalent
- Docker 24.0+, Docker Compose 2.20+

**Production Environment:**
- 4+ CPU cores, 8GB+ RAM (16GB recommended)
- 100GB+ SSD storage (NVMe recommended)
- Ubuntu 20.04+ or equivalent
- Docker 24.0+, Docker Compose 2.20+
- SSL certificates (Let's Encrypt or commercial)

### Access Requirements

- GitHub repository access with permissions to:
  - Push to branches starting with `claude/`
  - Create releases with tags `v*.*.*`
  - Write to GitHub Container Registry (ghcr.io)
- Server SSH access with sudo privileges
- DNS management for:
  - `piano-tutor.com` → Production frontend
  - `api.piano-tutor.com` → Production backend
  - `staging.piano-tutor.com` → Staging frontend
  - `api-staging.piano-tutor.com` → Staging backend

### Secrets Configuration

Configure the following secrets in GitHub:
- `AWS_ACCESS_KEY_ID` - AWS credentials (if using AWS)
- `AWS_SECRET_ACCESS_KEY` - AWS secret key
- `STAGING_HOST` - Staging server hostname/IP
- `STAGING_USER` - SSH user for staging
- `STAGING_SSH_KEY` - Private SSH key for staging
- `PRODUCTION_HOST` - Production server hostname/IP
- `PRODUCTION_USER` - SSH user for production
- `PRODUCTION_SSH_KEY` - Private SSH key for production

---

## Initial Setup

### 1. Server Preparation

```bash
# Update system packages
sudo apt update && sudo apt upgrade -y

# Install Docker
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh
sudo usermod -aG docker $USER

# Install Docker Compose
sudo curl -L "https://github.com/docker/compose/releases/latest/download/docker-compose-$(uname -s)-$(uname -m)" -o /usr/local/bin/docker-compose
sudo chmod +x /usr/local/bin/docker-compose

# Create application directory
sudo mkdir -p /opt/piano-tutor
sudo chown $USER:$USER /opt/piano-tutor
cd /opt/piano-tutor

# Create data directories
sudo mkdir -p /var/lib/piano-tutor/{postgres,redis,uploads}
sudo mkdir -p /var/log/piano-tutor
sudo mkdir -p /opt/backups
```

### 2. Environment Configuration

```bash
# Copy environment template
cp .env.production.example .env.production

# Edit with your values
nano .env.production

# CRITICAL: Set strong passwords and secrets
# - POSTGRES_PASSWORD (32+ characters)
# - JWT_SECRET (64+ characters)
# - All API keys and tokens
```

### 3. SSL Certificate Setup

**Using Let's Encrypt (Recommended):**

```bash
# Install certbot
sudo apt install certbot python3-certbot-nginx -y

# Obtain certificate
sudo certbot certonly --standalone -d piano-tutor.com -d www.piano-tutor.com

# Copy to application
sudo mkdir -p /opt/piano-tutor/ssl
sudo cp /etc/letsencrypt/live/piano-tutor.com/fullchain.pem /opt/piano-tutor/ssl/cert.pem
sudo cp /etc/letsencrypt/live/piano-tutor.com/privkey.pem /opt/piano-tutor/ssl/key.pem
sudo chown -R $USER:$USER /opt/piano-tutor/ssl
```

### 4. Initial Deployment

```bash
# Clone repository
git clone https://github.com/criptolandiatv/skills.git /opt/piano-tutor
cd /opt/piano-tutor

# Log in to GitHub Container Registry
echo $GITHUB_TOKEN | docker login ghcr.io -u USERNAME --password-stdin

# Pull images
export VERSION=v1.0.0
docker pull ghcr.io/criptolandiatv/skills/frontend:${VERSION}
docker pull ghcr.io/criptolandiatv/skills/backend:${VERSION}

# Start services
docker-compose -f docker-compose.production.yml up -d

# Verify health
curl http://localhost:3000/health
curl http://localhost:8000/health
```

---

## Deployment Workflows

### Automatic Deployments

The platform uses GitHub Actions for automated deployments:

**Staging Deployment:**
```bash
# Triggered automatically on push to main branch
git push origin main

# Or manually trigger
gh workflow run deploy-production.yml -f environment=staging
```

**Production Deployment:**
```bash
# Create and push a release tag
git tag -a v1.0.1 -m "Release v1.0.1"
git push origin v1.0.1

# GitHub Actions will:
# 1. Validate version format
# 2. Build Docker images
# 3. Run security scans
# 4. Deploy using Blue-Green strategy
# 5. Run smoke tests
# 6. Monitor for 5 minutes
# 7. Create GitHub release
```

### Manual Deployments

**Deploy to Staging:**
```bash
# SSH into staging server
ssh user@staging.piano-tutor.com

# Navigate to app directory
cd /opt/piano-tutor

# Pull latest code
git pull origin main

# Update environment variables if needed
nano .env.staging

# Pull latest images
export VERSION=staging-$(git rev-parse --short HEAD)
docker-compose -f docker-compose.staging.yml pull

# Restart services
docker-compose -f docker-compose.staging.yml down
docker-compose -f docker-compose.staging.yml up -d

# Verify health
curl http://localhost:3000/health
curl http://localhost:8000/health
```

**Deploy to Production (Blue-Green):**
```bash
# SSH into production server
ssh user@piano-tutor.com

# Navigate to app directory
cd /opt/piano-tutor

# Set version
export VERSION=v1.0.1
export DEPLOYMENT_COLOR=green  # or blue
export FRONTEND_PORT=3001      # 3001 for green, 3000 for blue
export BACKEND_PORT=8001       # 8001 for green, 8000 for blue

# Pull new images
docker-compose -f docker-compose.production.yml pull

# Start new environment (green)
docker-compose -f docker-compose.production.yml -p piano-tutor-green up -d

# Wait for health checks (30 seconds)
sleep 30

# Verify health on new environment
curl http://localhost:3001/health
curl http://localhost:8001/health

# Update load balancer to point to new environment
# (nginx/haproxy/cloud load balancer configuration)

# Stop old environment (blue) after verification
docker-compose -f docker-compose.production.yml -p piano-tutor-blue down
```

---

## Environment Configuration

### Required Environment Variables

See `.env.production.example` for complete list. Critical variables:

```bash
# Application
ENVIRONMENT=production
VERSION=v1.0.0

# Security
JWT_SECRET=<64-char-random-string>
POSTGRES_PASSWORD=<strong-password>

# URLs
API_URL=https://api.piano-tutor.com
WS_URL=wss://api.piano-tutor.com

# Monitoring
SENTRY_DSN=<your-sentry-dsn>
ANALYTICS_ID=<your-analytics-id>
```

### Configuration Validation

```bash
# Validate environment file
docker-compose -f docker-compose.production.yml config

# Should show no errors and display merged configuration
```

---

## Health Checks

### Health Check Endpoints

**Frontend:**
```bash
# Simple health check
curl http://localhost:3000/health
# Expected: Status 200, "OK"

# Detailed with timestamp
curl http://localhost:3000/health.html
```

**Backend:**
```bash
# Simple health check (load balancer)
curl http://localhost:8000/health
# Expected: {"status":"healthy","timestamp":"...","service":"piano-tutor-api","version":"1.0.0"}

# Readiness check (all dependencies)
curl http://localhost:8000/health/ready
# Expected: {"status":"ready","checks":{"database":true,"cache":true,...}}

# Liveness check (process alive)
curl http://localhost:8000/health/live
# Expected: {"status":"alive","timestamp":"..."}

# Detailed metrics
curl http://localhost:8000/health/detailed
# Expected: Full system metrics including CPU, memory, database pool

# Startup check (initialization complete)
curl http://localhost:8000/health/startup
# Expected: {"status":"started","ready":true,...}

# Prometheus metrics
curl http://localhost:8000/metrics
# Expected: Prometheus text format metrics
```

### Docker Health Checks

```bash
# Check container health status
docker ps --filter "label=com.piano-tutor.environment=production"

# View health check logs
docker inspect piano-tutor-frontend-blue | grep Health -A 20
docker inspect piano-tutor-backend-blue | grep Health -A 20
```

---

## Monitoring

### Application Logs

```bash
# View live logs
docker-compose -f docker-compose.production.yml logs -f

# View specific service logs
docker-compose -f docker-compose.production.yml logs -f backend
docker-compose -f docker-compose.production.yml logs -f frontend

# View last 100 lines
docker-compose -f docker-compose.production.yml logs --tail=100

# Search logs
docker-compose -f docker-compose.production.yml logs | grep ERROR
```

### System Metrics

```bash
# View resource usage
docker stats

# View specific container stats
docker stats piano-tutor-backend-blue piano-tutor-frontend-blue

# Disk usage
docker system df

# Network connections
docker network inspect piano-tutor-network
```

### Database Monitoring

```bash
# Connect to PostgreSQL
docker exec -it piano-tutor-db-production psql -U piano_tutor

# Check database size
SELECT pg_size_pretty(pg_database_size('piano_tutor'));

# Active connections
SELECT count(*) FROM pg_stat_activity;

# Slow queries
SELECT query, calls, total_time, mean_time
FROM pg_stat_statements
ORDER BY mean_time DESC
LIMIT 10;
```

### Cache Monitoring

```bash
# Connect to Redis
docker exec -it piano-tutor-redis-production redis-cli

# Get info
INFO memory
INFO stats

# Check key count
DBSIZE

# Monitor commands in real-time
MONITOR
```

---

## Troubleshooting

### Common Issues

**1. Container Won't Start**

```bash
# Check logs
docker logs piano-tutor-backend-blue --tail=100

# Common causes:
# - Missing environment variables
# - Database connection failure
# - Port already in use

# Verify environment
docker-compose -f docker-compose.production.yml config

# Check port availability
netstat -tlnp | grep :8000
```

**2. Database Connection Errors**

```bash
# Test database connectivity
docker exec piano-tutor-db-production pg_isready -U piano_tutor

# Check database logs
docker logs piano-tutor-db-production --tail=100

# Verify connection string
echo $DATABASE_URL

# Test connection from backend container
docker exec piano-tutor-backend-blue psql $DATABASE_URL -c "SELECT 1"
```

**3. High Memory Usage**

```bash
# Check memory by container
docker stats --no-stream

# Clear Redis cache
docker exec piano-tutor-redis-production redis-cli FLUSHDB

# Restart services
docker-compose -f docker-compose.production.yml restart
```

**4. Slow Performance**

```bash
# Check CPU usage
top -H

# Check disk I/O
iotop

# Check database query performance
docker exec -it piano-tutor-db-production psql -U piano_tutor -c "SELECT * FROM pg_stat_statements ORDER BY total_time DESC LIMIT 10;"

# Clear application cache
docker exec piano-tutor-backend-blue python -c "from app.core.cache import clear_all; clear_all()"
```

### Debug Mode

```bash
# Enable debug logging
export LOG_LEVEL=debug

# Restart services
docker-compose -f docker-compose.production.yml restart backend

# Watch logs
docker-compose -f docker-compose.production.yml logs -f backend | grep DEBUG
```

---

## Rollback Procedures

### Automatic Rollback

GitHub Actions will automatically rollback on deployment failure. Manual rollback:

### Quick Rollback (Blue-Green)

```bash
# Switch back to previous (blue) environment
cd /opt/piano-tutor

# Start previous environment
docker-compose -f docker-compose.production.yml -p piano-tutor-blue up -d

# Update load balancer to point to blue
sudo nginx -s reload  # or your load balancer command

# Stop failed environment (green)
docker-compose -f docker-compose.production.yml -p piano-tutor-green down

# Verify
curl https://piano-tutor.com/health
```

### Full Version Rollback

```bash
# Find previous version
docker images | grep piano-tutor

# Set previous version
export VERSION=v1.0.0  # previous stable version

# Pull previous images
docker pull ghcr.io/criptolandiatv/skills/frontend:${VERSION}
docker pull ghcr.io/criptolandiatv/skills/backend:${VERSION}

# Stop current services
docker-compose -f docker-compose.production.yml down

# Start with previous version
docker-compose -f docker-compose.production.yml up -d

# Verify
curl http://localhost:8000/health
```

### Database Rollback

```bash
# List backups
ls -lh /opt/backups/

# Restore from backup
BACKUP_DATE=20251025_020000
docker exec -i piano-tutor-db-production psql -U piano_tutor < /opt/backups/${BACKUP_DATE}/dump.sql

# Verify data
docker exec -it piano-tutor-db-production psql -U piano_tutor -c "SELECT count(*) FROM users;"
```

---

## Backup & Recovery

### Automated Backups

```bash
# Database backup script (add to crontab)
#!/bin/bash
BACKUP_DIR="/opt/backups/$(date +%Y%m%d_%H%M%S)"
mkdir -p $BACKUP_DIR

# Backup database
docker exec piano-tutor-db-production pg_dump -U piano_tutor piano_tutor > $BACKUP_DIR/dump.sql

# Backup uploads
cp -r /var/lib/piano-tutor/uploads $BACKUP_DIR/

# Compress
tar -czf $BACKUP_DIR.tar.gz $BACKUP_DIR
rm -rf $BACKUP_DIR

# Upload to S3 (optional)
aws s3 cp $BACKUP_DIR.tar.gz s3://piano-tutor-backups/

# Cleanup old backups (keep 30 days)
find /opt/backups -name "*.tar.gz" -mtime +30 -delete

echo "Backup completed: $BACKUP_DIR.tar.gz"
```

**Add to crontab:**
```bash
# Daily backup at 2 AM
0 2 * * * /opt/piano-tutor/scripts/backup.sh >> /var/log/piano-tutor/backup.log 2>&1
```

### Manual Backup

```bash
# Create backup directory
BACKUP_DIR="/opt/backups/manual_$(date +%Y%m%d_%H%M%S)"
mkdir -p $BACKUP_DIR

# Backup database
docker exec piano-tutor-db-production pg_dump -U piano_tutor piano_tutor | gzip > $BACKUP_DIR/dump.sql.gz

# Backup Redis
docker exec piano-tutor-redis-production redis-cli SAVE
docker cp piano-tutor-redis-production:/data/dump.rdb $BACKUP_DIR/

# Backup configuration
cp docker-compose.production.yml $BACKUP_DIR/
cp .env.production $BACKUP_DIR/

# Backup uploads
tar -czf $BACKUP_DIR/uploads.tar.gz /var/lib/piano-tutor/uploads

echo "Manual backup created: $BACKUP_DIR"
```

---

## Scaling

### Horizontal Scaling

**Add Backend Workers:**
```bash
# Scale backend replicas
docker-compose -f docker-compose.production.yml up -d --scale backend=3

# Verify
docker ps | grep piano-tutor-backend
```

**Add Celery Workers:**
```bash
# Scale Celery workers
docker-compose -f docker-compose.production.yml up -d --scale celery-worker=4

# Verify
docker ps | grep piano-tutor-celery
```

### Vertical Scaling

Edit `docker-compose.production.yml`:
```yaml
services:
  backend:
    deploy:
      resources:
        limits:
          cpus: '8.0'      # Increase from 4.0
          memory: 8G       # Increase from 4G
```

---

## Security Checklist

- [ ] All secrets rotated from defaults
- [ ] SSL/TLS certificates installed and auto-renewing
- [ ] Firewall configured (only ports 80, 443, 22 open)
- [ ] SSH key-based authentication only
- [ ] Database not exposed to public internet
- [ ] Regular security updates applied
- [ ] Backups encrypted and tested
- [ ] Monitoring alerts configured
- [ ] Rate limiting enabled
- [ ] CORS configured for production domains only

---

## Support & Contacts

- **Documentation**: https://docs.piano-tutor.com
- **Issues**: https://github.com/criptolandiatv/skills/issues
- **Emergency**: DevOps on-call rotation

---

**Last Updated**: 2025-10-25
**Version**: 1.0.0
