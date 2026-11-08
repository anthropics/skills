#!/bin/bash
#
# Deployment script for Piano Tutor Platform
# Usage: ./scripts/deploy.sh [staging|production] [version]
#

set -e

ENVIRONMENT=${1:-staging}
VERSION=${2:-latest}

if [ "$ENVIRONMENT" != "staging" ] && [ "$ENVIRONMENT" != "production" ]; then
    echo "❌ Invalid environment. Use 'staging' or 'production'"
    exit 1
fi

echo "========================================="
echo "Piano Tutor Deployment"
echo "Environment: $ENVIRONMENT"
echo "Version: $VERSION"
echo "$(date)"
echo "========================================="

# Confirmation for production
if [ "$ENVIRONMENT" = "production" ]; then
    echo -e "\n⚠️  WARNING: Deploying to PRODUCTION"
    read -p "Are you sure? (yes/no): " -r
    if [[ ! $REPLY =~ ^[Yy][Ee][Ss]$ ]]; then
        echo "Deployment cancelled"
        exit 0
    fi
fi

# Pre-deployment checks
echo -e "\n[Pre-Deployment Checks]"

# Check if docker is running
if ! docker info > /dev/null 2>&1; then
    echo "❌ Docker is not running"
    exit 1
fi
echo "✅ Docker is running"

# Check if docker-compose file exists
COMPOSE_FILE="docker-compose.$ENVIRONMENT.yml"
if [ ! -f "$COMPOSE_FILE" ]; then
    echo "❌ Compose file not found: $COMPOSE_FILE"
    exit 1
fi
echo "✅ Compose file found"

# Create backup
echo -e "\n[Creating Backup]"
BACKUP_DIR="/opt/backups/pre-deploy-$(date +%Y%m%d_%H%M%S)"
mkdir -p "$BACKUP_DIR"

if docker ps -q --filter "name=piano-tutor-db" > /dev/null 2>&1; then
    echo "Backing up database..."
    docker exec piano-tutor-db-$ENVIRONMENT pg_dump -U piano_tutor piano_tutor > "$BACKUP_DIR/dump.sql"
    gzip "$BACKUP_DIR/dump.sql"
    echo "✅ Database backup created: $BACKUP_DIR/dump.sql.gz"
else
    echo "⚠️  Database container not running, skipping backup"
fi

# Pull latest images
echo -e "\n[Pulling Images]"
export VERSION=$VERSION
docker-compose -f "$COMPOSE_FILE" pull

# Deploy
echo -e "\n[Deploying]"

if [ "$ENVIRONMENT" = "production" ]; then
    # Blue-Green deployment for production
    CURRENT_COLOR=$(docker ps --filter "label=com.piano-tutor.deployment-color" --format "{{.Label \"com.piano-tutor.deployment-color\"}}" | head -1 || echo "blue")

    if [ "$CURRENT_COLOR" = "blue" ]; then
        NEW_COLOR="green"
        FRONTEND_PORT=3001
        BACKEND_PORT=8001
    else
        NEW_COLOR="blue"
        FRONTEND_PORT=3000
        BACKEND_PORT=8000
    fi

    echo "Current deployment: $CURRENT_COLOR"
    echo "New deployment: $NEW_COLOR"

    export DEPLOYMENT_COLOR=$NEW_COLOR
    export FRONTEND_PORT=$FRONTEND_PORT
    export BACKEND_PORT=$BACKEND_PORT

    # Start new environment
    docker-compose -f "$COMPOSE_FILE" -p "piano-tutor-$NEW_COLOR" up -d

    # Wait for health checks
    echo -e "\n[Waiting for Health Checks]"
    sleep 30

    MAX_RETRIES=10
    RETRY=0
    while [ $RETRY -lt $MAX_RETRIES ]; do
        if curl -f "http://localhost:$FRONTEND_PORT/health" > /dev/null 2>&1 && \
           curl -f "http://localhost:$BACKEND_PORT/health" > /dev/null 2>&1; then
            echo "✅ Health checks passed"
            break
        fi
        RETRY=$((RETRY + 1))
        echo "Attempt $RETRY/$MAX_RETRIES - waiting..."
        sleep 5
    done

    if [ $RETRY -eq $MAX_RETRIES ]; then
        echo "❌ Health checks failed"
        echo "Rolling back..."
        docker-compose -f "$COMPOSE_FILE" -p "piano-tutor-$NEW_COLOR" down
        exit 1
    fi

    # Switch traffic (manual step - update load balancer)
    echo -e "\n⚠️  Manual step required:"
    echo "Update load balancer to point to:"
    echo "  Frontend: localhost:$FRONTEND_PORT"
    echo "  Backend: localhost:$BACKEND_PORT"
    read -p "Press Enter when load balancer is updated..."

    # Stop old environment
    echo "Stopping old environment ($CURRENT_COLOR)..."
    docker-compose -f "$COMPOSE_FILE" -p "piano-tutor-$CURRENT_COLOR" down

else
    # Simple deployment for staging
    docker-compose -f "$COMPOSE_FILE" down
    docker-compose -f "$COMPOSE_FILE" up -d

    # Wait for health checks
    echo -e "\n[Waiting for Health Checks]"
    sleep 20

    if ! curl -f "http://localhost:3000/health" > /dev/null 2>&1 || \
       ! curl -f "http://localhost:8000/health" > /dev/null 2>&1; then
        echo "❌ Health checks failed"
        exit 1
    fi
    echo "✅ Health checks passed"
fi

# Post-deployment verification
echo -e "\n[Post-Deployment Verification]"
./scripts/health-check.sh local

echo -e "\n========================================="
echo "✅ Deployment completed successfully"
echo "Environment: $ENVIRONMENT"
echo "Version: $VERSION"
echo "Backup: $BACKUP_DIR"
echo "========================================="

exit 0
