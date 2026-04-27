#!/bin/bash
#
# Health check script for Piano Tutor Platform
# Usage: ./scripts/health-check.sh [staging|production]
#

set -e

ENVIRONMENT=${1:-production}

if [ "$ENVIRONMENT" = "production" ]; then
    FRONTEND_URL="https://piano-tutor.com"
    BACKEND_URL="https://api.piano-tutor.com"
elif [ "$ENVIRONMENT" = "staging" ]; then
    FRONTEND_URL="https://staging.piano-tutor.com"
    BACKEND_URL="https://api-staging.piano-tutor.com"
else
    FRONTEND_URL="http://localhost:3000"
    BACKEND_URL="http://localhost:8000"
fi

echo "========================================="
echo "Piano Tutor Health Check - $ENVIRONMENT"
echo "$(date)"
echo "========================================="

# Frontend health check
echo -e "\n[Frontend Health]"
FRONTEND_STATUS=$(curl -s -o /dev/null -w "%{http_code}" "$FRONTEND_URL/health" || echo "000")
if [ "$FRONTEND_STATUS" = "200" ]; then
    echo "✅ Frontend: Healthy ($FRONTEND_STATUS)"
else
    echo "❌ Frontend: Unhealthy ($FRONTEND_STATUS)"
    exit 1
fi

# Backend health check
echo -e "\n[Backend Health]"
BACKEND_HEALTH=$(curl -s "$BACKEND_URL/health" || echo '{"status":"error"}')
BACKEND_STATUS=$(echo "$BACKEND_HEALTH" | jq -r '.status' 2>/dev/null || echo "error")
if [ "$BACKEND_STATUS" = "healthy" ]; then
    echo "✅ Backend: Healthy"
    echo "$BACKEND_HEALTH" | jq '.'
else
    echo "❌ Backend: Unhealthy"
    echo "$BACKEND_HEALTH"
    exit 1
fi

# Backend readiness check
echo -e "\n[Backend Readiness]"
BACKEND_READY=$(curl -s "$BACKEND_URL/health/ready" || echo '{"status":"error"}')
READY_STATUS=$(echo "$BACKEND_READY" | jq -r '.status' 2>/dev/null || echo "error")
if [ "$READY_STATUS" = "ready" ]; then
    echo "✅ Backend: Ready"
    echo "$BACKEND_READY" | jq '.checks'
else
    echo "❌ Backend: Not Ready"
    echo "$BACKEND_READY" | jq '.'
    exit 1
fi

# Detailed metrics (optional)
if [ "$2" = "--detailed" ]; then
    echo -e "\n[Detailed Metrics]"
    curl -s "$BACKEND_URL/health/detailed" | jq '.'
fi

echo -e "\n========================================="
echo "✅ All health checks passed"
echo "========================================="

exit 0
