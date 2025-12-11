#!/bin/bash
# Deploy ml-gradle application to multiple environments
# Usage: ./scripts/deploy-all-envs.sh [--skip-tests]

set -e

SKIP_TESTS=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --skip-tests)
      SKIP_TESTS=true
      shift
      ;;
    *)
      echo "Unknown option: $1"
      exit 1
      ;;
  esac
done

echo "🚀 Deploying to all environments..."
echo "===================================="

# Deploy to dev
echo ""
echo "📦 Deploying to DEV environment..."
gradle mlDeploy -PenvironmentName=dev

if [ "$SKIP_TESTS" = false ]; then
  echo "🧪 Running tests on DEV..."
  gradle mlUnitTest -PenvironmentName=dev
fi

# Deploy to test (requires approval in real workflow)
echo ""
read -p "Deploy to TEST environment? (y/n) " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
  echo "📦 Deploying to TEST environment..."
  gradle mlDeploy -PenvironmentName=test

  if [ "$SKIP_TESTS" = false ]; then
    echo "🧪 Running tests on TEST..."
    gradle mlUnitTest -PenvironmentName=test
  fi
else
  echo "Skipping TEST deployment"
fi

# Deploy to prod (requires approval in real workflow)
echo ""
read -p "Deploy to PROD environment? (y/n) " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
  echo "⚠️  WARNING: Deploying to PRODUCTION"
  echo "📦 Deploying to PROD environment..."
  gradle mlDeploy -PenvironmentName=prod

  echo "✅ PROD deployment complete"
else
  echo "Skipping PROD deployment"
fi

echo ""
echo "===================================="
echo "✅ Deployment workflow complete"
