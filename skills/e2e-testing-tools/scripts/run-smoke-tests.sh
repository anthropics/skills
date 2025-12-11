#!/bin/bash
# Run critical smoke tests only
# Usage: ./scripts/run-smoke-tests.sh [--headed] [--debug]

set -e

HEADED=""
DEBUG=""

while [[ $# -gt 0 ]]; do
  case $1 in
    --headed)
      HEADED="--headed"
      shift
      ;;
    --debug)
      DEBUG="--debug"
      shift
      ;;
    *)
      echo "Unknown option: $1"
      exit 1
      ;;
  esac
done

echo "🔥 Running E2E smoke tests (critical paths only)..."
echo "=================================================="

if command -v npx &> /dev/null; then
  # Playwright
  if [ -f "playwright.config.ts" ]; then
    echo "Running Playwright smoke tests..."
    npx playwright test --grep @smoke $HEADED $DEBUG
  # Cypress
  elif [ -f "cypress.config.js" ]; then
    echo "Running Cypress smoke tests..."
    if [ "$HEADED" == "--headed" ]; then
      npx cypress open
    else
      npx cypress run --spec "cypress/e2e/smoke/**"
    fi
  else
    echo "❌ No Playwright or Cypress config found"
    exit 1
  fi
else
  # Python with pytest-playwright
  echo "Running pytest-playwright smoke tests..."
  pytest tests/e2e -m smoke -v
fi

echo "=================================================="
echo "✅ Smoke tests completed"
