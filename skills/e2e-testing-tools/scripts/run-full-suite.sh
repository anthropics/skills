#!/bin/bash
# Run complete E2E regression suite
# Usage: ./scripts/run-full-suite.sh [--headed] [--workers=4]

set -e

HEADED=""
WORKERS="4"

while [[ $# -gt 0 ]]; do
  case $1 in
    --headed)
      HEADED="--headed"
      shift
      ;;
    --workers=*)
      WORKERS="${1#*=}"
      shift
      ;;
    *)
      echo "Unknown option: $1"
      exit 1
      ;;
  esac
done

echo "🚀 Running complete E2E regression suite..."
echo "=========================================="
echo "Workers: $WORKERS"
echo "Mode: $([ -n "$HEADED" ] && echo "headed" || echo "headless")"

if command -v npx &> /dev/null; then
  # Playwright
  if [ -f "playwright.config.ts" ]; then
    echo "Running Playwright full regression..."
    npx playwright test --workers=$WORKERS $HEADED
  # Cypress
  elif [ -f "cypress.config.js" ]; then
    echo "Running Cypress full regression..."
    npx cypress run --headless $([ -n "$HEADED" ] && echo "--headed")
  else
    echo "❌ No Playwright or Cypress config found"
    exit 1
  fi
else
  # Python with pytest-playwright
  echo "Running pytest-playwright full regression..."
  pytest tests/e2e -v -n auto
fi

echo "=========================================="
echo "✅ Full regression suite completed"
