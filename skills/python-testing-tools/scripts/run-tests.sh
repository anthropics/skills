#!/usr/bin/env bash
# Run Python tests with appropriate options
# Usage: ./run-tests.sh [target] [options]

set -euo pipefail

TARGET="${1:-.}"
SHIFT="${SHIFT:-0}"
if [ "$SHIFT" -eq 1 ]; then shift; fi

echo "Running tests in: $TARGET"
echo ""

# Check required tools
if ! command -v pytest &> /dev/null; then
    echo "Error: pytest not installed. Run: uv pip install pytest"
    exit 1
fi

# Run tests with coverage
pytest "$TARGET" \
    --cov=src \
    --cov-report=term-missing \
    --cov-report=html \
    -v \
    "$@"

echo ""
echo "Coverage report generated in htmlcov/index.html"
