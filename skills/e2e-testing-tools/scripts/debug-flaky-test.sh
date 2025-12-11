#!/bin/bash
# Debug a flaky test with tracing and replay
# Usage: ./scripts/debug-flaky-test.sh tests/checkout.spec.ts

set -e

if [ -z "$1" ]; then
  echo "Usage: $0 <test-file> [--headed] [--retries=3]"
  echo "Example: $0 tests/checkout.spec.ts --headed --retries=3"
  exit 1
fi

TEST_FILE="$1"
HEADED=""
RETRIES="3"

shift

while [[ $# -gt 0 ]]; do
  case $1 in
    --headed)
      HEADED="--headed"
      shift
      ;;
    --retries=*)
      RETRIES="${1#*=}"
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

echo "🐛 Debugging flaky test: $TEST_FILE"
echo "=================================="
echo "Retries: $RETRIES"
echo "Mode: $([ -n "$HEADED" ] && echo "headed (visible)" || echo "headless")"

if command -v npx &> /dev/null; then
  if [ -f "playwright.config.ts" ]; then
    echo ""
    echo "Running Playwright with trace recording..."
    npx playwright test "$TEST_FILE" \
      --trace on \
      --retries $RETRIES \
      $HEADED \
      $DEBUG

    echo ""
    echo "📊 Analyzing test results..."
    TRACE_FILE=$(find . -name "trace.zip" -type f -printf '%T@ %p\n' | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$TRACE_FILE" ]; then
      echo "✅ Trace recorded: $TRACE_FILE"
      echo ""
      echo "View the trace:"
      echo "  npx playwright show-trace $TRACE_FILE"
    fi

    # Check for videos
    if [ -d "test-results" ]; then
      VIDEOS=$(find test-results -name "*.webm" 2>/dev/null || true)
      if [ -n "$VIDEOS" ]; then
        echo ""
        echo "📹 Videos recorded:"
        echo "$VIDEOS"
      fi
    fi
  else
    echo "❌ Playwright config not found"
    exit 1
  fi
else
  echo "❌ npm/npx not available"
  exit 1
fi

echo ""
echo "=================================="
echo "🔍 Next steps:"
echo "1. Review the trace or video above"
echo "2. Check for race conditions or timing issues"
echo "3. Verify selectors are stable"
echo "4. Check for external API flakiness"
echo ""
