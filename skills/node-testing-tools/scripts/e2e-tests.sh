#!/bin/bash
# Run E2E tests with Playwright

set -e

echo "🎭 Running E2E tests with Playwright..."

# Check if app is running
if ! curl -s http://localhost:3000 > /dev/null 2>&1; then
    echo ""
    echo "⚠️  Warning: Application not detected at http://localhost:3000"
    echo "   Make sure your app is running before E2E tests"
    echo ""
fi

echo ""
echo "Running tests..."
npx playwright test --reporter=html

echo ""
echo "✅ E2E tests completed!"
echo ""
echo "📹 Test artifacts:"
echo "   - HTML report: playwright-report/index.html"
echo "   - Videos: test-results/*/video.webm"
echo "   - Screenshots: test-results/*/*.png"
echo ""

if command -v open &> /dev/null; then
    echo "Opening test report..."
    open playwright-report/index.html
fi
