#!/bin/bash
# Generate and open HTML coverage report

set -e

echo "📊 Generating coverage report..."
npm test -- --coverage --reporter=verbose

if [ -f coverage/index.html ]; then
    echo ""
    echo "✅ Coverage report generated!"
    echo ""
    echo "Opening coverage report in browser..."

    if command -v open &> /dev/null; then
        open coverage/index.html
    elif command -v xdg-open &> /dev/null; then
        xdg-open coverage/index.html
    else
        echo "   📂 Open coverage/index.html manually"
    fi
else
    echo "❌ Coverage report not found at coverage/index.html"
    exit 1
fi
