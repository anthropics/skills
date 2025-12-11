#!/bin/bash
# Run test suite with coverage reporting

set -e

echo "🧪 Running test suite with coverage..."
npm test -- --coverage --reporter=verbose

echo ""
echo "✅ Tests completed!"
echo ""
echo "📊 Coverage report generated in ./coverage"
echo "   Open coverage/index.html to view detailed report"
