#!/bin/bash
# Perform detailed code review with high reasoning
# Usage: codex-review.sh "Review src/ for security issues"

set -e

if [ $# -eq 0 ]; then
    echo "Usage: codex-review.sh \"<review-task>\""
    echo ""
    echo "Examples:"
    echo "  codex-review.sh \"Review src/ for security vulnerabilities\""
    echo "  codex-review.sh \"Code review: check design patterns in api/\""
    echo "  codex-review.sh \"Review database schema for normalization issues\""
    exit 1
fi

PROMPT="$1"
OUTPUT="${2:-review.md}"

echo "🔍 Performing code review with Codex (gpt-5-codex)..."
echo "   Prompt: $PROMPT"
echo "   Output: $OUTPUT"
echo ""

codex exec \
  --output-last-message "$OUTPUT" \
  -m gpt-5-codex \
  "$PROMPT"

echo "✅ Review complete: $OUTPUT"
echo ""
echo "📖 Preview:"
head -30 "$OUTPUT"
