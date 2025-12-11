#!/bin/bash
# Generate detailed architecture plan with high reasoning
# Usage: codex-plan.sh "Plan: migrate to microservices"

set -e

if [ $# -eq 0 ]; then
    echo "Usage: codex-plan.sh \"<planning-task>\""
    echo ""
    echo "Examples:"
    echo "  codex-plan.sh \"Plan: migrate to SQLAlchemy 2.x\""
    echo "  codex-plan.sh \"Plan: refactor to hexagonal architecture\""
    echo "  codex-plan.sh \"Plan: add async support to API\""
    exit 1
fi

PROMPT="$1"
OUTPUT="${2:-plan.md}"

echo "📋 Generating plan with Codex (gpt-5-codex)..."
echo "   Prompt: $PROMPT"
echo "   Output: $OUTPUT"
echo ""

codex exec \
  --output-last-message "$OUTPUT" \
  -m gpt-5-codex \
  "$PROMPT"

echo "✅ Plan generated: $OUTPUT"
echo ""
echo "📖 Preview:"
head -20 "$OUTPUT"
