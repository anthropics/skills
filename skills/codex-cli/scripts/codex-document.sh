#!/bin/bash
# Generate or improve documentation
# Usage: codex-document.sh "Write comprehensive API documentation for src/api/"

set -e

if [ $# -eq 0 ]; then
    echo "Usage: codex-document.sh \"<documentation-task>\""
    echo ""
    echo "Examples:"
    echo "  codex-document.sh \"Write comprehensive API documentation\""
    echo "  codex-document.sh \"Generate architecture decision records (ADRs)\""
    echo "  codex-document.sh \"Create deployment guide for production\""
    exit 1
fi

PROMPT="$1"
OUTPUT="${2:-documentation.md}"
MODEL="${3:-gpt-5}"

echo "📚 Generating documentation..."
echo "   Prompt: $PROMPT"
echo "   Output: $OUTPUT"
echo "   Model: $MODEL"
echo ""

codex exec \
  --output-last-message "$OUTPUT" \
  -m "$MODEL" \
  "$PROMPT"

echo "✅ Documentation generated: $OUTPUT"
echo ""
echo "📖 Preview:"
head -25 "$OUTPUT"
