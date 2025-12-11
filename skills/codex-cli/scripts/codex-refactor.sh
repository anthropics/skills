#!/bin/bash
# Analyze and propose refactoring with reasoning
# Usage: codex-refactor.sh "Refactor src/utils/ to improve testability"

set -e

if [ $# -eq 0 ]; then
    echo "Usage: codex-refactor.sh \"<refactoring-task>\""
    echo ""
    echo "Examples:"
    echo "  codex-refactor.sh \"Refactor to extract interfaces from handlers\""
    echo "  codex-refactor.sh \"Improve testability: add dependency injection\""
    echo "  codex-refactor.sh \"Modernize: convert callbacks to async/await\""
    exit 1
fi

PROMPT="$1"
OUTPUT="${2:-refactoring-plan.md}"

echo "🔧 Analyzing refactoring opportunities with Codex..."
echo "   Prompt: $PROMPT"
echo "   Output: $OUTPUT"
echo ""

codex exec \
  --output-last-message "$OUTPUT" \
  -m gpt-5-codex \
  "$PROMPT"

echo "✅ Refactoring analysis complete: $OUTPUT"
echo ""
echo "📖 Preview:"
head -30 "$OUTPUT"
