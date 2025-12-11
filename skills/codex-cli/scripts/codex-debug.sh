#!/bin/bash
# Capture full debugging session with detailed output
# Usage: codex-debug.sh "Debug: why is this async function hanging?"

set -e

if [ $# -eq 0 ]; then
    echo "Usage: codex-debug.sh \"<debugging-task>\""
    echo ""
    echo "Examples:"
    echo "  codex-debug.sh \"Debug: analyze error logs and suggest fixes\""
    echo "  codex-debug.sh \"Diagnose: why is memory usage growing\""
    echo "  codex-debug.sh \"Troubleshoot: intermittent database connection failures\""
    exit 1
fi

PROMPT="$1"
OUTPUT="${2:-debug-session.md}"

echo "🐛 Starting debug session with full output..."
echo "   Prompt: $PROMPT"
echo "   Output: $OUTPUT"
echo ""

# Capture with header
{
    echo "# Debug Session"
    echo "Generated: $(date)"
    echo "Prompt: $PROMPT"
    echo ""
    echo "## Analysis"
    echo ""
} > "$OUTPUT"

codex exec \
  --output-last-message /tmp/debug-result.txt \
  -m gpt-5-codex \
  "$PROMPT"

cat /tmp/debug-result.txt >> "$OUTPUT"
rm -f /tmp/debug-result.txt

echo "✅ Debug session captured: $OUTPUT"
echo ""
echo "📖 Full output:"
cat "$OUTPUT"
