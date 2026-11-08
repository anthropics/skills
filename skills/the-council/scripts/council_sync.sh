#!/usr/bin/env bash
# council_sync.sh — Sync project context to Codex (AGENTS.md) and Gemini (GEMINI.md)
#
# Usage: council_sync.sh [working_directory]
#   working_directory: defaults to current directory

set -euo pipefail

WORK_DIR="${1:-.}"
WORK_DIR="$(cd "$WORK_DIR" && pwd)"

CLAUDE_MD="$WORK_DIR/CLAUDE.md"
AGENTS_MD="$WORK_DIR/AGENTS.md"
GEMINI_MD="$WORK_DIR/GEMINI.md"

if [[ ! -f "$CLAUDE_MD" ]]; then
  echo "ERROR: No CLAUDE.md found in $WORK_DIR" >&2
  exit 1
fi

CLAUDE_CONTENT="$(cat "$CLAUDE_MD")"

# --- Write AGENTS.md for Codex ---
cat > "$AGENTS_MD" << 'PREAMBLE'
# Advisory Context (synced from CLAUDE.md)

You are being consulted as an external advisor on this project.
Review the project context below and provide your expert analysis when prompted.
Focus on correctness, potential issues, and alternative approaches.

---

PREAMBLE
echo "$CLAUDE_CONTENT" >> "$AGENTS_MD"

# --- Write GEMINI.md for Gemini ---
cat > "$GEMINI_MD" << 'PREAMBLE'
# Advisory Context (synced from CLAUDE.md)

You are being consulted as an external advisor on this project.
Review the project context below and provide your expert analysis when prompted.
Focus on correctness, potential issues, and alternative approaches.

---

PREAMBLE
echo "$CLAUDE_CONTENT" >> "$GEMINI_MD"

echo "Synced context to:"
echo "  - $AGENTS_MD ($(wc -l < "$AGENTS_MD") lines)"
echo "  - $GEMINI_MD ($(wc -l < "$GEMINI_MD") lines)"
