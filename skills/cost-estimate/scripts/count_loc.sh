#!/usr/bin/env bash
# count_loc.sh — Fast LOC count with graceful fallback.
#
# Tries cloc → tokei → scc in order (each handles exclusions properly).
# Falls back to `find + wc` with the standard exclusion list.
# Prints a single integer (total counted LOC) to stdout.
#
# Usage: bash scripts/count_loc.sh [path]
set -euo pipefail
ROOT="${1:-.}"

# Preferred: real counters
if command -v cloc >/dev/null 2>&1; then
  cloc --vcs=git --quiet "$ROOT" 2>/dev/null \
    | awk '/^SUM:/ {print $NF; found=1} END{exit !found}' && exit 0
fi
if command -v tokei >/dev/null 2>&1; then
  tokei --output=json "$ROOT" 2>/dev/null \
    | python3 -c "import sys,json; d=json.load(sys.stdin); print(d['Total']['code'])" && exit 0
fi
if command -v scc >/dev/null 2>&1; then
  scc --format=json "$ROOT" 2>/dev/null \
    | python3 -c "import sys,json; print(sum(l['Code'] for l in json.load(sys.stdin)))" && exit 0
fi

# Fallback: filtered find + wc (counts LINES, not files)
find "$ROOT" -type f \
  \( -name "*.ts" -o -name "*.tsx" -o -name "*.js" -o -name "*.jsx" \
     -o -name "*.py" -o -name "*.go" -o -name "*.rs" -o -name "*.java" \
     -o -name "*.rb" -o -name "*.php" -o -name "*.swift" -o -name "*.kt" \
     -o -name "*.cpp" -o -name "*.cc" -o -name "*.c" -o -name "*.h" -o -name "*.hpp" \) \
  -not -path "*/node_modules/*" -not -path "*/.git/*" \
  -not -path "*/dist/*" -not -path "*/build/*" -not -path "*/vendor/*" \
  -not -path "*/.venv/*" -not -path "*/__pycache__/*" -not -path "*/target/*" \
  -not -path "*/.next/*" \
  -print0 2>/dev/null \
  | xargs -0 wc -l 2>/dev/null \
  | awk 'END {print $1+0}'
