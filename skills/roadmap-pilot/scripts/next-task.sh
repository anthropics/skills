#!/bin/bash
# Finds the next unchecked task in CLAUDE.md roadmap section ONLY
# Usage: ./next-task.sh [path-to-claude-md]
#
# Only searches within the ## Roadmap section, ignoring other sections
# like Test Flows, QA Checklists, etc. that may also contain checkboxes.

CLAUDE_MD="${1:-CLAUDE.md}"

if [ ! -f "$CLAUDE_MD" ]; then
  echo "ERROR: $CLAUDE_MD not found"
  exit 1
fi

# Extract only the ## Roadmap section
# From "## Roadmap" until the next "## " heading (or end of file)
# Uses awk for reliable section extraction
ROADMAP_SECTION=$(awk '
  /^## Roadmap/ { found=1; next }
  found && /^## [^#]/ { exit }
  found { print }
' "$CLAUDE_MD")

if [ -z "$ROADMAP_SECTION" ]; then
  echo "ERROR: No '## Roadmap' section found in $CLAUDE_MD"
  exit 1
fi

# Find next unchecked task within roadmap section only
NEXT_TASK=$(echo "$ROADMAP_SECTION" | grep '^\- \[ \]' | head -1 | sed 's/^- \[ \] //')

if [ -z "$NEXT_TASK" ]; then
  echo "DONE: All roadmap tasks completed"
  exit 0
fi

# Find the actual line number in the original file
LINE_NUM=$(grep -n '^\- \[ \]' "$CLAUDE_MD" | while IFS=: read -r num line; do
  # Verify this line is within the roadmap section by checking it appears
  # after "## Roadmap" and before the next "## " section
  ROADMAP_START=$(grep -n '^## Roadmap' "$CLAUDE_MD" | head -1 | cut -d: -f1)
  NEXT_SECTION=$(awk "NR>$ROADMAP_START && /^## [^#]/{print NR; exit}" "$CLAUDE_MD")
  if [ -z "$NEXT_SECTION" ]; then
    NEXT_SECTION=999999
  fi
  if [ "$num" -gt "$ROADMAP_START" ] && [ "$num" -lt "$NEXT_SECTION" ]; then
    echo "$num"
    break
  fi
done)

echo "NEXT_TASK_LINE=$LINE_NUM"
echo "NEXT_TASK=$NEXT_TASK"

# Count progress (roadmap section only)
TOTAL=$(echo "$ROADMAP_SECTION" | grep -c '^\- \[.\]')
DONE=$(echo "$ROADMAP_SECTION" | grep -c '^\- \[x\]')
echo "PROGRESS=$DONE/$TOTAL"
