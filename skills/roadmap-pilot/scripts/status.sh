#!/bin/bash
# status.sh - Visual progress dashboard for roadmap section ONLY
# Usage: ./status.sh [path-to-claude-md]
#
# Only parses the ## Roadmap section, ignoring Test Flows, QA, etc.

CLAUDE_MD="${1:-CLAUDE.md}"

if [ ! -f "$CLAUDE_MD" ]; then
  echo "ERROR: $CLAUDE_MD not found"
  exit 1
fi

# Colors
if [ -t 1 ]; then
  BOLD='\033[1m'
  GREEN='\033[0;32m'
  YELLOW='\033[1;33m'
  BLUE='\033[0;34m'
  DIM='\033[2m'
  NC='\033[0m'
  FILLED='█'
  EMPTY='░'
else
  BOLD='' GREEN='' YELLOW='' BLUE='' DIM='' NC=''
  FILLED='#'
  EMPTY='-'
fi

BAR_WIDTH=20

draw_bar() {
  local done=$1
  local total=$2
  local filled=0

  if [ "$total" -gt 0 ]; then
    filled=$(( (done * BAR_WIDTH) / total ))
  fi

  local empty=$((BAR_WIDTH - filled))
  local bar=""

  for ((i=0; i<filled; i++)); do bar+="${FILLED}"; done
  for ((i=0; i<empty; i++)); do bar+="${EMPTY}"; done

  echo -n "$bar"
}

# Extract only the ## Roadmap section (awk for reliable extraction)
ROADMAP_SECTION=$(awk '
  /^## Roadmap/ { found=1; next }
  found && /^## [^#]/ { exit }
  found { print }
' "$CLAUDE_MD")

if [ -z "$ROADMAP_SECTION" ]; then
  echo "ERROR: No '## Roadmap' section found in $CLAUDE_MD"
  exit 1
fi

echo ""
echo -e "${BOLD}  ROADMAP PROGRESS${NC}"
echo -e "  ─────────────────────────────────────────────"
echo ""

# Parse phases within roadmap section only
CURRENT_PHASE=""
PHASE_DONE=0
PHASE_TOTAL=0
TOTAL_DONE=0
TOTAL_ALL=0

print_phase() {
  if [ -n "$CURRENT_PHASE" ]; then
    local bar=$(draw_bar "$PHASE_DONE" "$PHASE_TOTAL")
    local pct=0
    if [ "$PHASE_TOTAL" -gt 0 ]; then
      pct=$(( (PHASE_DONE * 100) / PHASE_TOTAL ))
    fi

    local color="$YELLOW"
    if [ "$PHASE_DONE" -eq "$PHASE_TOTAL" ]; then
      color="$GREEN"
    fi

    printf "  ${color}%-28s %s %d/%d (%d%%)${NC}\n" "$CURRENT_PHASE" "$bar" "$PHASE_DONE" "$PHASE_TOTAL" "$pct"
  fi
}

while IFS= read -r line; do
  # Detect phase headers (### Phase N - Description)
  if echo "$line" | grep -qE '^###\s+'; then
    print_phase
    CURRENT_PHASE=$(echo "$line" | sed 's/^###\s*//')
    PHASE_DONE=0
    PHASE_TOTAL=0
  fi

  # Count checked tasks
  if echo "$line" | grep -qE '^\- \[x\]'; then
    PHASE_DONE=$((PHASE_DONE + 1))
    PHASE_TOTAL=$((PHASE_TOTAL + 1))
    TOTAL_DONE=$((TOTAL_DONE + 1))
    TOTAL_ALL=$((TOTAL_ALL + 1))
  fi

  # Count unchecked tasks
  if echo "$line" | grep -qE '^\- \[ \]'; then
    PHASE_TOTAL=$((PHASE_TOTAL + 1))
    TOTAL_ALL=$((TOTAL_ALL + 1))
  fi
done <<< "$ROADMAP_SECTION"

# Print last phase
print_phase

# Total
echo ""
echo -e "  ─────────────────────────────────────────────"

TOTAL_BAR=$(draw_bar "$TOTAL_DONE" "$TOTAL_ALL")
TOTAL_PCT=0
if [ "$TOTAL_ALL" -gt 0 ]; then
  TOTAL_PCT=$(( (TOTAL_DONE * 100) / TOTAL_ALL ))
fi

TOTAL_COLOR="$YELLOW"
if [ "$TOTAL_DONE" -eq "$TOTAL_ALL" ] && [ "$TOTAL_ALL" -gt 0 ]; then
  TOTAL_COLOR="$GREEN"
fi

printf "\n  ${BOLD}${TOTAL_COLOR}%-28s %s %d/%d (%d%%)${NC}\n" "TOTAL" "$TOTAL_BAR" "$TOTAL_DONE" "$TOTAL_ALL" "$TOTAL_PCT"

# Show next task (from roadmap section only)
NEXT=$(echo "$ROADMAP_SECTION" | grep '^\- \[ \]' | head -1 | sed 's/^- \[ \] //')
if [ -n "$NEXT" ]; then
  echo ""
  echo -e "  ${BLUE}Next:${NC} $NEXT"
fi

echo ""
