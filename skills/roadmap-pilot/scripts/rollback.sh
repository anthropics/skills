#!/bin/bash
# rollback.sh - Safely revert the last roadmap commit
# Usage: ./rollback.sh [--dry-run]
#
# Reverts the last commit if it was a roadmap commit (matches [prefix] pattern).
# Also un-checks the task in CLAUDE.md that was marked done.

set -e

DRY_RUN=false
if [ "$1" = "--dry-run" ]; then
  DRY_RUN=true
fi

# Colors
if [ -t 1 ]; then
  BOLD='\033[1m'
  GREEN='\033[0;32m'
  YELLOW='\033[1;33m'
  RED='\033[0;31m'
  NC='\033[0m'
else
  BOLD='' GREEN='' YELLOW='' RED='' NC=''
fi

# Check we're in a git repo
if ! git rev-parse --is-inside-work-tree &>/dev/null; then
  echo -e "${RED}ERROR: Not a git repository${NC}"
  exit 1
fi

# Check there are no uncommitted changes
if [ -n "$(git status --porcelain)" ]; then
  echo -e "${RED}ERROR: You have uncommitted changes. Commit or stash them first.${NC}"
  exit 1
fi

# Get last commit info
LAST_MSG=$(git log -1 --pretty=format:'%s')
LAST_HASH=$(git log -1 --pretty=format:'%h')
LAST_FILES=$(git diff-tree --no-commit-id --name-only -r HEAD)

echo -e "${BOLD}Last commit:${NC}"
echo -e "  ${YELLOW}${LAST_HASH}${NC} ${LAST_MSG}"
echo ""
echo -e "${BOLD}Files changed:${NC}"
echo "$LAST_FILES" | while read -r f; do echo "  $f"; done
echo ""

# Verify it looks like a roadmap commit
if ! echo "$LAST_MSG" | grep -qE '^\['; then
  echo -e "${RED}WARNING: Last commit doesn't look like a roadmap commit (no [prefix]).${NC}"
  echo -e "${RED}Commit message: ${LAST_MSG}${NC}"
  echo ""
  read -p "Revert anyway? (y/N): " CONFIRM
  if [ "$CONFIRM" != "y" ] && [ "$CONFIRM" != "Y" ]; then
    echo "Aborted."
    exit 0
  fi
fi

if [ "$DRY_RUN" = true ]; then
  echo -e "${YELLOW}[DRY RUN] Would revert commit ${LAST_HASH}${NC}"
  echo -e "${YELLOW}[DRY RUN] No changes made.${NC}"
  exit 0
fi

# Revert
echo -e "${BOLD}Reverting...${NC}"
git revert HEAD --no-edit

echo ""
echo -e "${GREEN}Reverted successfully.${NC}"
echo ""
echo -e "${BOLD}What happened:${NC}"
echo "  - Created a new revert commit (safe, preserves history)"
echo "  - CLAUDE.md was restored to its previous state"
echo "  - The task that was marked [x] is now back to [ ]"
echo ""
echo -e "${YELLOW}Next: open Claude Code and run /roadmap to retry the task.${NC}"
