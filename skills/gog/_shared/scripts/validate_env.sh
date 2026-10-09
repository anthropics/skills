#!/usr/bin/env bash
# validate_env.sh - Check if GOG environment is properly configured

set -euo pipefail

# Colors for output (if terminal supports it)
if [ -t 1 ]; then
  RED='\033[0;31m'
  GREEN='\033[0;32m'
  YELLOW='\033[1;33m'
  NC='\033[0m' # No Color
else
  RED=''
  GREEN=''
  YELLOW=''
  NC=''
fi

echo "=== GOG Environment Validation ==="
echo

EXIT_CODE=0

# Check 1: GOG command exists
echo -n "Checking for 'gog' command... "
if command -v gog >/dev/null 2>&1; then
  echo -e "${GREEN}FOUND${NC}"
  GOG_PATH=$(command -v gog)
  echo "  Location: $GOG_PATH"

  # Try to get version
  if GOG_VERSION=$(gog version 2>/dev/null); then
    echo "  Version: $GOG_VERSION"
  else
    echo -e "  ${YELLOW}Warning: Could not retrieve version${NC}"
  fi
else
  echo -e "${RED}NOT FOUND${NC}"
  EXIT_CODE=1
  echo
  echo -e "${YELLOW}GOG CLI is not installed or not on PATH.${NC}"
  echo
  echo "To fix this:"
  echo "  1. Install GOG CLI (if available)"
  echo "  2. Add GOG to your PATH"
  echo "  3. Or create a GOG shim/wrapper script"
  echo
  echo "For more information, see:"
  echo "  skills/gog/_shared/references/gog-interface.md"
  echo
  exit $EXIT_CODE
fi

echo

# Check 2: GOG authentication
echo -n "Checking GOG authentication... "
if gog gmail search "is:inbox" --max 1 --json >/dev/null 2>&1; then
  echo -e "${GREEN}AUTHENTICATED${NC}"
else
  echo -e "${RED}NOT AUTHENTICATED${NC}"
  EXIT_CODE=1
  echo
  echo -e "${RED}═══════════════════════════════════════════════════════════${NC}"
  echo -e "${RED}  AUTHENTICATION REQUIRED${NC}"
  echo -e "${RED}═══════════════════════════════════════════════════════════${NC}"
  echo
  echo -e "${YELLOW}GOG requires Google Cloud OAuth2 credentials to access your data.${NC}"
  echo
  echo "FIRST TIME SETUP:"
  echo "  1. Set up OAuth2 credentials in Google Cloud Console"
  echo "     👉 https://github.com/steipete/gogcli?tab=readme-ov-file#1-get-oauth2-credentials"
  echo
  echo "  2. Create a Google Cloud project and enable:"
  echo "     - Gmail API"
  echo "     - Google Calendar API"
  echo "     - Google Tasks API"
  echo
  echo "  3. Create OAuth2 credentials (Desktop app type)"
  echo "     - Download the credentials JSON file"
  echo
  echo "  4. Authenticate GOG:"
  echo "     gog auth login"
  echo "     (Paste your client ID and secret when prompted)"
  echo
  echo "ALREADY HAVE CREDENTIALS?"
  echo "  Just run: gog auth login"
  echo "  (GOG will open browser for OAuth consent)"
  echo
  echo "For detailed instructions, see:"
  echo "  skills/gog/_shared/references/gog-interface.md"
  echo "  skills/gog/README.md (Step 0)"
  echo
  echo -e "${RED}═══════════════════════════════════════════════════════════${NC}"
  echo
  exit $EXIT_CODE
fi

echo

# Check 3: Audit log directory
echo -n "Checking audit log directory... "
AUDIT_DIR="$HOME/.gog-assistant"
AUDIT_LOG="$AUDIT_DIR/audit.log"

if [ -d "$AUDIT_DIR" ]; then
  echo -e "${GREEN}EXISTS${NC}"
  echo "  Location: $AUDIT_DIR"

  # Check permissions
  if [ -w "$AUDIT_DIR" ]; then
    echo -e "  Permissions: ${GREEN}Writable${NC}"
  else
    echo -e "  Permissions: ${RED}Not writable${NC}"
    EXIT_CODE=1
  fi

  # Check if log file exists
  if [ -f "$AUDIT_LOG" ]; then
    LOG_SIZE=$(wc -c < "$AUDIT_LOG" | tr -d ' ')
    LOG_LINES=$(wc -l < "$AUDIT_LOG" | tr -d ' ')
    echo "  Log file: $AUDIT_LOG ($LOG_LINES lines, $LOG_SIZE bytes)"
  else
    echo "  Log file: Does not exist yet (will be created on first action)"
  fi
else
  echo -e "${YELLOW}NOT FOUND${NC}"
  echo "  Creating: $AUDIT_DIR"
  mkdir -p "$AUDIT_DIR"
  chmod 700 "$AUDIT_DIR"
  echo -e "  ${GREEN}Created successfully${NC}"
fi

echo

# Check 4: Follow-up store
echo -n "Checking follow-up store... "
FOLLOWUP_STORE="$AUDIT_DIR/followups.json"

if [ -f "$FOLLOWUP_STORE" ]; then
  echo -e "${GREEN}EXISTS${NC}"
  echo "  Location: $FOLLOWUP_STORE"

  # Validate JSON
  if jq empty "$FOLLOWUP_STORE" 2>/dev/null; then
    FOLLOWUP_COUNT=$(jq 'length' "$FOLLOWUP_STORE" 2>/dev/null || echo "0")
    echo -e "  Status: ${GREEN}Valid JSON${NC} ($FOLLOWUP_COUNT items)"
  else
    echo -e "  Status: ${RED}Invalid JSON${NC}"
    EXIT_CODE=1
  fi
else
  echo -e "${YELLOW}NOT FOUND${NC}"
  echo "  This is OK - will be created when first follow-up is added"
fi

echo

# Check 5: Required tools
echo "Checking optional dependencies:"

check_tool() {
  local tool=$1
  local purpose=$2
  echo -n "  $tool ($purpose)... "
  if command -v "$tool" >/dev/null 2>&1; then
    echo -e "${GREEN}FOUND${NC}"
  else
    echo -e "${YELLOW}NOT FOUND${NC}"
  fi
}

check_tool "jq" "JSON parsing"
check_tool "curl" "HTTP requests"
check_tool "python3" "Python scripts"

echo

# Summary
if [ $EXIT_CODE -eq 0 ]; then
  echo -e "${GREEN}=== VALIDATION PASSED ===${NC}"
  echo "Your GOG environment is properly configured."
  echo
  echo "Next steps:"
  echo "  - Load a GOG skill in Claude Code"
  echo "  - Run smoke tests: bash skills/gog/_shared/scripts/smoke_test.sh"
  echo "  - Review documentation: skills/gog/README.md"
else
  echo -e "${RED}=== VALIDATION FAILED ===${NC}"
  echo "Please fix the issues above and run this script again."
fi

echo

exit $EXIT_CODE
