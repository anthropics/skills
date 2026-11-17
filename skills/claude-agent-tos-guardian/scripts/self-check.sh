#!/bin/bash
# TOS Guardian Self-Check Script
# Run at agent startup and every 4 hours via cron
# Exit codes: 0 = all clear, 1 = warnings, 2 = violations (agent should pause)

set -euo pipefail

AUDIT_LOG="${TOS_GUARDIAN_AUDIT_PATH:-/var/log/tos_audit.log}"
WARN_HOURS="${TOS_GUARDIAN_TOKEN_WARN_HOURS:-4}"
NOTIFY_METHOD="${TOS_GUARDIAN_NOTIFY_METHOD:-none}"
NOTIFY_TARGET="${TOS_GUARDIAN_NOTIFY_TARGET:-}"
STATUS=0

timestamp() { date -u +"%Y-%m-%dT%H:%M:%SZ"; }

log_audit() {
  local rule="$1" level="$2" msg="$3"
  echo "[$(timestamp)] [RULE_${rule}] [${level}] ${msg}" >> "$AUDIT_LOG"
}

echo "================================"
echo "TOS GUARDIAN SELF-CHECK"
echo "$(timestamp)"
echo "================================"

# Check token validity
CREDS_FILE="${HOME}/.claude/.credentials.json"
if [ -f "$CREDS_FILE" ] && command -v python3 &>/dev/null; then  TOKEN_STATUS=$(python3 -c "
import json, time
with open('$CREDS_FILE') as f:
    creds = json.load(f)
oauth = creds.get('claudeAiOauth', {})
exp = oauth.get('expiresAt', 0)
now = int(time.time() * 1000)
hours_left = (exp - now) / (1000*60*60)
if hours_left <= 0: print(f'EXPIRED|{hours_left:.1f}')
elif hours_left <= $WARN_HOURS: print(f'WARNING|{hours_left:.1f}')
else: print(f'VALID|{hours_left:.1f}')
" 2>/dev/null) || TOKEN_STATUS="ERROR|0"

  IFS='|' read -r TOKEN_STATE HOURS_LEFT <<< "$TOKEN_STATUS"
  case "$TOKEN_STATE" in
    VALID)   echo "  ✅ Token valid (${HOURS_LEFT}h remaining)";;
    WARNING) echo "  ⚠️  Token expiring (${HOURS_LEFT}h)"; STATUS=1;;
    EXPIRED) echo "  ❌ Token EXPIRED — agent must pause"; STATUS=2;;
    *)       echo "  ⚠️  Token check failed"; STATUS=1;;
  esac
  log_audit 1 "$TOKEN_STATE" "Token: ${HOURS_LEFT}h remaining"
fi

# Check sanctioned access
CLAUDE_BIN=$(which claude 2>/dev/null || echo "")
[ -n "$CLAUDE_BIN" ] && echo "  ✅ Claude Code CLI found" || echo "  ⚠️  Claude CLI not in PATH"

# Check for unsanctioned tools
for TOOL in opencode roo-code cline kilo; do
  command -v "$TOOL" &>/dev/null && { echo "  ❌ UNSANCTIONED: $TOOL"; STATUS=2; }
done
echo ""
echo "================================"
case $STATUS in
  0) echo "STATUS: ✅ ALL CLEAR — Agent may proceed" ;;
  1) echo "STATUS: ⚠️  WARNINGS — Proceed with caution" ;;
  2) echo "STATUS: ❌ VIOLATIONS — Agent MUST pause" ;;
esac
echo "================================"

exit $STATUS