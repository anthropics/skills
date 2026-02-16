#!/usr/bin/env bash
# cmail UserPromptSubmit hook — notify Claude of new messages before processing each prompt
set -euo pipefail

INBOX_DIR="$HOME/.cmail/inbox"
UNREAD_MARKER="$HOME/.cmail/.has_unread"

# Fast path: no marker means no new messages
if [[ ! -f "$UNREAD_MARKER" ]]; then
  exit 0
fi

count=$(ls -1 "$INBOX_DIR"/*.json 2>/dev/null | wc -l | tr -d ' ') || count=0
if (( count == 0 )); then
  exit 0
fi

context="FYI: You have ${count} unread cmail message(s). Run \`cmail inbox show --if-new\` to check them."

if command -v jq &>/dev/null; then
  jq -n --arg ctx "$context" '{"additionalContext": $ctx}'
else
  echo "$context" | python3 -c "import json,sys; print(json.dumps({'additionalContext': sys.stdin.read()}))"
fi

exit 0
