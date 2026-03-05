#!/usr/bin/env bash
# cmail Stop hook — when Claude finishes responding, check if new messages arrived
# Exit code 2 = force Claude to continue (so it can handle the new messages)
set -euo pipefail

INBOX_DIR="$HOME/.cmail/inbox"
UNREAD_MARKER="$HOME/.cmail/.has_unread"
LAST_CHECK_FILE="$HOME/.cmail/.last_stop_check"

# Fast path: no unread marker
if [[ ! -f "$UNREAD_MARKER" ]]; then
  exit 0
fi

# Debounce: don't force-continue more than once per 60 seconds
# This prevents infinite loops if Claude can't/won't handle the messages
if [[ -f "$LAST_CHECK_FILE" ]]; then
  last_check=$(cat "$LAST_CHECK_FILE" 2>/dev/null || echo 0)
  now=$(date +%s)
  elapsed=$(( now - last_check ))
  if (( elapsed < 60 )); then
    exit 0
  fi
fi

count=$(ls -1 "$INBOX_DIR"/*.json 2>/dev/null | wc -l | tr -d ' ') || count=0
if (( count == 0 )); then
  exit 0
fi

# Record this check to prevent rapid re-triggering
date +%s > "$LAST_CHECK_FILE"

# Build summary
summary=""
for file in $(ls -1t "$INBOX_DIR"/*.json 2>/dev/null | head -3); do
  if command -v jq &>/dev/null; then
    from=$(jq -r '.from // "unknown"' "$file")
    subject=$(jq -r '.subject // ""' "$file")
  else
    from=$(CMAIL_FILE="$file" python3 -c "import json,os; print(json.load(open(os.environ['CMAIL_FILE'])).get('from','unknown'))" 2>/dev/null || echo "unknown")
    subject=$(CMAIL_FILE="$file" python3 -c "import json,os; print(json.load(open(os.environ['CMAIL_FILE'])).get('subject',''))" 2>/dev/null || echo "")
  fi
  entry="- from ${from}"
  [[ -n "$subject" && "$subject" != "null" ]] && entry+=" — ${subject}"
  summary+="${entry}\n"
done

context="New cmail arrived while you were working! You have ${count} message(s). Check them with \`cmail inbox show\` and read/reply as needed.\n\n${summary}"

if command -v jq &>/dev/null; then
  jq -n --arg ctx "$context" '{"additionalContext": $ctx}'
else
  echo "$context" | python3 -c "import json,sys; print(json.dumps({'additionalContext': sys.stdin.read()}))"
fi

# Exit code 2 tells Claude Code to continue instead of stopping
exit 2
