#!/bin/bash
# Buildr Permission Hook - PermissionRequest hook for CC <> Telegram bridge
#
# Forwards permission requests to Telegram via outbox file.
# Polls for user response (YES / NO / custom message).
# NO TIMEOUT - waits forever until user responds.

BUILDR_HOME="${BUILDR_HOME:-$HOME/.buildr}"
OUTBOX="$BUILDR_HOME/outbox.jsonl"
RESPONSE_FILE="$BUILDR_HOME/perm-response"
REQID_FILE="$BUILDR_HOME/perm-reqid"
HEARTBEAT="$BUILDR_HOME/heartbeat"

# Read permission request from stdin
INPUT=$(cat)

# Parse tool info and build message
MSG=$(echo "$INPUT" | python3 -c "
import json, sys
try:
    d = json.load(sys.stdin)
    tool = d.get('tool_name', 'unknown')
    ti = d.get('tool_input', {})
    cmd = ti.get('command', '')
    desc = ti.get('description', '')
    fp = ti.get('file_path', '')
    parts = []
    if cmd: parts.append('Cmd: ' + cmd[:300])
    if desc: parts.append('Desc: ' + desc[:150])
    if fp: parts.append('File: ' + fp)
    if not parts: parts.append(json.dumps(ti)[:300])
    detail = chr(10).join(parts)
    print(f'PERMISSION REQUEST\n\nTool: {tool}\n{detail}\n\nReply YES or NO (waiting for your response)')
except:
    print('PERMISSION REQUEST\n\nReply YES or NO')
" 2>/dev/null)

# Fallback if parsing failed
if [ -z "$MSG" ]; then
  MSG="PERMISSION REQUEST\n\nReply YES or NO"
fi

# Clear previous state
rm -f "$RESPONSE_FILE" "$REQID_FILE"

# Unique request ID
REQ_ID="perm_$(date +%s%3N)"
echo "$REQ_ID" > "$REQID_FILE"

# Send to TG via outbox (relay delivers within 2s)
# Use base64 to safely pass message (avoids quote/escape issues)
MSG_B64=$(echo "$MSG" | base64 -w0)
python3 -c "
import json, os, base64
msg = base64.b64decode('$MSG_B64').decode('utf-8').strip()
outbox = os.environ.get('BUILDR_HOME', os.path.expanduser('~/.buildr')) + '/outbox.jsonl'
with open(outbox, 'a') as f:
    f.write(json.dumps({'text': msg}) + '\n')
" 2>/dev/null

# Fallback if outbox write failed
if [ $? -ne 0 ]; then
  python3 << 'PYEOF'
import json, os
outbox = os.environ.get('BUILDR_HOME', os.path.expanduser('~/.buildr')) + '/outbox.jsonl'
with open(outbox, 'a') as f:
    f.write(json.dumps({"text": "PERMISSION REQUEST - Reply YES or NO"}) + "\n")
PYEOF
fi

# Poll for response (NO TIMEOUT - waits forever)
while true; do
  # Keep heartbeat alive while waiting
  echo "$(date +%s%3N)" > "$HEARTBEAT" 2>/dev/null

  if [ -f "$RESPONSE_FILE" ]; then
    RESP_REQID=$(head -1 "$RESPONSE_FILE")
    RESP_ANSWER=$(tail -1 "$RESPONSE_FILE")

    if [ "$RESP_REQID" = "$REQ_ID" ]; then
      rm -f "$RESPONSE_FILE" "$REQID_FILE"
      RESP_LOWER=$(echo "$RESP_ANSWER" | tr '[:upper:]' '[:lower:]')

      if [ "$RESP_LOWER" = "yes" ] || [ "$RESP_LOWER" = "y" ]; then
        echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"allow"}}}'
        exit 0
      elif [ "$RESP_LOWER" = "no" ] || [ "$RESP_LOWER" = "n" ]; then
        echo '{"hookSpecificOutput":{"hookEventName":"PermissionRequest","decision":{"behavior":"deny","message":"Denied via Telegram"}}}'
        exit 0
      else
        # Custom response - deny but include message so CC sees it
        ESCAPED=$(echo "$RESP_ANSWER" | python3 -c "import json,sys; print(json.dumps(sys.stdin.read().strip()))" 2>/dev/null | sed 's/^"//;s/"$//')
        echo "{\"hookSpecificOutput\":{\"hookEventName\":\"PermissionRequest\",\"decision\":{\"behavior\":\"deny\",\"message\":\"User message from Telegram: $ESCAPED\"}}}"
        exit 0
      fi
    fi
  fi
  sleep 1
done
