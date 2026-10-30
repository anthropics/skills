#!/bin/bash
# Smart email poller with intelligent session routing.
# Polls POP3 every 3 min. When new email arrives, classifies intent:
#   "continue" → claude --resume (same session, preserves context)
#   "new"      → claude -p (fresh session, standalone task)
# Auto-expires after 24 hours.

QUEUE_FILE="${EMAIL_QUEUE_FILE:-/tmp/email-pending-queue.txt}"
LOCK_FILE="/tmp/email-poll.lock"
CLAUDE_LOCK="/tmp/email-claude.lock"
SESSION_FILE="/tmp/email-claude-session.txt"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BRIDGE="$SCRIPT_DIR/email-bridge.py"
DECIDE="$SCRIPT_DIR/email-decision.py"
PROJECT_DIR="${EMAIL_PROJECT_DIR:-$SCRIPT_DIR}"
SYS_SENDERS="service.netease.com|club@service.netease.com|safe@service.netease.com"

# Read receiver from config
RECEIVER=$(python3 -c "import json; print(json.load(open('$SCRIPT_DIR/email-config.json'))['receiver'])" 2>/dev/null || echo "")

PROMPT_CONTINUE="You are continuing a previous conversation via email.
Process the email content below and reply:
1. Read the email body as a command/instruction
2. Execute it, maintaining context from prior conversation
3. Reply via: python3 $BRIDGE send \"Re: <subject>\" \"<result>\"
Do not ask for confirmation. Work efficiently."

PROMPT_NEW="Process this email as a new standalone task:
1. Read the email body as a command/instruction
2. Execute it fully
3. Reply via: python3 $BRIDGE send \"Re: <subject>\" \"<result>\"
Do not ask for confirmation. Work efficiently."

exec 200>"$LOCK_FILE"
flock -n 200 || exit 0

END_TIME=$(($(date +%s) + 86400))

while [ $(date +%s) -lt $END_TIME ]; do
    OUTPUT=$(cd "$PROJECT_DIR" && python3 "$BRIDGE" check 3 2>/dev/null)
    if echo "$OUTPUT" | grep -q "^New:"; then
        HAS_USER=$(echo "$OUTPUT" | grep -vE "$SYS_SENDERS" | grep "$RECEIVER")
        if [ -n "$HAS_USER" ]; then
            # Extract email body for classification
            BODY=$(echo "$OUTPUT" | sed -n '/^Body: /,/^---END---/p' | sed '1s/^Body: //' | head -n -1)
            SUBJECT=$(echo "$OUTPUT" | grep "^Subject:" | head -1)

            # Classify intent
            MODE="new"
            # Check subject for Re:
            if echo "$SUBJECT" | grep -qi "Re:"; then
                MODE="continue"
            fi
            # Run keyword classifier
            DECISION=$(echo "$BODY" | python3 "$DECIDE" 2>/dev/null)
            if [ "$DECISION" = "continue" ]; then
                MODE="continue"
            fi

            # Write to queue as backup
            {
                echo "=== $(date '+%Y-%m-%d %H:%M:%S') [mode=$MODE] ==="
                echo "$OUTPUT"
            } >> "$QUEUE_FILE"

            # Process with appropriate session mode
            (
                exec 201>"$CLAUDE_LOCK"
                if flock -n 201; then
                    cd "$PROJECT_DIR"

                    if [ "$MODE" = "continue" ] && [ -f "$SESSION_FILE" ]; then
                        RESUME_FLAG="--resume $(cat "$SESSION_FILE")"
                        PROMPT="$PROMPT_CONTINUE"
                        echo "[email-poll] Continue session $(cat "$SESSION_FILE")"
                    else
                        RESUME_FLAG=""
                        PROMPT="$PROMPT_NEW"
                        echo "[email-poll] New session"
                    fi

                    RESULT=$(claude -p "$PROMPT

Email content:
$OUTPUT" \
                        --max-turns 8 \
                        --dangerously-skip-permissions \
                        --output-format json \
                        $RESUME_FLAG \
                        2>&1)

                    # Save session ID for future continuation
                    echo "$RESULT" | python3 -c "
import sys, json
for line in sys.stdin:
    line = line.strip()
    if line.startswith('{'):
        d = json.loads(line)
        sid = d.get('session_id','')
        if sid:
            open('$SESSION_FILE','w').write(sid)
            print(f'Saved session: {sid}')
        break
" 2>/dev/null

                    echo "$RESULT" > /tmp/email-claude-output.json
                fi
            ) &
        fi
    fi
    sleep 180
done

rm -f "$LOCK_FILE"
