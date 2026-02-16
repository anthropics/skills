#!/usr/bin/env bash
# cmail-agent — auto-respond to incoming cmail using claude --print
# Triggered by the watcher when new messages arrive.
# Modeled after signal-bridge's approach: non-interactive subprocess with session persistence.
set -euo pipefail

COMMS_DIR="$HOME/.cmail"
INBOX_DIR="$COMMS_DIR/inbox"
AGENT_STATE="$COMMS_DIR/.agent"
SESSION_FILE="$AGENT_STATE/session_id"
LOCK_FILE="$AGENT_STATE/.lock"
LOG_FILE="$AGENT_STATE/agent.log"
# Find claude binary
find_claude() {
  if [[ -n "${CMAIL_CLAUDE_PATH:-}" ]] && [[ -x "$CMAIL_CLAUDE_PATH" ]]; then
    echo "$CMAIL_CLAUDE_PATH"
    return
  fi
  for candidate in \
    "$(command -v claude 2>/dev/null)" \
    "$HOME/.local/bin/claude" \
    "$HOME/.claude/local/claude" \
    "/usr/local/bin/claude" \
    ; do
    if [[ -n "$candidate" ]] && [[ -x "$candidate" ]]; then
      echo "$candidate"
      return
    fi
  done
  echo "claude"  # fallback, will fail with a clear error
}

CLAUDE_PATH="$(find_claude)"
CLAUDE_TIMEOUT="${CMAIL_AGENT_TIMEOUT:-120}"
CMAIL_SCRIPT="$(cd "$(dirname "$0")" && pwd)/cmail.sh"

mkdir -p "$AGENT_STATE"

log() {
  echo "[$(date -u +%Y-%m-%dT%H:%M:%SZ)] $*" >> "$LOG_FILE"
}

# --- Lock to prevent concurrent invocations ---
acquire_lock() {
  if [[ -f "$LOCK_FILE" ]]; then
    local lock_pid
    lock_pid="$(cat "$LOCK_FILE" 2>/dev/null || echo "")"
    if [[ -n "$lock_pid" ]] && kill -0 "$lock_pid" 2>/dev/null; then
      log "Agent already running (PID: $lock_pid), skipping."
      return 1
    fi
    # Stale lock
    rm -f "$LOCK_FILE"
  fi
  echo $$ > "$LOCK_FILE"
  return 0
}

release_lock() {
  rm -f "$LOCK_FILE"
}

trap release_lock EXIT

# --- Session management ---
get_session_id() {
  if [[ -f "$SESSION_FILE" ]]; then
    cat "$SESSION_FILE"
  fi
}

save_session_id() {
  echo "$1" > "$SESSION_FILE"
}

# --- Build inbox summary for Claude ---
build_inbox_prompt() {
  local files
  files="$(ls -1t "$INBOX_DIR"/*.json 2>/dev/null)" || true
  if [[ -z "$files" ]]; then
    echo ""
    return
  fi

  local count
  count="$(echo "$files" | wc -l | tr -d ' ')"
  local prompt="You have ${count} cmail message(s) in your inbox. Here are the details:\n\n"

  while IFS= read -r file; do
    [[ -f "$file" ]] || continue
    local id from to timestamp subject body
    if command -v jq &>/dev/null; then
      id="$(jq -r '.id' "$file")"
      from="$(jq -r '.from' "$file")"
      to="$(jq -r '.to' "$file")"
      timestamp="$(jq -r '.timestamp' "$file")"
      subject="$(jq -r '.subject // ""' "$file")"
      body="$(jq -r '.body' "$file")"
    else
      id="$(CMAIL_FILE="$file" python3 -c "import json,os; print(json.load(open(os.environ['CMAIL_FILE']))['id'])")"
      from="$(CMAIL_FILE="$file" python3 -c "import json,os; print(json.load(open(os.environ['CMAIL_FILE']))['from'])")"
      to="$(CMAIL_FILE="$file" python3 -c "import json,os; print(json.load(open(os.environ['CMAIL_FILE']))['to'])")"
      timestamp="$(CMAIL_FILE="$file" python3 -c "import json,os; print(json.load(open(os.environ['CMAIL_FILE']))['timestamp'])")"
      subject="$(CMAIL_FILE="$file" python3 -c "import json,os; print(json.load(open(os.environ['CMAIL_FILE'])).get('subject',''))")"
      body="$(CMAIL_FILE="$file" python3 -c "import json,os; print(json.load(open(os.environ['CMAIL_FILE']))['body'])")"
    fi
    local short_id="${id:0:8}"
    prompt+="--- Message [${short_id}] ---\n"
    prompt+="From: ${from}\n"
    prompt+="Date: ${timestamp}\n"
    [[ -n "$subject" && "$subject" != "null" ]] && prompt+="Subject: ${subject}\n"
    prompt+="Body: ${body}\n\n"
  done <<< "$files"

  prompt+="Read each message and reply to any that need a response using: cmail reply <id> \"your reply\"\n"
  prompt+="After replying, delete the message from inbox: rm ~/.cmail/inbox/<filename>\n"
  prompt+="If a message doesn't need a reply, just delete it from inbox."

  printf '%b' "$prompt"
}

# --- System prompt ---
SYSTEM_PROMPT='You are a cmail auto-responder running on '"$(hostname)"'. You receive messages from other machines and humans via cmail (file-based messaging over SSH).

Your job:
1. Read the incoming messages shown to you
2. Reply to messages that need a response using: cmail reply <message-id> "your reply"
3. Clean up handled messages by removing them from ~/.cmail/inbox/
4. Be helpful, concise, and actionable in your replies

You can read files and search the codebase to answer questions. You can only run cmail commands and manage inbox files.

Available commands:
- cmail reply <id> "message" — reply to a message (preserves threading)
- cmail send <host> "message" — send a new message
- cmail inbox show — list all inbox messages
- rm -f ~/.cmail/inbox/<filename>.json — remove a handled message

Keep replies concise. You are responding via cmail, not a terminal — short, actionable messages work best.'

# --- Main ---

# Ensure cmail and claude are findable by subprocesses
export PATH="$HOME/.local/bin:/usr/local/bin:$PATH"

main() {
  if ! acquire_lock; then
    exit 0
  fi

  local inbox_prompt
  inbox_prompt="$(build_inbox_prompt)"
  if [[ -z "$inbox_prompt" ]]; then
    log "No messages in inbox, nothing to do."
    exit 0
  fi

  log "Processing inbox ($(ls -1 "$INBOX_DIR"/*.json 2>/dev/null | wc -l | tr -d ' ') messages)"

  local session_id
  session_id="$(get_session_id)"

  # Build claude command
  local cmd=(
    "$CLAUDE_PATH" "--print"
    "--model" "${CMAIL_AGENT_MODEL:-claude-sonnet-4-5-20250929}"
    "--output-format" "json"
    "--system-prompt" "$SYSTEM_PROMPT"
    "--allowedTools" "Bash(cmail *)" "Bash(rm -f ~/.cmail/inbox/*.json)" "Bash(ls ~/.cmail/inbox/*)" "Read" "Grep" "Glob"
    "-p" "$inbox_prompt"
  )

  if [[ -n "$session_id" ]]; then
    cmd+=("--resume" "$session_id")
  fi

  log "Running: claude --print (session: ${session_id:-new})"

  local output
  if output="$(timeout "$CLAUDE_TIMEOUT" "${cmd[@]}" 2>&1)"; then
    # Parse JSON output for session_id and result
    if command -v jq &>/dev/null; then
      local new_session
      new_session="$(echo "$output" | jq -r '.session_id // empty' 2>/dev/null)" || true
      local result
      result="$(echo "$output" | jq -r '.result // empty' 2>/dev/null)" || true

      if [[ -n "$new_session" ]]; then
        save_session_id "$new_session"
        log "Session: $new_session"
      fi

      if [[ -n "$result" ]]; then
        log "Claude responded (${#result} chars)"
      else
        log "Claude responded (raw output, ${#output} chars)"
      fi
    else
      log "Claude responded (${#output} chars, no jq to parse session)"
    fi
  else
    local exit_code=$?
    if [[ $exit_code -eq 124 ]]; then
      log "ERROR: Claude timed out after ${CLAUDE_TIMEOUT}s"
    else
      log "ERROR: Claude exited with code $exit_code"
      log "Output: ${output:0:500}"
    fi
  fi

  # Clear unread marker since we've processed everything
  rm -f "$COMMS_DIR/.has_unread"

  log "Done."
}

main "$@"
