#!/usr/bin/env bash
# log.sh - Audit logging utility for GOG skills

# This script provides a simple function to append audit log entries
# to ~/.gog-assistant/audit.log

# Usage:
#   source /path/to/log.sh
#   log_action "skill-name" "action-type" "status" "entity_id" '{"details":"json"}'

set -euo pipefail

# Default audit log location
AUDIT_DIR="${GOG_AUDIT_DIR:-$HOME/.gog-assistant}"
AUDIT_LOG="$AUDIT_DIR/audit.log"

# Ensure audit directory exists
ensure_audit_dir() {
  if [ ! -d "$AUDIT_DIR" ]; then
    mkdir -p "$AUDIT_DIR"
    chmod 700 "$AUDIT_DIR"
  fi
}

# Generate ISO8601 timestamp with UTC timezone
get_timestamp() {
  date -u +"%Y-%m-%dT%H:%M:%SZ"
}

# Escape JSON strings (basic implementation)
json_escape() {
  local input="$1"
  # Replace backslash, quote, newline, tab
  printf '%s' "$input" | \
    sed 's/\\/\\\\/g' | \
    sed 's/"/\\"/g' | \
    sed 's/\n/\\n/g' | \
    sed 's/\t/\\t/g'
}

# Log an action to the audit log
# Args:
#   $1 - skill name (required)
#   $2 - action type (required)
#   $3 - log_status: success, failure, pending (required)
#   $4 - entity_id (optional)
#   $5 - details JSON object (optional)
log_action() {
  local skill="${1:-}"
  local action="${2:-}"
  local log_status="${3:-}"
  local entity_id="${4:-}"
  local details="${5:-{}}"

  # Validate required parameters
  if [ -z "$skill" ] || [ -z "$action" ] || [ -z "$log_status" ]; then
    echo "ERROR: log_action requires skill, action, and log_status" >&2
    return 1
  fi

  # Validate log_status
  if [[ ! "$log_status" =~ ^(success|failure|pending)$ ]]; then
    echo "ERROR: log_status must be one of: success, failure, pending" >&2
    return 1
  fi

  # Ensure audit directory exists
  ensure_audit_dir

  # Get timestamp
  local timestamp
  timestamp=$(get_timestamp)

  # Build JSON entry
  local entry

  if [ -n "$entity_id" ]; then
    # Validate details is valid JSON
    if echo "$details" | jq empty 2>/dev/null; then
      entry=$(jq -n \
        --arg ts "$timestamp" \
        --arg sk "$skill" \
        --arg act "$action" \
        --arg st "$log_status" \
        --arg eid "$entity_id" \
        --argjson det "$details" \
        '{timestamp: $ts, skill: $sk, action: $act, status: $st, entity_id: $eid, details: $det}')
    else
      echo "ERROR: details is not valid JSON: $details" >&2
      return 1
    fi
  else
    # No entity_id
    if echo "$details" | jq empty 2>/dev/null; then
      entry=$(jq -n \
        --arg ts "$timestamp" \
        --arg sk "$skill" \
        --arg act "$action" \
        --arg st "$log_status" \
        --argjson det "$details" \
        '{timestamp: $ts, skill: $sk, action: $act, status: $st, details: $det}')
    else
      echo "ERROR: details is not valid JSON: $details" >&2
      return 1
    fi
  fi

  # Append to log file
  echo "$entry" >> "$AUDIT_LOG"

  # Ensure log file has restrictive permissions
  chmod 600 "$AUDIT_LOG"

  return 0
}

# Log a simple action without details
# Args:
#   $1 - skill name (required)
#   $2 - action type (required)
#   $3 - log_status (required)
#   $4 - entity_id (optional)
log_simple() {
  local skill="${1:-}"
  local action="${2:-}"
  local log_status="${3:-}"
  local entity_id="${4:-}"

  log_action "$skill" "$action" "$log_status" "$entity_id" "{}"
}

# Get the last N entries from the audit log
# Args:
#   $1 - number of entries (default: 10)
get_recent_logs() {
  local count="${1:-10}"

  if [ ! -f "$AUDIT_LOG" ]; then
    echo "No audit log found at: $AUDIT_LOG" >&2
    return 1
  fi

  tail -n "$count" "$AUDIT_LOG"
}

# Count actions by skill
# Args:
#   $1 - skill name
count_by_skill() {
  local skill="$1"

  if [ ! -f "$AUDIT_LOG" ]; then
    echo "0"
    return 0
  fi

  jq -r --arg sk "$skill" 'select(.skill == $sk)' "$AUDIT_LOG" | wc -l | tr -d ' '
}

# Count failed actions
count_failures() {
  if [ ! -f "$AUDIT_LOG" ]; then
    echo "0"
    return 0
  fi

  jq -r 'select(.status == "failure")' "$AUDIT_LOG" | wc -l | tr -d ' '
}

# Display help
show_log_help() {
  cat <<EOF
GOG Audit Logging Utility

This script provides functions for logging actions to the GOG audit log.

Functions:
  log_action <skill> <action> <log_status> [entity_id] [details_json]
    Log a complete action with optional details JSON

  log_simple <skill> <action> <log_status> [entity_id]
    Log a simple action without details

  get_recent_logs [count]
    Display the last N log entries (default: 10)

  count_by_skill <skill>
    Count total actions by a specific skill

  count_failures
    Count total failed actions

Log status values: success, failure, pending

Example usage:
  source log.sh
  log_action "gog-email-send" "email-send" "success" "msg_123" '{"to":["user@example.com"]}'
  log_simple "gog-tasks" "task-create" "success" "task_456"
  get_recent_logs 20

Environment variables:
  GOG_AUDIT_DIR - Override audit directory (default: ~/.gog-assistant)

Audit log location: $AUDIT_LOG
EOF
}

# If script is run directly (not sourced), show help
if [ "${BASH_SOURCE[0]:-}" = "${0}" ]; then
  show_log_help
fi
