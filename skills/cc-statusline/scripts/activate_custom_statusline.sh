#!/usr/bin/env bash
set -euo pipefail

CLAUDE_DIR="${CC_STATUSLINE_CLAUDE_DIR:-$HOME/.claude}"
SETTINGS_FILE="${CC_STATUSLINE_SETTINGS_FILE:-$CLAUDE_DIR/settings.json}"
STATE_FILE="${CC_STATUSLINE_STATE_FILE:-$CLAUDE_DIR/cc-statusline-state.json}"
TARGET_PATH="${1:-$CLAUDE_DIR/statusline.custom.sh}"
PRESET_LABEL="custom"
THEME_LABEL="${2:-custom}"
ICON_STYLE_LABEL="${3:-custom}"
STATUSLINE_COMMAND="bash \"$TARGET_PATH\""
JQ_BIN=""

log() {
    printf '[cc-statusline][activate-custom] %s\n' "$1"
}

warn() {
    printf '[cc-statusline][activate-custom][warn] %s\n' "$1"
}

fail_manual() {
    printf '[cc-statusline][activate-custom][error] %s\n' "$1" >&2
    printf 'Manual fallback:\n' >&2
    printf '1. Confirm the custom script exists at %s\n' "$TARGET_PATH" >&2
    printf '2. Update only the statusLine field in %s\n' "$SETTINGS_FILE" >&2
    printf '3. Use this command value: %s\n' "$STATUSLINE_COMMAND" >&2
    exit 1
}

choose_jq_bin() {
    if [ -x "$HOME/.claude/jq.exe" ] && "$HOME/.claude/jq.exe" --version >/dev/null 2>&1; then
        printf '%s' "$HOME/.claude/jq.exe"
        return 0
    fi
    if [ -x "$HOME/.claude/jq" ] && "$HOME/.claude/jq" --version >/dev/null 2>&1; then
        printf '%s' "$HOME/.claude/jq"
        return 0
    fi
    if command -v jq >/dev/null 2>&1; then
        command -v jq
        return 0
    fi
    return 1
}

choose_python() {
    if command -v python3 >/dev/null 2>&1; then
        command -v python3
        return 0
    fi
    if command -v python >/dev/null 2>&1; then
        command -v python
        return 0
    fi
    return 1
}

ensure_inputs() {
    [ -f "$TARGET_PATH" ] || fail_manual "Custom statusline script not found: $TARGET_PATH"
    mkdir -p "$CLAUDE_DIR"
}

settings_valid_json() {
    [ ! -f "$SETTINGS_FILE" ] && return 0
    "$JQ_BIN" -e . "$SETTINGS_FILE" >/dev/null 2>&1
}

save_previous_statusline_state() {
    local previous_json timestamp
    previous_json='null'
    timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || date)

    if [ -f "$SETTINGS_FILE" ] && settings_valid_json; then
        previous_json=$("$JQ_BIN" -c '.statusLine // null' "$SETTINGS_FILE" 2>/dev/null || printf 'null')
    fi

    "$JQ_BIN" -n \
        --arg savedAt "$timestamp" \
        --arg platform "activation" \
        --arg preset "$PRESET_LABEL" \
        --arg theme "$THEME_LABEL" \
        --arg iconStyle "$ICON_STYLE_LABEL" \
        --arg targetPath "$TARGET_PATH" \
        --arg backupPath "" \
        --arg command "$STATUSLINE_COMMAND" \
        --arg sourceScript "$TARGET_PATH" \
        --argjson previousStatusLine "$previous_json" \
        '{
            tool: "cc-statusline",
            savedAt: $savedAt,
            platform: $platform,
            preset: $preset,
            theme: $theme,
            iconStyle: $iconStyle,
            targetPath: $targetPath,
            backupPath: $backupPath,
            command: $command,
            sourceScript: $sourceScript,
            previousStatusLine: $previousStatusLine
        }' > "$STATE_FILE"
}

update_settings_with_jq() {
    local tmp_file
    tmp_file="$SETTINGS_FILE.tmp.$$"

    if [ ! -f "$SETTINGS_FILE" ]; then
        "$JQ_BIN" -n --arg cmd "$STATUSLINE_COMMAND" '{statusLine:{type:"command",command:$cmd,padding:0}}' > "$SETTINGS_FILE"
        return 0
    fi

    settings_valid_json || return 1
    "$JQ_BIN" --arg cmd "$STATUSLINE_COMMAND" '.statusLine = {type:"command", command:$cmd, padding:0}' "$SETTINGS_FILE" > "$tmp_file"
    mv "$tmp_file" "$SETTINGS_FILE"
}

update_settings_with_python() {
    local py
    py=$(choose_python) || return 1

    "$py" - "$SETTINGS_FILE" "$STATUSLINE_COMMAND" <<'PY'
import json
import os
import sys

settings_file = sys.argv[1]
command = sys.argv[2]

data = {}
if os.path.exists(settings_file):
    with open(settings_file, 'r', encoding='utf-8') as f:
        data = json.load(f)

data['statusLine'] = {
    'type': 'command',
    'command': command,
    'padding': 0,
}

with open(settings_file, 'w', encoding='utf-8') as f:
    json.dump(data, f, ensure_ascii=False, indent=2)
    f.write('\n')
PY
}

update_settings() {
    if update_settings_with_jq; then
        return 0
    fi
    warn 'jq-based activation failed. Attempting Python fallback.'
    if update_settings_with_python; then
        return 0
    fi
    fail_manual 'Failed to activate custom statusline automatically.'
}

main() {
    ensure_inputs
    JQ_BIN=$(choose_jq_bin) || fail_manual 'jq is required to update settings.json.'
    save_previous_statusline_state
    update_settings
    log "Activated custom statusline: $TARGET_PATH"
    log "Saved previous statusLine snapshot to $STATE_FILE"
}

main "$@"
