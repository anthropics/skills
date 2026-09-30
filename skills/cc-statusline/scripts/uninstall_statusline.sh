#!/usr/bin/env bash
set -euo pipefail

CLAUDE_DIR="${CC_STATUSLINE_CLAUDE_DIR:-$HOME/.claude}"
SETTINGS_FILE="${CC_STATUSLINE_SETTINGS_FILE:-$CLAUDE_DIR/settings.json}"
STATE_FILE="${CC_STATUSLINE_STATE_FILE:-$CLAUDE_DIR/cc-statusline-state.json}"

log() {
    printf '[cc-statusline][uninstall] %s\n' "$1"
}

warn() {
    printf '[cc-statusline][uninstall][warn] %s\n' "$1"
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

settings_has_statusline_jq() {
    local jq_bin=$1
    [ -f "$SETTINGS_FILE" ] || return 1
    "$jq_bin" -e '.statusLine != null' "$SETTINGS_FILE" >/dev/null 2>&1
}

remove_with_jq() {
    local jq_bin=$1
    local tmp_file
    tmp_file="$SETTINGS_FILE.tmp.$$"
    "$jq_bin" -e . "$SETTINGS_FILE" >/dev/null 2>&1 || return 1
    "$jq_bin" 'del(.statusLine)' "$SETTINGS_FILE" > "$tmp_file"
    mv "$tmp_file" "$SETTINGS_FILE"
}

remove_with_python() {
    local py
    py=$(choose_python) || return 1
    "$py" - "$SETTINGS_FILE" <<'PY'
import json
import sys

settings_file = sys.argv[1]
with open(settings_file, 'r', encoding='utf-8') as f:
    data = json.load(f)

data.pop('statusLine', None)

with open(settings_file, 'w', encoding='utf-8') as f:
    json.dump(data, f, ensure_ascii=False, indent=2)
    f.write('\n')
PY
}

print_restore_hint() {
    if [ -f "$STATE_FILE" ]; then
        log "Previous statusLine snapshot remains available at $STATE_FILE"
        local jq_bin
        if jq_bin=$(choose_jq_bin); then
            local previous
            previous=$("$jq_bin" -c '.previousStatusLine // null' "$STATE_FILE" 2>/dev/null || printf 'null')
            log "Saved previous statusLine value: $previous"
        fi
    else
        warn 'No saved previous statusLine snapshot was found.'
    fi
}

main() {
    if [ ! -f "$SETTINGS_FILE" ]; then
        log "No settings.json found at $SETTINGS_FILE. Nothing to remove."
        exit 0
    fi

    local jq_bin
    if jq_bin=$(choose_jq_bin); then
        if ! settings_has_statusline_jq "$jq_bin"; then
            log 'settings.json does not contain a statusLine entry. Nothing to remove.'
            exit 0
        fi
        if remove_with_jq "$jq_bin"; then
            log 'Removed only the statusLine field from settings.json.'
            print_restore_hint
            log 'Generated script files were kept on disk.'
            exit 0
        fi
        warn 'jq-based uninstall failed. Attempting Python fallback.'
    fi

    if remove_with_python; then
        log 'Removed only the statusLine field from settings.json using Python fallback.'
        print_restore_hint
        log 'Generated script files were kept on disk.'
        exit 0
    fi

    warn 'Automatic uninstall failed.'
    warn 'Manual fallback: remove only the statusLine field from ~/.claude/settings.json and keep script files as desired.'
    exit 1
}

main "$@"
