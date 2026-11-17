#!/usr/bin/env bash
set -euo pipefail

PLATFORM_NAME="macOS"
EXPECTED_OS="macos"
PRESET="${1:-full}"
THEME="${2:-aurora}"
ICON_STYLE="${3:-classic}"
TARGET_PATH="${4:-$HOME/.claude/statusline.sh}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_SCRIPT="$SCRIPT_DIR/statusline.sh"
INSTALL_JQ_SCRIPT="$SCRIPT_DIR/install_jq.sh"
CLAUDE_DIR="${CC_STATUSLINE_CLAUDE_DIR:-$HOME/.claude}"
SETTINGS_FILE="${CC_STATUSLINE_SETTINGS_FILE:-$CLAUDE_DIR/settings.json}"
STATE_FILE="${CC_STATUSLINE_STATE_FILE:-$CLAUDE_DIR/cc-statusline-state.json}"
TARGET_DIR="$(dirname "$TARGET_PATH")"
BACKUP_PATH="$TARGET_DIR/$(basename "$TARGET_PATH").bak"
STATUSLINE_COMMAND="bash \"$TARGET_PATH\" \"$PRESET\" \"$THEME\" \"$ICON_STYLE\""
JQ_BIN=""

usage() {
    printf 'Usage: bash scripts/install_statusline_macos.sh [preset] [theme] [icon_style] [target_path]\n'
    printf 'Example: bash scripts/install_statusline_macos.sh full aurora classic "$HOME/.claude/statusline.sh"\n'
}

log() {
    printf '[cc-statusline][%s] %s\n' "$PLATFORM_NAME" "$1"
}

warn() {
    printf '[cc-statusline][%s][warn] %s\n' "$PLATFORM_NAME" "$1"
}

fail_manual() {
    printf '[cc-statusline][%s][error] %s\n' "$PLATFORM_NAME" "$1" >&2
    printf 'Manual fallback:\n' >&2
    printf '1. Copy %s to %s\n' "$SOURCE_SCRIPT" "$TARGET_PATH" >&2
    printf '2. Ensure jq is available at ~/.claude/jq.exe, ~/.claude/jq, or in PATH\n' >&2
    printf '3. Update only the statusLine field in %s\n' "$SETTINGS_FILE" >&2
    printf '4. Use this command value: %s\n' "$STATUSLINE_COMMAND" >&2
    exit 1
}

validate_choice() {
    case "$PRESET" in
        full|standard|minimal|developer) ;;
        *) fail_manual "Unsupported preset: $PRESET" ;;
    esac
    case "$THEME" in
        aurora|sunset|ocean|mono) ;;
        *) fail_manual "Unsupported theme: $THEME" ;;
    esac
    case "$ICON_STYLE" in
        classic|minimal|developer) ;;
        *) fail_manual "Unsupported icon style: $ICON_STYLE" ;;
    esac
}

detect_os() {
    case "$(uname -s 2>/dev/null)" in
        Linux*) printf 'linux' ;;
        Darwin*) printf 'macos' ;;
        CYGWIN*|MINGW*|MSYS*) printf 'windows' ;;
        *)
            if [ -n "${WINDIR:-}" ]; then
                printf 'windows'
            else
                printf 'unknown'
            fi
            ;;
    esac
}

warn_if_unexpected_os() {
    local detected
    detected=$(detect_os)
    if [ "$detected" != "$EXPECTED_OS" ]; then
        warn "This installer targets $PLATFORM_NAME, but detected $detected. Continuing anyway."
    fi
}

ensure_paths() {
    [ -f "$SOURCE_SCRIPT" ] || fail_manual "Runtime script not found: $SOURCE_SCRIPT"
    mkdir -p "$CLAUDE_DIR" "$TARGET_DIR"
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

ensure_jq() {
    if JQ_BIN=$(choose_jq_bin); then
        log "Using jq at $JQ_BIN"
        return 0
    fi
    warn "jq not found. Attempting automatic install."
    if [ -f "$INSTALL_JQ_SCRIPT" ]; then
        bash "$INSTALL_JQ_SCRIPT" || true
    fi
    if JQ_BIN=$(choose_jq_bin); then
        log "jq installed successfully at $JQ_BIN"
        return 0
    fi
    fail_manual 'jq is required for the statusline runtime and could not be installed automatically.'
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

settings_valid_json() {
    [ ! -f "$SETTINGS_FILE" ] && return 0
    "$JQ_BIN" -e . "$SETTINGS_FILE" >/dev/null 2>&1
}

read_current_statusline_json() {
    [ -f "$SETTINGS_FILE" ] || return 0
    "$JQ_BIN" -c '.statusLine // empty' "$SETTINGS_FILE" 2>/dev/null || true
}

read_current_statusline_command() {
    [ -f "$SETTINGS_FILE" ] || return 0
    "$JQ_BIN" -r '.statusLine.command // empty' "$SETTINGS_FILE" 2>/dev/null || true
}

is_existing_script_managed() {
    [ -f "$TARGET_PATH" ] || return 1
    grep -q 'cc-statusline runtime script' "$TARGET_PATH" 2>/dev/null
}

confirm_foreign_statusline() {
    [ -f "$SETTINGS_FILE" ] || return 0
    settings_valid_json || fail_manual "settings.json is not valid JSON and cannot be updated safely."

    local current_json current_command
    current_json=$(read_current_statusline_json)
    [ -z "$current_json" ] && return 0

    current_command=$(read_current_statusline_command)
    if [[ "$current_command" == *"$(basename "$TARGET_PATH")"* ]] && is_existing_script_managed; then
        log 'Existing cc-statusline-managed configuration detected. Updating in place.'
        return 0
    fi

    printf 'Existing statusLine configuration detected:\n%s\n' "$current_json"
    read -r -p 'Replace it with cc-statusline? [y/N] ' reply
    case "$reply" in
        y|Y|yes|YES) ;;
        *)
            log 'Installation cancelled by user.'
            exit 0
            ;;
    esac
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
        --arg platform "$EXPECTED_OS" \
        --arg preset "$PRESET" \
        --arg theme "$THEME" \
        --arg iconStyle "$ICON_STYLE" \
        --arg targetPath "$TARGET_PATH" \
        --arg backupPath "$BACKUP_PATH" \
        --arg command "$STATUSLINE_COMMAND" \
        --arg sourceScript "$SOURCE_SCRIPT" \
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

backup_target() {
    if [ -f "$TARGET_PATH" ]; then
        cp "$TARGET_PATH" "$BACKUP_PATH"
        log "Backed up existing script to $BACKUP_PATH"
    fi
}

install_runtime_script() {
    cp "$SOURCE_SCRIPT" "$TARGET_PATH"
    chmod +x "$TARGET_PATH"
    log "Installed runtime script to $TARGET_PATH"
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
        log "Updated $SETTINGS_FILE"
        return 0
    fi
    warn 'jq-based settings update failed. Attempting Python fallback.'
    if update_settings_with_python; then
        log "Updated $SETTINGS_FILE using Python fallback"
        return 0
    fi
    fail_manual 'Failed to update settings.json automatically.'
}

print_summary() {
    printf '\n'
    printf 'Installed cc-statusline for %s\n' "$PLATFORM_NAME"
    printf -- '- preset: %s\n' "$PRESET"
    printf -- '- theme: %s\n' "$THEME"
    printf -- '- icon style: %s\n' "$ICON_STYLE"
    printf -- '- target: %s\n' "$TARGET_PATH"
    printf -- '- command: %s\n' "$STATUSLINE_COMMAND"
    printf -- '- previous statusLine snapshot: %s\n' "$STATE_FILE"
    if [ -f "$BACKUP_PATH" ]; then
        printf -- '- backup: %s\n' "$BACKUP_PATH"
    fi
}

main() {
    if [ "${1:-}" = '--help' ] || [ "${1:-}" = '-h' ]; then
        usage
        exit 0
    fi

    validate_choice
    warn_if_unexpected_os
    ensure_paths
    ensure_jq
    confirm_foreign_statusline
    save_previous_statusline_state
    backup_target
    install_runtime_script
    update_settings
    print_summary
}

main "$@"
