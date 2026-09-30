#!/usr/bin/env bash
set -euo pipefail

TARGET_PATH="${1:-$HOME/.claude/statusline.custom.sh}"
SCRIPT_ARGC=$#
SCRIPT_ARGS=("$@")

value_or_default() {
    local index=$1
    local default_value=$2
    local array_index=$((index - 1))
    if [ "$SCRIPT_ARGC" -ge "$index" ]; then
        printf '%s' "${SCRIPT_ARGS[$array_index]}"
    else
        printf '%s' "$default_value"
    fi
}

normalize_line() {
    case "$1" in
        -|none|empty|null)
            printf ''
            ;;
        *)
            printf '%s' "$1"
            ;;
    esac
}

preview_line() {
    if [ -n "$1" ]; then
        printf '%s' "$1"
    else
        printf '(empty)'
    fi
}

LINE_1=$(normalize_line "$(value_or_default 2 "model,modes,version,active")")
LINE_2=$(normalize_line "$(value_or_default 3 "context,tools,cwd,git")")
LINE_3=$(normalize_line "$(value_or_default 4 "ctx_tokens,sum_tokens,duration,cost")")
THEME=$(value_or_default 5 "aurora")
ICON_STYLE=$(value_or_default 6 "classic")

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUNTIME_SCRIPT="$SCRIPT_DIR/statusline.sh"
TARGET_DIR="$(dirname "$TARGET_PATH")"

mkdir -p "$TARGET_DIR"
cp "$RUNTIME_SCRIPT" "$TARGET_PATH"
chmod +x "$TARGET_PATH"

cat <<EOF >> "$TARGET_PATH"

# ---- cc-statusline custom layout override ----
export CC_STATUSLINE_CUSTOM_LAYOUT_MODE=true
export CC_STATUSLINE_CUSTOM_THEME="${THEME}"
export CC_STATUSLINE_CUSTOM_ICON_STYLE="${ICON_STYLE}"
export CC_STATUSLINE_CUSTOM_LINE_1="${LINE_1}"
export CC_STATUSLINE_CUSTOM_LINE_2="${LINE_2}"
export CC_STATUSLINE_CUSTOM_LINE_3="${LINE_3}"
EOF

printf 'Generated custom statusline at %s\n' "$TARGET_PATH"
printf 'Line 1: %s\n' "$(preview_line "$LINE_1")"
printf 'Line 2: %s\n' "$(preview_line "$LINE_2")"
printf 'Line 3: %s\n' "$(preview_line "$LINE_3")"
printf 'Theme: %s\n' "$THEME"
printf 'Icon style: %s\n' "$ICON_STYLE"
