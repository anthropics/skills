#!/usr/bin/env bash
set -euo pipefail

PRESET="${1:-full}"
THEME="${2:-aurora}"
ICON_STYLE="${3:-classic}"
TARGET_PATH="${4:-${CC_STATUSLINE_CLAUDE_DIR:-$HOME/.claude}/statusline.sh}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
case "$(uname -s 2>/dev/null)" in
    Darwin*) INSTALLER="$SCRIPT_DIR/install_statusline_macos.sh" ;;
    CYGWIN*|MINGW*|MSYS*) INSTALLER="$SCRIPT_DIR/install_statusline_windows.sh" ;;
    *) INSTALLER="$SCRIPT_DIR/install_statusline_linux.sh" ;;
esac

exec bash "$INSTALLER" "$PRESET" "$THEME" "$ICON_STYLE" "$TARGET_PATH"
