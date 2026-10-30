#!/usr/bin/env bash
# Opens a new Terminal window running the voice-prompt listener so the user
# can keep focus on their Claude Code window.
set -euo pipefail

SCRIPT="$HOME/.claude/skills/voice-prompt/voice_prompt.py"

if [ ! -f "$SCRIPT" ]; then
  echo "ERROR: $SCRIPT not found." >&2
  exit 1
fi

# Open in a new Terminal.app window. If iTerm is preferred, the user can
# replace "Terminal" with "iTerm" below.
osascript <<EOF
tell application "Terminal"
  activate
  do script "echo '── voice-prompt listener (Cmd+W to stop) ──'; python3 $SCRIPT"
end tell
EOF

echo "[voice-prompt] Listener launched in a new Terminal window."
echo "[voice-prompt] Click back into your Claude Code window and start speaking."
