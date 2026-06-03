#!/usr/bin/env bash
# voice-prompt setup: cross-platform installer.
set -euo pipefail

PY=${PYTHON:-python3}
OS="$(uname -s)"

echo "[voice-prompt] Detected: $OS"

if ! command -v "$PY" >/dev/null 2>&1; then
  echo "ERROR: python3 not found on PATH." >&2
  exit 1
fi

case "$OS" in
  Darwin)
    # PortAudio for sounddevice; AppleScript ships with macOS.
    if command -v brew >/dev/null 2>&1; then
      brew list --versions portaudio >/dev/null 2>&1 || brew install portaudio
    else
      echo "WARN: Homebrew not found — sounddevice may fail. Install PortAudio manually." >&2
    fi
    EXTRA=()
    ;;
  Linux)
    # xdotool to send keystrokes; portaudio19-dev for sounddevice build.
    if ! command -v xdotool >/dev/null 2>&1; then
      echo "[voice-prompt] xdotool missing. On Debian/Ubuntu:  sudo apt install xdotool portaudio19-dev"
      echo "[voice-prompt] On Fedora:                          sudo dnf install xdotool portaudio-devel"
      echo "[voice-prompt] On Arch:                            sudo pacman -S xdotool portaudio"
    fi
    EXTRA=()
    ;;
  MINGW*|MSYS*|CYGWIN*|Windows_NT)
    # Windows uses pyautogui as the typing backend.
    EXTRA=(pyautogui)
    ;;
  *)
    echo "WARN: unknown OS '$OS' — proceeding with Python deps only." >&2
    EXTRA=()
    ;;
esac

"$PY" -m pip install --user --upgrade pip
"$PY" -m pip install --user \
  sounddevice \
  numpy \
  faster-whisper \
  "${EXTRA[@]}"

echo
echo "[voice-prompt] Done."
echo
echo "Permissions reminder:"
case "$OS" in
  Darwin)
    echo "  System Settings → Privacy & Security → Microphone   → enable your terminal"
    echo "  System Settings → Privacy & Security → Accessibility → enable your terminal"
    ;;
  Linux)
    echo "  Make sure your user is in the 'audio' group (sudo usermod -aG audio \$USER)"
    echo "  X11 is required for xdotool (Wayland users: try 'ydotool' as a drop-in replacement)"
    ;;
esac
echo
echo "Start the listener:"
echo "  python3 ~/.claude/skills/voice-prompt/voice_prompt.py"
