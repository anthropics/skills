#!/bin/bash
# Agent Notify - macOS Notification Script
# Plays system sound and shows notification center alert

TYPE="${1:-default}"
CONFIG_PATH="${2:-}"

# Default values
FLASH_COUNT=5
CUSTOM_SOUND=""
NOTIFICATION_TITLE="Agent Notify"

# Load config if provided
if [ -n "$CONFIG_PATH" ] && [ -f "$CONFIG_PATH" ]; then
    if command -v jq &>/dev/null; then
        FLASH_COUNT=$(jq -r '.taskbar.flashCount // 5' "$CONFIG_PATH" 2>/dev/null)
        CUSTOM_SOUND=$(jq -r ".sounds.${TYPE} // empty" "$CONFIG_PATH" 2>/dev/null)
    elif command -v python3 &>/dev/null; then
        FLASH_COUNT=$(python3 -c "import json; c=json.load(open('$CONFIG_PATH')); print(c.get('taskbar',{}).get('flashCount',5))" 2>/dev/null || echo 5)
        CUSTOM_SOUND=$(python3 -c "import json; c=json.load(open('$CONFIG_PATH')); print(c.get('sounds',{}).get('$TYPE',''))" 2>/dev/null)
    fi
fi

# Determine notification message
case "$TYPE" in
    confirm)
        MSG="Waiting for your confirmation"
        MSG_CN="等待你的确认"
        SOUND_NAME="Funk"
        ;;
    done)
        MSG="Task completed"
        MSG_CN="任务已完成"
        SOUND_NAME="Glass"
        ;;
    error)
        MSG="An error occurred"
        MSG_CN="发生错误"
        SOUND_NAME="Basso"
        ;;
    *)
        MSG="Notification"
        MSG_CN="通知"
        SOUND_NAME="Tink"
        ;;
esac

# Play sound
if [ -n "$CUSTOM_SOUND" ] && [ -f "$CUSTOM_SOUND" ]; then
    afplay "$CUSTOM_SOUND" &
else
    afplay "/System/Library/Sounds/${SOUND_NAME}.aiff" 2>/dev/null &
fi

# Show notification center alert (no sound name — afplay already handles audio)
osascript -e "display notification \"${MSG}\" with title \"${NOTIFICATION_TITLE}\"" 2>/dev/null &

# Bounce dock icon without stealing focus
# Method 1: Use Python + PyObjC (available by default on macOS) for proper NSApplication bounce
python3 -c "
try:
    from AppKit import NSApplication, NSInformationalRequest
    app = NSApplication.sharedApplication()
    app.requestUserAttention_(NSInformationalRequest)
except:
    pass
" 2>/dev/null &

# Method 2: Terminal bell — triggers Dock bounce on most terminal apps
printf '\a'

wait
