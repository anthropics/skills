#!/bin/bash
# Agent Notify - Linux Notification Script
# Plays sound and shows desktop notification

TYPE="${1:-default}"
CONFIG_PATH="${2:-}"

# Default values
CUSTOM_SOUND=""
URGENCY="normal"

# Load config if provided
if [ -n "$CONFIG_PATH" ] && [ -f "$CONFIG_PATH" ]; then
    if command -v jq &>/dev/null; then
        CUSTOM_SOUND=$(jq -r ".sounds.${TYPE} // empty" "$CONFIG_PATH" 2>/dev/null)
    elif command -v python3 &>/dev/null; then
        CUSTOM_SOUND=$(python3 -c "import json; c=json.load(open('$CONFIG_PATH')); print(c.get('sounds',{}).get('$TYPE',''))" 2>/dev/null)
    fi
fi

# Determine notification message and sound
case "$TYPE" in
    confirm)
        MSG="Waiting for your confirmation"
        ICON="dialog-question"
        URGENCY="critical"
        SYSTEM_SOUND="/usr/share/sounds/freedesktop/stereo/dialog-warning.oga"
        ;;
    done)
        MSG="Task completed"
        ICON="dialog-information"
        URGENCY="normal"
        SYSTEM_SOUND="/usr/share/sounds/freedesktop/stereo/complete.oga"
        ;;
    error)
        MSG="An error occurred"
        ICON="dialog-error"
        URGENCY="critical"
        SYSTEM_SOUND="/usr/share/sounds/freedesktop/stereo/dialog-error.oga"
        ;;
    *)
        MSG="Notification"
        ICON="dialog-information"
        URGENCY="normal"
        SYSTEM_SOUND="/usr/share/sounds/freedesktop/stereo/message.oga"
        ;;
esac

# Play sound
play_sound() {
    local sound_file="$1"
    if [ -n "$sound_file" ] && [ -f "$sound_file" ]; then
        if command -v paplay &>/dev/null; then
            paplay "$sound_file" 2>/dev/null &
        elif command -v aplay &>/dev/null; then
            aplay "$sound_file" 2>/dev/null &
        elif command -v pw-play &>/dev/null; then
            pw-play "$sound_file" 2>/dev/null &
        fi
        return 0
    fi
    return 1
}

if [ -n "$CUSTOM_SOUND" ]; then
    play_sound "$CUSTOM_SOUND" || play_sound "$SYSTEM_SOUND"
else
    play_sound "$SYSTEM_SOUND"
fi

# Show desktop notification
if command -v notify-send &>/dev/null; then
    notify-send -u "$URGENCY" -i "$ICON" "Agent Notify" "$MSG" 2>/dev/null &
fi

wait
