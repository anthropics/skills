#!/bin/bash

# Shell helper for sending notifications to the notification hub

NOTIFY_HOST="localhost"
NOTIFY_PORT=9999

send_notification() {
    local title="${1:-Notification}"
    local message="${2:-}"
    
    if [ -z "$message" ]; then
        echo "Usage: $0 \"Title\" \"Message\""
        exit 1
    fi
    
    # Create JSON payload
    local json_payload=$(cat <<EOF
{"title":"$title","message":"$message"}
EOF
)
    
    # Send to notification hub
    echo "$json_payload" | nc $NOTIFY_HOST $NOTIFY_PORT > /dev/null 2>&1
    
    if [ $? -eq 0 ]; then
        echo "✓ Notification sent: $title"
    else
        echo "✗ Failed to send notification (is notification hub running?)"
        exit 1
    fi
}

# Main
if [ $# -lt 2 ]; then
    echo "Send notification via socket to notification hub"
    echo ""
    echo "Usage: $0 \"Title\" \"Message\""
    echo ""
    echo "Example:"
    echo "  $0 \"Task Complete\" \"Your file processing is done!\""
    exit 1
fi

send_notification "$1" "$2"
