---
name: claude-web-remote
description: Set up remote browser access to Claude Code and dev site preview from any device (iPad, phone, another computer) with QR codes. Use when the user wants to access Claude Code remotely, work from a tablet or phone, or set up browser-based terminal access.
license: MIT
compatibility: Designed for Claude Code on macOS and Linux
---

# Claude Web Remote — Browser Access Setup

Set up remote access to Claude Code + dev site preview from any browser, with scannable QR codes and basic authentication.

## Prerequisites

Check and install if missing:

**macOS:**
```bash
brew install ttyd cloudflared qrencode
```

**Linux:**
```bash
# ttyd: https://github.com/tsl0922/ttyd/releases
# cloudflared: https://developers.cloudflare.com/cloudflare-one/connections/connect-networks/downloads/
sudo apt install qrencode
```

## Steps

1. **Detect the project type** — look at package.json, docker-compose.yml, requirements.txt, manage.py, etc. to find the dev server command and port.

2. **Generate a random password** for the ttyd session to prevent unauthorized access.

3. **Create `claude-remote.sh`** in the project root with this template, adapting SITE_PORT and the dev server command:

```bash
#!/bin/bash
# Claude Web Remote — access Claude Code + site preview from anywhere
# Uses ttyd (web terminal) + Cloudflare quick tunnels + QR codes
# Auth: ttyd basic auth protects terminal access

set -euo pipefail

CLAUDE_PORT=7682
SITE_PORT=3000  # Adapt: match your dev server port
CLAUDE_TUNNEL_LOG=$(mktemp)
SITE_TUNNEL_LOG=$(mktemp)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# --- Authentication ---
# Generate random credentials for this session
TTYD_USER="claude"
TTYD_PASS=$(LC_ALL=C tr -dc 'A-Za-z0-9' < /dev/urandom | head -c 16)

PIDS=()
cleanup() {
    echo ""
    echo "Shutting down..."
    for pid in "${PIDS[@]}"; do
        kill "$pid" 2>/dev/null || true
    done
    rm -f "$CLAUDE_TUNNEL_LOG" "$SITE_TUNNEL_LOG"
    wait 2>/dev/null
    echo "All processes stopped."
}
trap cleanup EXIT INT TERM

# --- Claude Code terminal (with basic auth) ---
echo "Starting Claude Code web terminal on port $CLAUDE_PORT..."
ttyd -W -p $CLAUDE_PORT \
    -c "${TTYD_USER}:${TTYD_PASS}" \
    -t fontSize=14 \
    -t 'theme={"background":"#1a1a2e","foreground":"#e0e0e0"}' \
    bash -c "cd $SCRIPT_DIR && claude" &
PIDS+=($!)
sleep 2

if ! kill -0 "${PIDS[-1]}" 2>/dev/null; then
    echo "Failed to start ttyd"
    exit 1
fi

# --- Dev server ---
echo "Starting dev server on port $SITE_PORT..."
# Adapt: change this to your dev server start command
cd "$SCRIPT_DIR" && npm run dev &
PIDS+=($!)
cd "$SCRIPT_DIR"
echo "Waiting for dev server to start..."
sleep 8

# --- Tunnels ---
echo "Creating Cloudflare tunnels..."
cloudflared tunnel --url http://localhost:$CLAUDE_PORT > "$CLAUDE_TUNNEL_LOG" 2>&1 &
PIDS+=($!)

cloudflared tunnel --url http://localhost:$SITE_PORT > "$SITE_TUNNEL_LOG" 2>&1 &
PIDS+=($!)

# Wait for both tunnel URLs
echo "Waiting for tunnel URLs..."
get_tunnel_url() {
    local logfile="$1"
    for i in $(seq 1 30); do
        local url
        url=$(grep -oE 'https://[a-z0-9-]+\.trycloudflare\.com' "$logfile" 2>/dev/null | head -1 || true)
        if [ -n "$url" ]; then
            echo "$url"
            return 0
        fi
        sleep 1
    done
    echo "FAILED"
    return 1
}

CLAUDE_URL=$(get_tunnel_url "$CLAUDE_TUNNEL_LOG")
SITE_URL=$(get_tunnel_url "$SITE_TUNNEL_LOG")

echo ""
echo "================================================"
echo "  CLAUDE WEB REMOTE"
echo "================================================"
echo ""

if [ "$CLAUDE_URL" != "FAILED" ]; then
    echo "  Claude Code:  $CLAUDE_URL"
    echo "  Login:        $TTYD_USER / $TTYD_PASS"
else
    echo "  Claude Code:  FAILED (check $CLAUDE_TUNNEL_LOG)"
fi

if [ "$SITE_URL" != "FAILED" ]; then
    echo "  Site Preview: $SITE_URL"
else
    echo "  Site Preview: FAILED (check $SITE_TUNNEL_LOG)"
fi

echo ""
echo "================================================"

if [ "$CLAUDE_URL" != "FAILED" ]; then
    echo ""
    echo "--- Claude Code QR ---"
    qrencode -t ANSIUTF8 "$CLAUDE_URL"
fi

if [ "$SITE_URL" != "FAILED" ]; then
    echo ""
    echo "--- Site Preview QR ---"
    qrencode -t ANSIUTF8 "$SITE_URL"
fi

echo ""
echo "Press Ctrl+C to stop"
echo ""

wait
```

4. **Make executable and run:**
```bash
chmod +x claude-remote.sh
./claude-remote.sh
```

5. **Show the user** the tunnel URLs, login credentials, and QR codes from the output. Remind them that the credentials are for the ttyd terminal login prompt.

## Adaptation Guide

- **Next.js**: `SITE_PORT=3000`, dev command = `npm run dev`
- **Vite/React**: `SITE_PORT=5173`, dev command = `npm run dev`
- **Flask**: `SITE_PORT=5000`, dev command = `python app.py` (use 5050 if 5000 is taken by AirPlay on macOS)
- **Django**: `SITE_PORT=8000`, dev command = `python manage.py runserver`
- **Static HTML**: Replace dev server block with `python3 -m http.server $SITE_PORT --directory ./public &`

## Security

- **Terminal auth**: ttyd is launched with `-c user:pass` flag for basic authentication. A random 16-character password is generated each session.
- **Tunnel URLs**: Cloudflare quick tunnels use random URLs that are hard to guess and expire when the script stops.
- **No Cloudflare account needed**: Quick tunnels are free and anonymous.
- **For stronger security**: Swap to a named Cloudflare tunnel with Access policies to gate access behind email verification.

## Notes

- Access via any browser (Safari, Chrome on iPad/phone works fine)
- Tunnel URLs are random and temporary — they die when the script stops
- `-W` flag on ttyd enables writable/interactive mode
- For persistent sessions, wrap in `tmux` before running
