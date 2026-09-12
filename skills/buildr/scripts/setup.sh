#!/bin/bash
# ============================================================
# Buildr Setup - One-command installer for CC <> Telegram bridge
#
# Usage:
#   ./setup.sh <BOT_TOKEN> <USER_ID>
#   ./setup.sh   (interactive - prompts for token and user ID)
#
# What this does:
#   1. Creates ~/.buildr/ working directory
#   2. Copies relay, hooks to ~/.buildr/
#   3. Writes config.env with token + user ID
#   4. Installs PM2 if needed, starts relay daemon
#   5. Adds PreToolUse + PermissionRequest hooks to Claude Code
#   6. Sets up tmux session for CC persistence (survives laptop close)
#   7. Sends test message to verify connection
# ============================================================

set -e

BUILDR_HOME="${HOME}/.buildr"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SETTINGS_FILE="${HOME}/.claude/settings.json"

# --- Colors ---
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

log()  { echo -e "${GREEN}[buildr]${NC} $1"; }
warn() { echo -e "${YELLOW}[buildr]${NC} $1"; }
err()  { echo -e "${RED}[buildr]${NC} $1"; }

# --- Get credentials ---
BOT_TOKEN="${1:-}"
USER_ID="${2:-}"

if [ -z "$BOT_TOKEN" ]; then
  echo -e "${CYAN}Buildr Setup${NC}"
  echo ""
  echo "You need:"
  echo "  1. A Telegram bot token (from @BotFather)"
  echo "  2. Your Telegram user ID (from @userinfobot)"
  echo ""
  read -p "Bot token: " BOT_TOKEN
fi

if [ -z "$USER_ID" ]; then
  read -p "Your Telegram user ID: " USER_ID
fi

if [ -z "$BOT_TOKEN" ] || [ -z "$USER_ID" ]; then
  err "Both BOT_TOKEN and USER_ID are required."
  exit 1
fi

log "Setting up Buildr..."
log "Home: $BUILDR_HOME"
log "User ID: $USER_ID"

# --- 1. Create directory ---
mkdir -p "$BUILDR_HOME"
log "Created $BUILDR_HOME"

# --- 2. Copy files ---
cp "$SCRIPT_DIR/relay.js" "$BUILDR_HOME/relay.js"
cp "$SCRIPT_DIR/bridge-hook.py" "$BUILDR_HOME/bridge-hook.py"
cp "$SCRIPT_DIR/perm-hook.sh" "$BUILDR_HOME/perm-hook.sh"
chmod +x "$BUILDR_HOME/perm-hook.sh"
chmod +x "$BUILDR_HOME/bridge-hook.py"
log "Copied relay, hooks to $BUILDR_HOME"

# --- 3. Write config ---
cat > "$BUILDR_HOME/config.env" << EOF
BOT_TOKEN=$BOT_TOKEN
USER_ID=$USER_ID
EOF
log "Config written to $BUILDR_HOME/config.env"

# --- 4. Initialize files ---
touch "$BUILDR_HOME/inbox.jsonl"
touch "$BUILDR_HOME/outbox.jsonl"
echo "0" > "$BUILDR_HOME/heartbeat"
log "Initialized data files"

# --- 5. PM2 setup ---
if ! command -v pm2 &>/dev/null; then
  warn "PM2 not found. Installing globally..."
  npm install -g pm2 2>/dev/null || {
    err "Failed to install PM2. Please install it: npm install -g pm2"
    exit 1
  }
fi

# Stop existing if running
pm2 delete buildr-relay 2>/dev/null || true

# Create PM2 ecosystem file for proper env var passing
cat > "$BUILDR_HOME/ecosystem.config.js" << ECOEOF
module.exports = {
  apps: [{
    name: 'buildr-relay',
    script: '$BUILDR_HOME/relay.js',
    env: { BUILDR_HOME: '$BUILDR_HOME' },
    autorestart: true,
    restart_delay: 3000,
    max_restarts: 50,
    watch: false,
  }]
};
ECOEOF

# Start relay daemon
pm2 start "$BUILDR_HOME/ecosystem.config.js"
pm2 save 2>/dev/null || true
log "Relay daemon started via PM2 (buildr-relay)"

# Try to set up PM2 startup (survives server reboot)
pm2 startup 2>/dev/null || warn "Run 'pm2 startup' manually to survive reboots"

# --- 6. Claude Code hooks ---
mkdir -p "$(dirname "$SETTINGS_FILE")"

# Create or update settings.json
if [ -f "$SETTINGS_FILE" ]; then
  # Merge hooks into existing settings
  python3 << PYEOF
import json, os

settings_file = "$SETTINGS_FILE"
buildr_home = "$BUILDR_HOME"

with open(settings_file) as f:
    settings = json.load(f)

hooks = settings.get('hooks', {})

# PreToolUse hook
pre_hooks = hooks.get('PreToolUse', [])
# Remove any existing buildr hooks
pre_hooks = [h for h in pre_hooks if not any('buildr' in (hk.get('command','') or '') for hk in h.get('hooks', []))]
pre_hooks.append({
    "matcher": "",
    "hooks": [{
        "type": "command",
        "command": f"python3 {buildr_home}/bridge-hook.py",
        "timeout": 86400
    }]
})
hooks['PreToolUse'] = pre_hooks

# PermissionRequest hook
perm_hooks = hooks.get('PermissionRequest', [])
perm_hooks = [h for h in perm_hooks if not any('buildr' in (hk.get('command','') or '') for hk in h.get('hooks', []))]
perm_hooks.append({
    "matcher": "",
    "hooks": [{
        "type": "command",
        "command": f"{buildr_home}/perm-hook.sh",
        "timeout": 86400
    }]
})
hooks['PermissionRequest'] = perm_hooks

settings['hooks'] = hooks

with open(settings_file, 'w') as f:
    json.dump(settings, f, indent=2)

print("Hooks merged into existing settings.json")
PYEOF
else
  # Create fresh settings.json
  python3 << PYEOF
import json

buildr_home = "$BUILDR_HOME"
settings = {
    "hooks": {
        "PreToolUse": [{
            "matcher": "",
            "hooks": [{
                "type": "command",
                "command": f"python3 {buildr_home}/bridge-hook.py",
                "timeout": 86400
            }]
        }],
        "PermissionRequest": [{
            "matcher": "",
            "hooks": [{
                "type": "command",
                "command": f"{buildr_home}/perm-hook.sh",
                "timeout": 86400
            }]
        }]
    }
}

with open("$SETTINGS_FILE", 'w') as f:
    json.dump(settings, f, indent=2)

print("Created settings.json with hooks")
PYEOF
fi
log "Claude Code hooks configured"

# --- 7. Tmux persistence setup ---
# Create a startup script that launches CC in tmux
cat > "$BUILDR_HOME/start-cc.sh" << 'TMUXEOF'
#!/bin/bash
# Start Claude Code in a persistent tmux session
# This keeps CC alive even when VS Code / SSH disconnects

SESSION="buildr-cc"
BUILDR_HOME="${BUILDR_HOME:-$HOME/.buildr}"

# Check if tmux is available
if ! command -v tmux &>/dev/null; then
  echo "[buildr] tmux not installed. Install with: apt install tmux"
  exit 1
fi

# Check if session already exists
if tmux has-session -t "$SESSION" 2>/dev/null; then
  echo "[buildr] tmux session '$SESSION' already running"
  echo "[buildr] Attach with: tmux attach -t $SESSION"
  exit 0
fi

# Create detached tmux session running claude
tmux new-session -d -s "$SESSION" -x 200 -y 50
tmux send-keys -t "$SESSION" "export BUILDR_HOME=$BUILDR_HOME && claude" Enter

echo "[buildr] Started CC in tmux session '$SESSION'"
echo "[buildr] Attach: tmux attach -t $SESSION"
echo "[buildr] Detach: Ctrl+B then D"
TMUXEOF
chmod +x "$BUILDR_HOME/start-cc.sh"
log "Tmux persistence script created: $BUILDR_HOME/start-cc.sh"

# --- 8. Create CLAUDE.md instructions for new sessions ---
cat > "$BUILDR_HOME/CLAUDE.md" << 'CLAUDEEOF'
# Buildr - Telegram Bridge Protocol

You are bridged to Telegram. Every response you give here is mirrored to the user's Telegram chat.

## MANDATORY - Every Response:

1. **Mirror to TG**: Write every response to the outbox file:
   ```
   python3 -c "import json, os; home=os.environ.get('BUILDR_HOME',os.path.expanduser('~/.buildr')); open(os.path.join(home,'outbox.jsonl'),'a').write(json.dumps({'text':'YOUR MESSAGE HERE'}) + '\n')"
   ```

2. **On compaction**: Send "COMPACTED" to TG (saves space, keeps user informed)

3. **When done/waiting**: Create await flag, then make any tool call:
   ```
   touch ~/.buildr/await-flag
   ```
   The hook will notify the user and wait for their response.

## Rules:
- Do NOT use curl/API for TG - use the outbox file only (relay delivers within 2s)
- If user says STOP on Telegram - halt immediately
- All TG messages arrive via the PreToolUse hook (blocks once to show you)
- Permission requests are forwarded to TG automatically
CLAUDEEOF
log "CLAUDE.md bridge instructions created"

# --- 9. Test connection ---
log "Testing Telegram connection..."
python3 << PYEOF
import json
outbox = "$BUILDR_HOME/outbox.jsonl"
with open(outbox, 'a') as f:
    f.write(json.dumps({'text': 'Buildr setup complete! Bridge is active.\n\nCommands:\n/status - Check status\n/help - Show help\nSTOP - Halt CC\n\nYour messages here will be forwarded to Claude Code.'}) + '\n')
PYEOF

# Wait briefly for relay to pick up and send
sleep 3

echo ""
echo -e "${GREEN}============================================${NC}"
echo -e "${GREEN}  Buildr Setup Complete!${NC}"
echo -e "${GREEN}============================================${NC}"
echo ""
echo -e "  Home:    ${CYAN}$BUILDR_HOME${NC}"
echo -e "  Relay:   ${CYAN}pm2 status buildr-relay${NC}"
echo -e "  Logs:    ${CYAN}pm2 logs buildr-relay${NC}"
echo ""
echo -e "  ${YELLOW}For persistent CC (survives laptop close):${NC}"
echo -e "  ${CYAN}$BUILDR_HOME/start-cc.sh${NC}"
echo ""
echo -e "  ${YELLOW}To uninstall:${NC}"
echo -e "  ${CYAN}$(dirname "$0")/teardown.sh${NC}"
echo ""
echo -e "  Send a message to your bot on Telegram to test!"
echo ""
