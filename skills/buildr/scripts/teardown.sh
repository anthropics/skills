#!/bin/bash
# ============================================================
# Buildr Teardown - Clean uninstaller
#
# Usage: ./teardown.sh
#
# What this does:
#   1. Stops and removes PM2 relay process
#   2. Kills tmux CC session if running
#   3. Removes Buildr hooks from Claude Code settings
#   4. Optionally removes ~/.buildr/ directory
# ============================================================

set -e

BUILDR_HOME="${HOME}/.buildr"
SETTINGS_FILE="${HOME}/.claude/settings.json"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

log()  { echo -e "${GREEN}[buildr]${NC} $1"; }
warn() { echo -e "${YELLOW}[buildr]${NC} $1"; }

echo -e "${YELLOW}Buildr Teardown${NC}"
echo ""

# --- 1. Stop PM2 relay ---
if command -v pm2 &>/dev/null; then
  if pm2 describe buildr-relay &>/dev/null; then
    pm2 delete buildr-relay 2>/dev/null || true
    pm2 save 2>/dev/null || true
    log "Stopped PM2 relay daemon"
  else
    log "PM2 relay not running (already stopped)"
  fi
else
  warn "PM2 not found, skipping"
fi

# --- 2. Kill tmux session ---
if command -v tmux &>/dev/null; then
  if tmux has-session -t buildr-cc 2>/dev/null; then
    tmux kill-session -t buildr-cc 2>/dev/null || true
    log "Killed tmux CC session"
  else
    log "No tmux CC session running"
  fi
fi

# --- 3. Remove hooks from Claude Code settings ---
if [ -f "$SETTINGS_FILE" ]; then
  python3 << PYEOF
import json

with open("$SETTINGS_FILE") as f:
    settings = json.load(f)

hooks = settings.get('hooks', {})
changed = False

for hook_type in ['PreToolUse', 'PermissionRequest']:
    if hook_type in hooks:
        original = len(hooks[hook_type])
        hooks[hook_type] = [
            h for h in hooks[hook_type]
            if not any('buildr' in (hk.get('command','') or '') for hk in h.get('hooks', []))
        ]
        if len(hooks[hook_type]) != original:
            changed = True
        if not hooks[hook_type]:
            del hooks[hook_type]

if not hooks:
    if 'hooks' in settings:
        del settings['hooks']

with open("$SETTINGS_FILE", 'w') as f:
    json.dump(settings, f, indent=2)

if changed:
    print("Removed Buildr hooks from settings.json")
else:
    print("No Buildr hooks found in settings.json")
PYEOF
  log "Claude Code hooks cleaned"
else
  log "No settings.json found, skipping"
fi

# --- 4. Remove data directory ---
echo ""
if [ -d "$BUILDR_HOME" ]; then
  read -p "Remove $BUILDR_HOME and all data? [y/N]: " CONFIRM
  if [ "$CONFIRM" = "y" ] || [ "$CONFIRM" = "Y" ]; then
    rm -rf "$BUILDR_HOME"
    log "Removed $BUILDR_HOME"
  else
    log "Kept $BUILDR_HOME (you can remove it manually later)"
  fi
else
  log "No $BUILDR_HOME directory found"
fi

echo ""
echo -e "${GREEN}Buildr has been uninstalled.${NC}"
echo ""
