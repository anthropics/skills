#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SKILL_SRC="$SCRIPT_DIR"
SKILL_DST="$HOME/.claude/skills/cmail"
HOOKS_SRC="$SKILL_SRC/scripts/hooks"
CLAUDE_SETTINGS="$HOME/.claude/settings.json"

echo "=== cmail Installer ==="
echo ""

# --- Step 1: Symlink skill into ~/.claude/skills/ ---

mkdir -p "$HOME/.claude/skills"

if [[ -L "$SKILL_DST" ]]; then
  echo "Removing existing symlink: $SKILL_DST"
  rm "$SKILL_DST"
elif [[ -d "$SKILL_DST" ]]; then
  echo "Warning: $SKILL_DST exists and is not a symlink."
  read -r -p "Replace it? [y/N] " confirm
  if [[ "$confirm" =~ ^[Yy]$ ]]; then
    rm -rf "$SKILL_DST"
  else
    echo "Aborted."
    exit 1
  fi
fi

ln -s "$SKILL_SRC" "$SKILL_DST"
echo "Linked: $SKILL_DST -> $SKILL_SRC"

# Make scripts executable
chmod +x "$SKILL_SRC/scripts/cmail.sh"
chmod +x "$SKILL_SRC/scripts/cmail-agent.sh"
chmod +x "$HOOKS_SRC"/*.sh 2>/dev/null || true
echo "Made scripts executable."

# --- Step 2: Install cmail to PATH ---

CMAIL_SCRIPT="$SKILL_SRC/scripts/cmail.sh"
CMAIL_BIN=""

install_to_path() {
  local target="$1"
  local use_sudo="${2:-false}"

  if [[ "$use_sudo" == true ]]; then
    sudo rm -f "$target" 2>/dev/null && \
    sudo ln -s "$CMAIL_SCRIPT" "$target" 2>/dev/null || return 1
  else
    rm -f "$target"
    ln -s "$CMAIL_SCRIPT" "$target" || return 1
  fi

  # Verify the symlink actually resolves
  if [[ -x "$target" ]] && "$target" help &>/dev/null; then
    CMAIL_BIN="$target"
    return 0
  else
    echo "  Warning: symlink created but doesn't resolve correctly. Removing."
    rm -f "$target" 2>/dev/null || sudo rm -f "$target" 2>/dev/null
    return 1
  fi
}

BIN_DIR="/usr/local/bin"
if [[ -w "$BIN_DIR" ]]; then
  install_to_path "$BIN_DIR/cmail" false
elif command -v sudo &>/dev/null; then
  install_to_path "$BIN_DIR/cmail" true
fi

if [[ -z "$CMAIL_BIN" ]]; then
  echo "Note: Could not install to $BIN_DIR. Trying ~/.local/bin instead."
  mkdir -p "$HOME/.local/bin"
  install_to_path "$HOME/.local/bin/cmail" false
  if [[ -n "$CMAIL_BIN" ]] && [[ ":$PATH:" != *":$HOME/.local/bin:"* ]]; then
    echo "  Add to PATH: export PATH=\"\$HOME/.local/bin:\$PATH\""
  fi
fi

if [[ -n "$CMAIL_BIN" ]]; then
  echo "Installed: $CMAIL_BIN (verified working)"
else
  echo "Warning: Could not install cmail to PATH. Use the full path:"
  echo "  $CMAIL_SCRIPT"
fi

# --- Step 3: Initialize ~/.cmail/ structure ---

mkdir -p "$HOME/.cmail/inbox" "$HOME/.cmail/outbox" "$HOME/.cmail/.agent"
echo "Created ~/.cmail/ directories."

CONFIG_JSON="$HOME/.cmail/config.json"
if [[ ! -f "$CONFIG_JSON" ]]; then
  IDENTITY="$(hostname | tr '[:upper:]' '[:lower:]' | sed 's/\.local$//')"
  cat > "$CONFIG_JSON" <<EOF
{
  "identity": "$IDENTITY",
  "hosts": {}
}
EOF
  echo "Created default config with identity: $IDENTITY"
else
  IDENTITY="$(jq -r '.identity // empty' "$CONFIG_JSON" 2>/dev/null || echo "")"
  echo "Config already exists (identity: ${IDENTITY:-unknown}), skipping."
fi

# --- Step 3b: Auto-discover Tailscale hosts ---

if command -v tailscale &>/dev/null && command -v jq &>/dev/null; then
  echo ""
  echo "Scanning Tailscale network for hosts..."
  SELF_HOST="$(tailscale status --json 2>/dev/null | jq -r '.Self.HostName // empty' 2>/dev/null | tr '[:upper:]' '[:lower:]')" || true

  PEERS="$(tailscale status --json 2>/dev/null | jq -r '
    .Peer | to_entries[] |
    select(.value.OS != "iOS" and .value.OS != "android") |
    "\(.value.HostName)\t\(.value.TailscaleIPs[0])\t\(.value.OS)\t\(.value.Online)"
  ' 2>/dev/null)" || true

  if [[ -n "$PEERS" ]]; then
    EXISTING_HOSTS="$(jq -r '.hosts | keys[]' "$CONFIG_JSON" 2>/dev/null | tr '[:upper:]' '[:lower:]')" || true
    PEER_NAMES=() PEER_INFO=()

    while IFS=$'\t' read -r p_name p_ip p_os p_online; do
      p_lower="$(echo "$p_name" | tr '[:upper:]' '[:lower:]')"
      [[ "$p_lower" == "$SELF_HOST" ]] && continue
      [[ "$p_lower" == "${IDENTITY:-}" ]] && continue
      echo "$EXISTING_HOSTS" | grep -qx "$p_lower" 2>/dev/null && continue

      status_str="offline"
      [[ "$p_online" == "true" ]] && status_str="online"
      PEER_NAMES+=("$p_lower")
      PEER_INFO+=("$p_name ($p_os, $status_str, $p_ip)")
    done <<< "$PEERS"

    if [[ ${#PEER_NAMES[@]} -gt 0 ]]; then
      echo ""
      echo "Found ${#PEER_NAMES[@]} host(s) on your Tailscale network:"
      echo ""
      for i in "${!PEER_INFO[@]}"; do
        echo "  $((i+1))) ${PEER_INFO[$i]}"
      done
      echo "  0) Skip — don't add any"
      echo ""
      echo "Enter numbers to add, separated by spaces (e.g. 1 3):"
      read -r -p "> " selections

      for sel in $selections; do
        [[ "$sel" == "0" ]] && break
        idx=$((sel - 1))
        if [[ $idx -ge 0 && $idx -lt ${#PEER_NAMES[@]} ]]; then
          sel_name="${PEER_NAMES[$idx]}"
          jq --arg name "$sel_name" --arg addr "$sel_name" --arg method "tailscale" \
            '.hosts[$name] = {"address": $addr, "ssh_method": $method}' "$CONFIG_JSON" > "$CONFIG_JSON.tmp" && mv "$CONFIG_JSON.tmp" "$CONFIG_JSON"
          echo "  Added: $sel_name (tailscale)"
        fi
      done
    else
      echo "All Tailscale peers already configured."
    fi
  else
    echo "No peers found on Tailscale network."
  fi
else
  if ! command -v tailscale &>/dev/null; then
    echo "Note: Tailscale not found — skipping host auto-discovery. Run 'cmail setup' to add hosts later."
  fi
fi

# --- Step 4: Auto-start watcher in shell profile ---

WATCH_LINE='command -v cmail &>/dev/null && cmail watch --daemon &>/dev/null &'
SHELL_RC=""
if [[ -f "$HOME/.zshrc" ]]; then
  SHELL_RC="$HOME/.zshrc"
elif [[ -f "$HOME/.bashrc" ]]; then
  SHELL_RC="$HOME/.bashrc"
elif [[ -f "$HOME/.bash_profile" ]]; then
  SHELL_RC="$HOME/.bash_profile"
fi

if [[ -n "$SHELL_RC" ]]; then
  if ! grep -qF "cmail watch --daemon" "$SHELL_RC" 2>/dev/null; then
    echo "" >> "$SHELL_RC"
    echo "# cmail: auto-start inbox watcher" >> "$SHELL_RC"
    echo "$WATCH_LINE" >> "$SHELL_RC"
    echo "Added cmail watcher to $SHELL_RC"
  else
    echo "Watcher already in $SHELL_RC, skipping."
  fi
else
  echo "Note: Could not find shell rc file. Add this to your shell profile manually:"
  echo "  $WATCH_LINE"
fi

# --- Step 5: Register Claude Code permissions and hooks ---

install_permissions_and_hooks() {
  if [[ ! -f "$CLAUDE_SETTINGS" ]]; then
    echo "No Claude Code settings found at $CLAUDE_SETTINGS — skipping."
    return 0
  fi

  if ! command -v jq &>/dev/null; then
    echo "jq not found — skipping settings registration. Install jq and re-run."
    return 0
  fi

  local tmp="$CLAUDE_SETTINGS.tmp"
  local changed=false

  # --- Permissions ---
  # Include both short command and resolved full paths so permissions work
  # regardless of whether cmail is on PATH or invoked directly
  local resolved_script
  resolved_script="$(readlink -f "$CMAIL_SCRIPT" 2>/dev/null || echo "$CMAIL_SCRIPT")"

  local cmail_perms=(
    'Bash(cmail *)'
    "Bash($CMAIL_SCRIPT *)"
    "Bash($resolved_script *)"
    'Bash(~/.claude/skills/cmail/scripts/cmail.sh *)'
    'Bash(rm -f ~/.cmail/inbox/*.json *)'
    'Bash(rm -f ~/.cmail/.has_unread)'
    'Bash(rm -f ~/.cmail/.last_stop_check)'
    'Bash(ls ~/.cmail/inbox/*)'
    'Bash(tailscale ssh *)'
    'Bash(claude --print *)'
  )

  # Deduplicate (resolved path may equal CMAIL_SCRIPT)
  local unique_perms=()
  local seen=""
  for perm in "${cmail_perms[@]}"; do
    if [[ "$seen" != *"|$perm|"* ]]; then
      unique_perms+=("$perm")
      seen+="|$perm|"
    fi
  done
  cmail_perms=("${unique_perms[@]}")

  # Check which permissions are missing
  local existing_perms
  existing_perms="$(jq -r '.permissions.allow // [] | .[]' "$CLAUDE_SETTINGS" 2>/dev/null)" || true

  local perms_to_add=()
  for perm in "${cmail_perms[@]}"; do
    if ! echo "$existing_perms" | grep -qF "$perm"; then
      perms_to_add+=("$perm")
    fi
  done

  if [[ ${#perms_to_add[@]} -gt 0 ]]; then
    local perms_json
    perms_json="$(printf '%s\n' "${perms_to_add[@]}" | jq -R . | jq -s .)"
    jq --argjson new "$perms_json" '
      .permissions //= {} |
      .permissions.allow = ((.permissions.allow // []) + $new | unique)
    ' "$CLAUDE_SETTINGS" > "$tmp" && mv "$tmp" "$CLAUDE_SETTINGS"
    echo "Added ${#perms_to_add[@]} cmail permissions."
    changed=true
  else
    echo "cmail permissions already registered."
  fi

  # --- Hooks ---
  local session_start="$HOOKS_SRC/session-start.sh"
  local user_prompt="$HOOKS_SRC/user-prompt-submit.sh"
  local stop_hook="$HOOKS_SRC/stop.sh"

  if jq -r '.hooks | .. | .command? // empty' "$CLAUDE_SETTINGS" 2>/dev/null | grep -q "cmail"; then
    echo "cmail hooks already registered."
  else
    jq --arg ss "$session_start" --arg up "$user_prompt" --arg st "$stop_hook" '
      .hooks //= {} |
      .hooks.SessionStart = (.hooks.SessionStart // []) + [{
        "hooks": [{"type": "command", "command": $ss, "timeout": 10}]
      }] |
      .hooks.UserPromptSubmit = (.hooks.UserPromptSubmit // []) + [{
        "hooks": [{"type": "command", "command": $up, "timeout": 5}]
      }] |
      .hooks.Stop = (.hooks.Stop // []) + [{
        "hooks": [{"type": "command", "command": $st, "timeout": 10}]
      }]
    ' "$CLAUDE_SETTINGS" > "$tmp" && mv "$tmp" "$CLAUDE_SETTINGS"
    echo "Registered Claude Code hooks (SessionStart, UserPromptSubmit, Stop)."
    changed=true
  fi

  if [[ "$changed" == true ]]; then
    echo "  Updated: $CLAUDE_SETTINGS"
  fi
}

install_permissions_and_hooks

# --- Step 6: Status line integration ---

STATUSLINE_SCRIPT="$HOME/.claude/statusline-command.sh"
CMAIL_MARKER="# cmail-statusline-start"

if [[ -f "$STATUSLINE_SCRIPT" ]]; then
  if grep -qF "$CMAIL_MARKER" "$STATUSLINE_SCRIPT" 2>/dev/null; then
    echo "cmail statusline already present, skipping."
  else
    CMAIL_BLOCK='# cmail-statusline-start
# cmail inbox count (added by cmail installer)
_cmail_count=$(ls -1 "$HOME/.cmail/inbox/"*.json 2>/dev/null | wc -l | tr -d '"'"' '"'"')
if (( _cmail_count > 0 )); then
    _cmail_info=" \\033[38;2;128;128;128m|\\033[0m \\033[1m(${_cmail_count})\\033[22m cmail"
else
    _cmail_info=" \\033[38;2;128;128;128m|\\033[0m \\033[38;2;128;128;128m(0) cmail\\033[0m"
fi
# cmail-statusline-end'

    # Try to insert before the output line and wire into it
    if grep -q '^line=' "$STATUSLINE_SCRIPT"; then
      # Insert cmail block before the line= assignment, then append ${_cmail_info} to it
      tmp_sl="$STATUSLINE_SCRIPT.tmp"
      awk -v block="$CMAIL_BLOCK" '
        /^line=/ && !done {
          print block
          print ""
          # Append ${_cmail_info} to the line= value
          sub(/"$/, "${_cmail_info}\"")
          done=1
        }
        { print }
      ' "$STATUSLINE_SCRIPT" > "$tmp_sl" && mv "$tmp_sl" "$STATUSLINE_SCRIPT"
      echo "Added cmail count to statusline (auto-wired into output)."
    else
      # Fallback: append block and note for manual wiring
      printf '\n%s\n' "$CMAIL_BLOCK" >> "$STATUSLINE_SCRIPT"
      echo "Added cmail count to statusline script."
      echo "  Note: Add \${_cmail_info} to your status line output variable to display it."
    fi
  fi
else
  echo "No statusline script found — status line integration skipped."
  echo "  To add manually, see: cmail setup"
fi

# --- Step 7: Enable agent (opt-in) ---

if [[ ! -f "$HOME/.cmail/.agent-enabled" ]]; then
  echo ""
  echo "The auto-respond agent uses 'claude --print' to automatically reply"
  echo "to incoming messages. This uses API credits and grants the agent"
  echo "tools (Bash, Edit, Write, Read) to fulfill requests."
  read -r -p "Enable auto-respond agent? [y/N] " enable_agent
  if [[ "$enable_agent" =~ ^[Yy]$ ]]; then
    touch "$HOME/.cmail/.agent-enabled"
    echo "Enabled auto-respond agent."
  else
    echo "Agent not enabled. Enable later with: touch ~/.cmail/.agent-enabled"
  fi
else
  echo "Agent already enabled."
fi

# --- Step 8: Start watcher ---

"$SKILL_SRC/scripts/cmail.sh" watch --daemon &>/dev/null &
echo "Started cmail watcher (PID: $!)."

# --- Done ---

echo ""
echo "Installation complete!"
echo ""
echo "Next steps:"
echo "  1. Run guided setup:  cmail setup"
echo "  2. Test connectivity:  cmail hosts"
echo "  3. Send a message:     cmail send <host> \"hello\""
