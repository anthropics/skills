#!/usr/bin/env bash
set -euo pipefail

COMMS_DIR="$HOME/.cmail"
INBOX_DIR="$COMMS_DIR/inbox"
OUTBOX_DIR="$COMMS_DIR/outbox"
CONFIG_FILE="$COMMS_DIR/config.json"
UNREAD_MARKER="$COMMS_DIR/.has_unread"

DEPS_CHECKED_MARKER="$COMMS_DIR/.deps_checked"

# Resolve real script directory (follow symlinks)
SCRIPT_REAL_PATH="$(readlink -f "$0" 2>/dev/null || python3 -c "import os; print(os.path.realpath('$0'))" 2>/dev/null || echo "$0")"
SCRIPT_DIR="$(cd "$(dirname "$SCRIPT_REAL_PATH")" && pwd)"

# --- Dependency Management ---

detect_pkg_manager() {
  if command -v brew &>/dev/null; then echo "brew"
  elif command -v apt-get &>/dev/null; then echo "apt"
  elif command -v dnf &>/dev/null; then echo "dnf"
  elif command -v yum &>/dev/null; then echo "yum"
  elif command -v pacman &>/dev/null; then echo "pacman"
  elif command -v apk &>/dev/null; then echo "apk"
  else echo "unknown"
  fi
}

install_pkg() {
  local pkg="$1"
  local mgr
  mgr="$(detect_pkg_manager)"
  case "$mgr" in
    brew)   brew install "$pkg" ;;
    apt)    sudo apt-get install -y "$pkg" ;;
    dnf)    sudo dnf install -y "$pkg" ;;
    yum)    sudo yum install -y "$pkg" ;;
    pacman) sudo pacman -S --noconfirm "$pkg" ;;
    apk)    sudo apk add "$pkg" ;;
    *)      return 1 ;;
  esac
}

# Maps logical dep names to package names per manager
pkg_name() {
  local dep="$1" mgr="$2"
  case "$dep" in
    jq) echo "jq" ;;
    fswatch) echo "fswatch" ;;
    inotifywait)
      case "$mgr" in
        apt|dnf|yum) echo "inotify-tools" ;;
        pacman) echo "inotify-tools" ;;
        apk) echo "inotify-tools" ;;
        *) echo "inotify-tools" ;;
      esac
      ;;
  esac
}

check_deps() {
  # Skip if already checked this install
  [[ -f "$DEPS_CHECKED_MARKER" ]] && return 0

  mkdir -p "$COMMS_DIR"
  local missing=()

  # jq is strongly recommended
  if ! command -v jq &>/dev/null; then
    missing+=("jq")
  fi

  # File watcher (platform-dependent)
  if [[ "$(uname)" == "Darwin" ]]; then
    if ! command -v fswatch &>/dev/null; then
      missing+=("fswatch")
    fi
  else
    if ! command -v inotifywait &>/dev/null; then
      missing+=("inotifywait")
    fi
  fi

  if [[ ${#missing[@]} -eq 0 ]]; then
    touch "$DEPS_CHECKED_MARKER"
    return 0
  fi

  local mgr
  mgr="$(detect_pkg_manager)"

  echo "cmail: missing optional dependencies: ${missing[*]}"

  if [[ "$mgr" == "unknown" ]]; then
    echo "Could not detect package manager. Please install manually: ${missing[*]}"
    # Don't block — deps are optional
    touch "$DEPS_CHECKED_MARKER"
    return 0
  fi

  echo "Install them now? (Uses $mgr) [Y/n] "
  read -r confirm </dev/tty 2>/dev/null || confirm="y"
  if [[ "$confirm" =~ ^[Nn] ]]; then
    echo "Skipping. cmail will use fallbacks where available."
    touch "$DEPS_CHECKED_MARKER"
    return 0
  fi

  for dep in "${missing[@]}"; do
    local actual_pkg
    actual_pkg="$(pkg_name "$dep" "$mgr")"
    echo "Installing $actual_pkg..."
    if install_pkg "$actual_pkg"; then
      echo "  Installed $actual_pkg"
    else
      echo "  Failed to install $actual_pkg — continuing without it"
    fi
  done

  touch "$DEPS_CHECKED_MARKER"
}

cmd_deps() {
  # Force re-check by removing marker
  rm -f "$DEPS_CHECKED_MARKER"
  check_deps
  echo ""
  echo "Dependency status:"
  printf "  %-15s %s\n" "jq" "$(command -v jq &>/dev/null && echo "installed" || echo "missing (using python3 fallback)")"
  printf "  %-15s %s\n" "python3" "$(command -v python3 &>/dev/null && echo "installed" || echo "missing")"
  if [[ "$(uname)" == "Darwin" ]]; then
    printf "  %-15s %s\n" "fswatch" "$(command -v fswatch &>/dev/null && echo "installed" || echo "missing (needed for watch command)")"
  else
    printf "  %-15s %s\n" "inotifywait" "$(command -v inotifywait &>/dev/null && echo "installed" || echo "missing (needed for watch command)")"
  fi
  printf "  %-15s %s\n" "ssh" "$(command -v ssh &>/dev/null && echo "installed" || echo "missing")"
  printf "  %-15s %s\n" "tailscale" "$(command -v tailscale &>/dev/null && echo "installed" || echo "not found")"
}

# --- Helpers ---

ensure_dirs() {
  mkdir -p "$INBOX_DIR" "$OUTBOX_DIR"
}

ensure_config() {
  ensure_dirs
  if [[ ! -f "$CONFIG_FILE" ]]; then
    local identity
    identity="$(hostname | tr '[:upper:]' '[:lower:]' | sed 's/\.local$//')"
    cat > "$CONFIG_FILE" <<EOF
{
  "identity": "$identity",
  "hosts": {}
}
EOF
    echo "Created config with identity: $identity"
    echo "Run 'cmail setup' to add hosts."
  fi
}

get_identity() {
  ensure_config
  json_get "$CONFIG_FILE" '.identity'
}

generate_uuid() {
  if command -v uuidgen &>/dev/null; then
    uuidgen | tr '[:upper:]' '[:lower:]'
  elif [[ -f /proc/sys/kernel/random/uuid ]]; then
    cat /proc/sys/kernel/random/uuid
  else
    python3 -c "import uuid; print(uuid.uuid4())"
  fi
}

sanitize_filename_part() {
  echo "$1" | tr -cd 'a-zA-Z0-9._-'
}

get_timestamp() {
  if date -u +%Y-%m-%dT%H:%M:%S.000Z 2>/dev/null; then
    return
  fi
  python3 -c "from datetime import datetime, timezone; print(datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%S.000Z'))"
}

get_filename_timestamp() {
  if date -u +%Y%m%dT%H%M%S.000Z 2>/dev/null; then
    return
  fi
  python3 -c "from datetime import datetime, timezone; print(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.000Z'))"
}

json_get() {
  local file="$1" query="$2"
  if command -v jq &>/dev/null; then
    jq -r "$query" "$file"
  else
    CMAIL_FILE="$file" CMAIL_QUERY="$query" python3 -c "
import json, os, functools
with open(os.environ['CMAIL_FILE']) as f: data = json.load(f)
keys = os.environ['CMAIL_QUERY'].strip('.').split('.')
result = functools.reduce(lambda d, k: d[k] if isinstance(d, dict) else d[int(k)], keys, data)
print(result)
" 2>/dev/null || echo "null"
  fi
}

json_get_str() {
  local str="$1" query="$2"
  if command -v jq &>/dev/null; then
    echo "$str" | jq -r "$query"
  else
    CMAIL_QUERY="$query" python3 -c "
import json, sys, os, functools
data = json.loads(sys.stdin.read())
keys = os.environ['CMAIL_QUERY'].strip('.').split('.')
result = functools.reduce(lambda d, k: d[k] if isinstance(d, dict) else d[int(k)], keys, data)
print(result)
" <<< "$str" 2>/dev/null || echo "null"
  fi
}

get_host_address() {
  local host="$1"
  ensure_config
  if command -v jq &>/dev/null; then
    jq -r ".hosts[\"$host\"].address // empty" "$CONFIG_FILE"
  else
    CMAIL_CONFIG="$CONFIG_FILE" CMAIL_HOST="$host" python3 -c "
import json, os
with open(os.environ['CMAIL_CONFIG']) as f:
    data = json.load(f)
addr = data.get('hosts', {}).get(os.environ['CMAIL_HOST'], {}).get('address', '')
if addr: print(addr)
"
  fi
}

get_host_ssh_method() {
  local host="$1"
  ensure_config
  if command -v jq &>/dev/null; then
    jq -r ".hosts[\"$host\"].ssh_method // \"tailscale\"" "$CONFIG_FILE"
  else
    CMAIL_CONFIG="$CONFIG_FILE" CMAIL_HOST="$host" python3 -c "
import json, os
with open(os.environ['CMAIL_CONFIG']) as f:
    data = json.load(f)
method = data.get('hosts', {}).get(os.environ['CMAIL_HOST'], {}).get('ssh_method', 'tailscale')
print(method)
"
  fi
}

# Resolve a sender identity (from message's "from" field) to a configured host name.
# The sender's identity may differ from the config key (e.g. "biggirldl380" vs "biggirl").
# Tries: exact match, case-insensitive match, then substring match.
resolve_sender_to_host() {
  local sender="$1"
  local sender_lower
  sender_lower="$(echo "$sender" | tr '[:upper:]' '[:lower:]')"

  # Check if sender matches a configured host name directly
  local address
  address="$(get_host_address "$sender")"
  if [[ -n "$address" ]]; then
    echo "$sender"
    return
  fi

  # Search configured hosts for a name that's a substring of the sender or vice versa
  local hosts=""
  if command -v jq &>/dev/null; then
    hosts="$(jq -r '.hosts | keys[]' "$CONFIG_FILE" 2>/dev/null)" || true
  else
    hosts="$(CMAIL_CONFIG="$CONFIG_FILE" python3 -c "
import json, os
with open(os.environ['CMAIL_CONFIG']) as f: data = json.load(f)
for k in data.get('hosts', {}): print(k)
" 2>/dev/null)" || true
  fi

  while IFS= read -r h; do
    [[ -z "$h" ]] && continue
    local h_lower
    h_lower="$(echo "$h" | tr '[:upper:]' '[:lower:]')"
    # biggirl matches biggirldl380, or biggirldl380 matches biggirl
    if [[ "$sender_lower" == *"$h_lower"* || "$h_lower" == *"$sender_lower"* ]]; then
      echo "$h"
      return
    fi
  done <<< "$hosts"

  # No match found — return sender as-is
  echo "$sender"
}

auto_update_ssh_method() {
  local addr="$1"
  # Update config so future calls skip the failed tailscale attempt
  # Looks up hosts by address since callers pass the address, not the name
  if command -v jq &>/dev/null; then
    jq --arg addr "$addr" \
      '(.hosts | to_entries[] | select(.value.address == $addr) | .key) as $name |
       if $name then .hosts[$name].ssh_method = "standard" else . end' \
      "$CONFIG_FILE" > "$CONFIG_FILE.tmp" && mv "$CONFIG_FILE.tmp" "$CONFIG_FILE"
  else
    CMAIL_CONFIG="$CONFIG_FILE" CMAIL_ADDR="$addr" python3 -c "
import json, os
cfg = os.environ['CMAIL_CONFIG']
with open(cfg, 'r') as f: data = json.load(f)
for name, info in data.get('hosts', {}).items():
    if info.get('address') == os.environ['CMAIL_ADDR']:
        info['ssh_method'] = 'standard'
        break
with open(cfg, 'w') as f: json.dump(data, f, indent=2)
" 2>/dev/null
  fi
}

ssh_exec() {
  local address="$1" method="$2"
  shift 2
  if [[ "$method" == "tailscale" ]]; then
    if tailscale ssh "$address" "$@" 2>/dev/null; then
      return 0
    fi
    auto_update_ssh_method "$address"
  fi
  ssh -o ConnectTimeout=5 -o StrictHostKeyChecking=accept-new "$address" "$@"
}

ssh_pipe() {
  local address="$1" method="$2" remote_cmd="$3"
  if [[ "$method" == "tailscale" ]]; then
    if tailscale ssh "$address" "$remote_cmd" 2>/dev/null; then
      return 0
    fi
    auto_update_ssh_method "$address"
  fi
  ssh -o ConnectTimeout=5 -o StrictHostKeyChecking=accept-new "$address" "$remote_cmd"
}

# --- Commands ---

cmd_setup() {
  ensure_config

  local CLAUDE_SETTINGS="$HOME/.claude/settings.json"
  local HOOKS_DIR
  HOOKS_DIR="$(cd "$(dirname "$0")" && pwd)/hooks"
  local STATUSLINE_SCRIPT="$HOME/.claude/statusline-command.sh"

  echo "╔══════════════════════════════════════╗"
  echo "║           cmail setup                ║"
  echo "╚══════════════════════════════════════╝"
  echo ""

  # --- 1. Identity ---
  echo "── Step 1/6: Identity ──"
  echo ""
  local identity
  identity="$(json_get "$CONFIG_FILE" '.identity')"
  echo "  Your identity is how other machines see you."
  echo "  Current: $identity"
  read -r -p "  New identity (Enter to keep): " new_identity </dev/tty 2>/dev/null || new_identity=""
  if [[ -n "$new_identity" ]]; then
    if command -v jq &>/dev/null; then
      jq --arg id "$new_identity" '.identity = $id' "$CONFIG_FILE" > "$CONFIG_FILE.tmp" && mv "$CONFIG_FILE.tmp" "$CONFIG_FILE"
    else
      CMAIL_CONFIG="$CONFIG_FILE" CMAIL_IDENTITY="$new_identity" python3 -c "
import json, os
cfg = os.environ['CMAIL_CONFIG']
with open(cfg, 'r') as f: data = json.load(f)
data['identity'] = os.environ['CMAIL_IDENTITY']
with open(cfg, 'w') as f: json.dump(data, f, indent=2)
"
    fi
    identity="$new_identity"
    echo "  Set to: $identity"
  else
    echo "  Keeping: $identity"
  fi
  echo ""

  # --- 2. Hosts ---
  echo "── Step 2/6: Remote Hosts ──"
  echo ""

  # Show existing hosts
  local existing_hosts=""
  if command -v jq &>/dev/null; then
    existing_hosts="$(jq -r '.hosts | keys[]' "$CONFIG_FILE" 2>/dev/null)" || true
  else
    existing_hosts="$(CMAIL_CONFIG="$CONFIG_FILE" python3 -c "
import json, os
with open(os.environ['CMAIL_CONFIG']) as f: data = json.load(f)
for k in data.get('hosts', {}): print(k)
" 2>/dev/null)" || true
  fi

  if [[ -n "$existing_hosts" ]]; then
    echo "  Already configured:"
    while IFS= read -r h; do
      local addr
      addr="$(get_host_address "$h")"
      local method
      method="$(get_host_ssh_method "$h")"
      echo "    $h -> $addr ($method)"
    done <<< "$existing_hosts"
    echo ""
  fi

  # Auto-discover Tailscale peers
  local discovered=false
  if command -v tailscale &>/dev/null; then
    echo "  Scanning Tailscale network..."
    local self_host
    self_host="$(tailscale status --json 2>/dev/null | jq -r '.Self.HostName // empty' 2>/dev/null)" || true
    self_host="$(echo "$self_host" | tr '[:upper:]' '[:lower:]')"

    local peers=""
    if command -v jq &>/dev/null; then
      peers="$(tailscale status --json 2>/dev/null | jq -r '
        .Peer | to_entries[] |
        select(.value.OS != "iOS" and .value.OS != "android") |
        "\(.value.HostName)\t\(.value.TailscaleIPs[0])\t\(.value.OS)\t\(.value.Online)"
      ' 2>/dev/null)" || true
    fi

    if [[ -n "$peers" ]]; then
      # Build arrays of discoverable peers (exclude self and already-configured)
      local peer_names=() peer_ips=() peer_info=()
      while IFS=$'\t' read -r p_name p_ip p_os p_online; do
        local p_lower
        p_lower="$(echo "$p_name" | tr '[:upper:]' '[:lower:]')"
        # Skip self
        [[ "$p_lower" == "$self_host" ]] && continue
        [[ "$p_lower" == "$identity" ]] && continue
        # Skip already configured
        local already=false
        if [[ -n "$existing_hosts" ]]; then
          while IFS= read -r eh; do
            [[ "$(echo "$eh" | tr '[:upper:]' '[:lower:]')" == "$p_lower" ]] && { already=true; break; }
          done <<< "$existing_hosts"
        fi
        [[ "$already" == true ]] && continue

        local status_str="offline"
        [[ "$p_online" == "true" ]] && status_str="online"
        peer_names+=("$p_lower")
        peer_ips+=("$p_ip")
        peer_info+=("$p_name ($p_os, $status_str, $p_ip)")
      done <<< "$peers"

      if [[ ${#peer_names[@]} -gt 0 ]]; then
        discovered=true
        echo ""
        echo "  Found ${#peer_names[@]} host(s) on your Tailscale network:"
        echo ""
        for i in "${!peer_info[@]}"; do
          echo "    $((i+1))) ${peer_info[$i]}"
        done
        echo "    0) Skip — don't add any"
        echo ""
        echo "  Enter numbers to add, separated by spaces (e.g. 1 3):"
        read -r -p "  > " selections </dev/tty 2>/dev/null || selections=""

        for sel in $selections; do
          [[ "$sel" == "0" ]] && break
          local idx=$((sel - 1))
          if [[ $idx -ge 0 && $idx -lt ${#peer_names[@]} ]]; then
            local sel_name="${peer_names[$idx]}"
            local sel_ip="${peer_ips[$idx]}"

            if command -v jq &>/dev/null; then
              jq --arg name "$sel_name" --arg addr "$sel_name" --arg method "tailscale" \
                '.hosts[$name] = {"address": $addr, "ssh_method": $method}' "$CONFIG_FILE" > "$CONFIG_FILE.tmp" && mv "$CONFIG_FILE.tmp" "$CONFIG_FILE"
            else
              CMAIL_CONFIG="$CONFIG_FILE" CMAIL_HOST="$sel_name" python3 -c "
import json, os
cfg = os.environ['CMAIL_CONFIG']
host = os.environ['CMAIL_HOST']
with open(cfg, 'r') as f: data = json.load(f)
data.setdefault('hosts', {})[host] = {'address': host, 'ssh_method': 'tailscale'}
with open(cfg, 'w') as f: json.dump(data, f, indent=2)
"
            fi

            echo "  Testing $sel_name..."
            if ssh_exec "$sel_name" "tailscale" "echo ok" &>/dev/null; then
              echo "    Added: $sel_name (connected!)"
            else
              echo "    Added: $sel_name (could not connect — check Tailscale SSH)"
            fi
          fi
        done
      else
        echo "  All Tailscale peers already configured."
      fi
    else
      echo "  No peers found on Tailscale network."
    fi
  else
    echo "  Tailscale not found — skipping auto-discovery."
  fi

  # Offer manual entry as fallback
  echo ""
  echo "  Add a host manually? (e.g. non-Tailscale SSH host)"
  read -r -p "  Host name (Enter to skip): " host_name </dev/tty 2>/dev/null || host_name=""
  while [[ -n "$host_name" ]]; do
    read -r -p "  Address (hostname or IP): " host_addr </dev/tty 2>/dev/null || host_addr=""
    [[ -z "$host_addr" ]] && { echo "  Address required, skipping."; break; }

    echo "  SSH method:"
    echo "    1) tailscale — uses 'tailscale ssh' (no keys needed)"
    echo "    2) standard  — uses regular 'ssh' (needs keys/password)"
    read -r -p "  Choose [1/2] (default: 1): " method_choice </dev/tty 2>/dev/null || method_choice=""
    local host_method="tailscale"
    [[ "$method_choice" == "2" ]] && host_method="standard"

    if command -v jq &>/dev/null; then
      jq --arg name "$host_name" --arg addr "$host_addr" --arg method "$host_method" \
        '.hosts[$name] = {"address": $addr, "ssh_method": $method}' "$CONFIG_FILE" > "$CONFIG_FILE.tmp" && mv "$CONFIG_FILE.tmp" "$CONFIG_FILE"
    else
      CMAIL_CONFIG="$CONFIG_FILE" CMAIL_HOST="$host_name" CMAIL_ADDR="$host_addr" CMAIL_METHOD="$host_method" python3 -c "
import json, os
cfg = os.environ['CMAIL_CONFIG']
with open(cfg, 'r') as f: data = json.load(f)
data.setdefault('hosts', {})[os.environ['CMAIL_HOST']] = {
    'address': os.environ['CMAIL_ADDR'], 'ssh_method': os.environ['CMAIL_METHOD']
}
with open(cfg, 'w') as f: json.dump(data, f, indent=2)
"
    fi
    echo "  Added: $host_name -> $host_addr ($host_method)"

    read -r -p "  Add another? Host name (Enter to skip): " host_name </dev/tty 2>/dev/null || host_name=""
  done

  # --- 3. Hooks ---
  echo "── Step 3/6: Claude Code Hooks ──"
  echo ""
  echo "  Hooks let Claude auto-detect new messages."
  echo "    - SessionStart:     check inbox when a session opens"
  echo "    - UserPromptSubmit: check before each response"
  echo "    - Stop:             check after each response, continue if new mail"
  echo ""

  local hooks_installed=false
  if [[ -f "$CLAUDE_SETTINGS" ]] && command -v jq &>/dev/null; then
    if jq -r '.hooks | .. | .command? // empty' "$CLAUDE_SETTINGS" 2>/dev/null | grep -q "cmail"; then
      echo "  Hooks are already installed."
      hooks_installed=true
    fi
  fi

  if [[ "$hooks_installed" == false ]]; then
    if [[ ! -f "$CLAUDE_SETTINGS" ]]; then
      echo "  No Claude Code settings found ($CLAUDE_SETTINGS)."
      echo "  Skipping — you can add hooks manually later."
    elif ! command -v jq &>/dev/null; then
      echo "  jq not found — needed to edit settings. Install jq and re-run setup."
    else
      read -r -p "  Install hooks now? [Y/n] " hook_confirm </dev/tty 2>/dev/null || hook_confirm="y"
      if [[ ! "$hook_confirm" =~ ^[Nn] ]]; then
        local session_start="$HOOKS_DIR/session-start.sh"
        local user_prompt="$HOOKS_DIR/user-prompt-submit.sh"
        local stop_hook="$HOOKS_DIR/stop.sh"
        local tmp="$CLAUDE_SETTINGS.tmp"

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

        echo "  Hooks installed!"
      else
        echo "  Skipped. Run 'cmail setup' again to install later."
      fi
    fi
  fi
  echo ""

  # --- 4. Status line ---
  echo "── Step 4/6: Status Line ──"
  echo ""
  echo "  Show inbox count in Claude Code's status line: (3) cmail"
  echo ""

  local statusline_done=false
  if [[ -f "$STATUSLINE_SCRIPT" ]]; then
    if grep -qF "cmail" "$STATUSLINE_SCRIPT" 2>/dev/null; then
      echo "  cmail is already in your status line."
      statusline_done=true
    fi
  fi

  if [[ "$statusline_done" == false ]]; then
    if [[ -f "$STATUSLINE_SCRIPT" ]]; then
      read -r -p "  Add cmail count to your existing status line? [Y/n] " sl_confirm </dev/tty 2>/dev/null || sl_confirm="y"
      if [[ ! "$sl_confirm" =~ ^[Nn] ]]; then
        cat >> "$STATUSLINE_SCRIPT" <<'CMAIL_EOF'

# cmail-statusline-start
_cmail_count=$(ls -1 "$HOME/.cmail/inbox/"*.json 2>/dev/null | wc -l | tr -d ' ')
if (( _cmail_count > 0 )); then
    _cmail_info=" \033[38;2;128;128;128m|\033[0m \033[1m(${_cmail_count})\033[22m cmail"
else
    _cmail_info=" \033[38;2;128;128;128m|\033[0m \033[38;2;128;128;128m(0) cmail\033[0m"
fi
# cmail-statusline-end
CMAIL_EOF
        echo "  Added! You may need to add \${_cmail_info} to your output line."
      else
        echo "  Skipped."
      fi
    else
      echo "  No statusline script found at $STATUSLINE_SCRIPT."
      echo "  See README for manual setup instructions."
    fi
  fi
  echo ""

  # --- 5. Watcher ---
  echo "── Step 5/6: Inbox Watcher ──"
  echo ""

  local watcher_running=false
  local pidfile="$COMMS_DIR/.watch.pid"
  if [[ -f "$pidfile" ]] && kill -0 "$(cat "$pidfile")" 2>/dev/null; then
    echo "  Watcher is running (PID: $(cat "$pidfile"))."
    watcher_running=true
  else
    echo "  Watcher is not running."
    read -r -p "  Start it now? [Y/n] " watch_confirm </dev/tty 2>/dev/null || watch_confirm="y"
    if [[ ! "$watch_confirm" =~ ^[Nn] ]]; then
      cmd_watch --daemon &
      sleep 1
      echo "  Watcher started."
      watcher_running=true
    fi
  fi

  # Check shell profile
  local SHELL_RC=""
  if [[ -f "$HOME/.zshrc" ]]; then
    SHELL_RC="$HOME/.zshrc"
  elif [[ -f "$HOME/.bashrc" ]]; then
    SHELL_RC="$HOME/.bashrc"
  fi

  if [[ -n "$SHELL_RC" ]]; then
    if grep -qF "cmail watch --daemon" "$SHELL_RC" 2>/dev/null; then
      echo "  Auto-start is configured in $SHELL_RC."
    else
      read -r -p "  Add auto-start to $SHELL_RC? [Y/n] " auto_confirm </dev/tty 2>/dev/null || auto_confirm="y"
      if [[ ! "$auto_confirm" =~ ^[Nn] ]]; then
        echo "" >> "$SHELL_RC"
        echo "# cmail: auto-start inbox watcher" >> "$SHELL_RC"
        echo 'command -v cmail &>/dev/null && cmail watch --daemon &>/dev/null &' >> "$SHELL_RC"
        echo "  Added to $SHELL_RC."
      fi
    fi
  fi
  echo ""

  # --- 6. Agent ---
  echo "── Step 6/6: Auto-Respond Agent ──"
  echo ""
  echo "  When enabled, the agent uses 'claude --print' to automatically"
  echo "  read and reply to incoming messages — even when no user is active."
  echo ""

  local agent_enabled=false
  if [[ -f "$COMMS_DIR/.agent-enabled" ]]; then
    echo "  Agent is currently: ENABLED"
    agent_enabled=true
    read -r -p "  Keep it enabled? [Y/n] " agent_confirm </dev/tty 2>/dev/null || agent_confirm="y"
    if [[ "$agent_confirm" =~ ^[Nn] ]]; then
      rm -f "$COMMS_DIR/.agent-enabled"
      agent_enabled=false
      echo "  Agent disabled."
    fi
  else
    echo "  Agent is currently: DISABLED"
    read -r -p "  Enable auto-respond agent? [Y/n] " agent_confirm </dev/tty 2>/dev/null || agent_confirm="y"
    if [[ ! "$agent_confirm" =~ ^[Nn] ]]; then
      touch "$COMMS_DIR/.agent-enabled"
      agent_enabled=true
      echo "  Agent enabled!"
    else
      echo "  Skipped. Run 'cmail agent on' to enable later."
    fi
  fi
  echo ""

  # --- Summary ---
  echo "╔══════════════════════════════════════╗"
  echo "║          Setup complete!             ║"
  echo "╚══════════════════════════════════════╝"
  echo ""
  echo "  Identity:    $identity"

  # Count hosts
  local host_count=0
  if command -v jq &>/dev/null; then
    host_count=$(jq '.hosts | length' "$CONFIG_FILE" 2>/dev/null || echo 0)
  fi
  echo "  Hosts:       $host_count configured"

  if [[ "$hooks_installed" == true ]] || { [[ -f "$CLAUDE_SETTINGS" ]] && command -v jq &>/dev/null && jq -r '.hooks | .. | .command? // empty' "$CLAUDE_SETTINGS" 2>/dev/null | grep -q "cmail"; }; then
    echo "  Hooks:       installed"
  else
    echo "  Hooks:       not installed"
  fi

  if [[ -f "$STATUSLINE_SCRIPT" ]] && grep -qF "cmail" "$STATUSLINE_SCRIPT" 2>/dev/null; then
    echo "  Status line: configured"
  else
    echo "  Status line: not configured"
  fi

  if [[ "$watcher_running" == true ]]; then
    echo "  Watcher:     running"
  else
    echo "  Watcher:     not running"
  fi

  if [[ "$agent_enabled" == true ]]; then
    echo "  Agent:       enabled"
  else
    echo "  Agent:       disabled"
  fi

  echo ""
  echo "  Try: cmail send <host> \"hello from $identity\""
  echo ""
}

cmd_send() {
  ensure_config
  local host="" subject="" message="" in_reply_to="" thread_id=""

  while [[ $# -gt 0 ]]; do
    case "$1" in
      --subject) subject="$2"; shift 2 ;;
      --in-reply-to) in_reply_to="$2"; shift 2 ;;
      --thread-id) thread_id="$2"; shift 2 ;;
      *)
        if [[ -z "$host" ]]; then
          host="$1"
        else
          message="$1"
        fi
        shift
        ;;
    esac
  done

  if [[ -z "$host" || -z "$message" ]]; then
    echo "Usage: cmail send <host> [--subject <subject>] <message>" >&2
    exit 1
  fi

  local address
  address="$(get_host_address "$host")"
  if [[ -z "$address" ]]; then
    address="$host"
  fi

  local method
  method="$(get_host_ssh_method "$host")"

  local identity
  identity="$(get_identity)"
  local msg_id
  msg_id="$(generate_uuid)"
  local timestamp
  timestamp="$(get_timestamp)"
  local file_timestamp
  file_timestamp="$(get_filename_timestamp)"
  local short_id="${msg_id:0:6}"
  local safe_identity
  safe_identity="$(sanitize_filename_part "$identity")"
  local filename="${file_timestamp}-${safe_identity}-${short_id}.json"

  [[ -z "$thread_id" ]] && thread_id="$msg_id"

  local json_msg
  if command -v jq &>/dev/null; then
    json_msg="$(jq -n \
      --arg id "$msg_id" \
      --arg from "$identity" \
      --arg to "$host" \
      --arg ts "$timestamp" \
      --arg subj "$subject" \
      --arg body "$message" \
      --arg reply "$in_reply_to" \
      --arg thread "$thread_id" \
      '{id: $id, from: $from, to: $to, timestamp: $ts, subject: $subj, body: $body, in_reply_to: ($reply | if . == "" then null else . end), thread_id: $thread}'
    )"
  else
    json_msg="$(CMAIL_ID="$msg_id" CMAIL_FROM="$identity" CMAIL_TO="$host" \
      CMAIL_TS="$timestamp" CMAIL_SUBJ="$subject" CMAIL_BODY="$message" \
      CMAIL_REPLY="$in_reply_to" CMAIL_THREAD="$thread_id" python3 -c "
import json, os
msg = {
    'id': os.environ['CMAIL_ID'],
    'from': os.environ['CMAIL_FROM'],
    'to': os.environ['CMAIL_TO'],
    'timestamp': os.environ['CMAIL_TS'],
    'subject': os.environ['CMAIL_SUBJ'],
    'body': os.environ['CMAIL_BODY'],
    'in_reply_to': os.environ['CMAIL_REPLY'] or None,
    'thread_id': os.environ['CMAIL_THREAD']
}
print(json.dumps(msg, indent=2))
")"
  fi

  echo "$json_msg" | ssh_pipe "$address" "$method" "mkdir -p ~/.cmail/inbox && cat > ~/.cmail/inbox/$filename && touch ~/.cmail/.has_unread"

  # Save to local outbox
  echo "$json_msg" > "$OUTBOX_DIR/$filename"

  echo "Message sent to $host (id: $msg_id)"
}

cmd_inbox() {
  ensure_config
  local subcmd=""
  local if_new=false

  # Parse subcommand and flags
  case "${1:-}" in
    show)    subcmd="show"; shift ;;
    clear)   subcmd="clear"; shift ;;
    --if-new) subcmd="show"; if_new=true; shift ;;
    -h|--help|help) show_inbox_help; return 0 ;;
    -*) ;; # unknown flags
    "") ;;
    *) subcmd="$1"; shift ;;
  esac

  # No subcommand = show help (Mullvad-style)
  if [[ -z "$subcmd" ]]; then
    show_inbox_help
    return 0
  fi

  case "$subcmd" in
    show)
      # Parse show subcommand and flags
      local show_subcmd=""
      local detail_count=1

      while [[ $# -gt 0 ]]; do
        case "$1" in
          detail)  show_subcmd="detail"; shift ;;
          --if-new) if_new=true; shift ;;
          -h|--help|help) show_show_help; return 0 ;;
          -[0-9]*) detail_count="${1#-}"; show_subcmd="detail"; shift ;;
          *) shift ;;
        esac
      done

      if [[ "$if_new" == true ]]; then
        if [[ ! -f "$UNREAD_MARKER" ]]; then
          echo "No new messages."
          return 0
        fi
      fi

      local files
      files="$(ls -1 "$INBOX_DIR"/*.json 2>/dev/null | sort -r)" || true

      if [[ -z "$files" ]]; then
        echo "Inbox is empty."
        return 0
      fi

      if [[ "$show_subcmd" == "detail" ]]; then
        # Show full message contents for the N most recent
        local shown=0
        while IFS= read -r file; do
          (( shown >= detail_count )) && break
          local id from to timestamp subject body
          id="$(json_get "$file" '.id')"
          from="$(json_get "$file" '.from')"
          to="$(json_get "$file" '.to')"
          timestamp="$(json_get "$file" '.timestamp')"
          subject="$(json_get "$file" '.subject')"
          body="$(json_get "$file" '.body')"
          local short_id="${id:0:8}"

          (( shown > 0 )) && echo ""
          echo "=== Message [$short_id] ==="
          echo "From:    $from"
          echo "To:      $to"
          echo "Date:    $timestamp"
          [[ -n "$subject" && "$subject" != "null" ]] && echo "Subject: $subject"
          echo "---"
          echo "$body"
          shown=$((shown + 1))
        done <<< "$files"

        local total
        total="$(echo "$files" | wc -l | tr -d ' ')"
        if (( total > shown )); then
          echo ""
          echo "(showing $shown of $total — use -$total to see all)"
        fi
      else
        # Default: summary list
        local total
        total="$(echo "$files" | wc -l | tr -d ' ')"
        echo "=== Inbox ($total messages) ==="
        echo ""
        while IFS= read -r file; do
          local id from subject timestamp
          id="$(json_get "$file" '.id')"
          from="$(json_get "$file" '.from')"
          subject="$(json_get "$file" '.subject')"
          timestamp="$(json_get "$file" '.timestamp')"
          local short_id="${id:0:8}"
          local display_subject=""
          [[ -n "$subject" && "$subject" != "null" && "$subject" != "" ]] && display_subject=" — $subject"
          echo "[$short_id] $timestamp  from: $from$display_subject"
        done <<< "$files"
        echo ""
        echo "Use 'cmail inbox show detail' to read the latest, or 'detail -N' for N messages."
      fi
      ;;

    clear)
      local count
      count="$(ls -1 "$INBOX_DIR"/*.json 2>/dev/null | wc -l | tr -d ' ')" || count=0
      if (( count == 0 )); then
        echo "Inbox is already empty."
        return 0
      fi

      echo "WARNING: This will permanently delete $count message(s) from your inbox."
      read -r -p "Are you sure? [y/N] " confirm </dev/tty 2>/dev/null || confirm=""
      if [[ "$confirm" =~ ^[Yy]$ ]]; then
        rm -f "$INBOX_DIR"/*.json
        rm -f "$UNREAD_MARKER"
        echo "Inbox cleared ($count messages removed)."
      else
        echo "Aborted."
      fi
      ;;

    *)
      echo "Unknown inbox subcommand: $subcmd"
      echo ""
      show_inbox_help
      return 1
      ;;
  esac
}

cmd_read() {
  ensure_config
  local target_id="$1"

  if [[ -z "$target_id" ]]; then
    echo "Usage: cmail read <message-id>" >&2
    exit 1
  fi

  local found=""
  for file in "$INBOX_DIR"/*.json; do
    [[ -f "$file" ]] || continue
    local id
    id="$(json_get "$file" '.id')"
    if [[ "$id" == "$target_id"* ]]; then
      found="$file"
      break
    fi
  done

  if [[ -z "$found" ]]; then
    echo "Message not found: $target_id" >&2
    exit 1
  fi

  local id from to timestamp subject body in_reply_to thread_id
  id="$(json_get "$found" '.id')"
  from="$(json_get "$found" '.from')"
  to="$(json_get "$found" '.to')"
  timestamp="$(json_get "$found" '.timestamp')"
  subject="$(json_get "$found" '.subject')"
  body="$(json_get "$found" '.body')"
  in_reply_to="$(json_get "$found" '.in_reply_to')"
  thread_id="$(json_get "$found" '.thread_id')"

  echo "=== Message ==="
  echo "ID:        $id"
  echo "From:      $from"
  echo "To:        $to"
  echo "Date:      $timestamp"
  [[ -n "$subject" && "$subject" != "null" ]] && echo "Subject:   $subject"
  [[ -n "$in_reply_to" && "$in_reply_to" != "null" ]] && echo "Reply-To:  $in_reply_to"
  [[ -n "$thread_id" && "$thread_id" != "null" ]] && echo "Thread:    $thread_id"
  echo "---"
  echo "$body"

  # Clear unread marker if no other unread messages
  # (Simple approach: remove marker, let watcher re-create if needed)
  rm -f "$UNREAD_MARKER"
}

cmd_reply() {
  local target_id="${1:-}"
  shift || true
  local message=""
  local subject=""

  while [[ $# -gt 0 ]]; do
    case "$1" in
      --subject) subject="$2"; shift 2 ;;
      *)
        message="$1"
        shift
        ;;
    esac
  done

  if [[ -z "$target_id" || -z "$message" ]]; then
    echo "Usage: cmail reply <message-id> [--subject <subject>] <message>" >&2
    exit 1
  fi

  # Find original message
  local found=""
  for file in "$INBOX_DIR"/*.json "$OUTBOX_DIR"/*.json; do
    [[ -f "$file" ]] || continue
    local id
    id="$(json_get "$file" '.id')"
    if [[ "$id" == "$target_id"* ]]; then
      found="$file"
      break
    fi
  done

  if [[ -z "$found" ]]; then
    echo "Original message not found: $target_id" >&2
    exit 1
  fi

  local orig_from orig_thread_id orig_subject
  orig_from="$(json_get "$found" '.from')"
  orig_thread_id="$(json_get "$found" '.thread_id')"
  orig_subject="$(json_get "$found" '.subject')"

  # Resolve sender identity to a configured host name
  local reply_host
  reply_host="$(resolve_sender_to_host "$orig_from")"

  [[ -z "$subject" && -n "$orig_subject" && "$orig_subject" != "null" ]] && subject="Re: $orig_subject"

  cmd_send "$reply_host" --subject "$subject" --in-reply-to "$target_id" --thread-id "$orig_thread_id" "$message"
}

cmd_hosts() {
  ensure_config
  echo "=== Configured Hosts ==="
  echo ""

  local hosts_json
  if command -v jq &>/dev/null; then
    hosts_json="$(jq -r '.hosts | to_entries[] | "\(.key)\t\(.value.address)\t\(.value.ssh_method // "tailscale")"' "$CONFIG_FILE" 2>/dev/null)" || true
  else
    hosts_json="$(CMAIL_CONFIG="$CONFIG_FILE" python3 -c "
import json, os
with open(os.environ['CMAIL_CONFIG']) as f: data = json.load(f)
for name, info in data.get('hosts', {}).items():
    print(f\"{name}\t{info['address']}\t{info.get('ssh_method', 'tailscale')}\")
" 2>/dev/null)" || true
  fi

  if [[ -z "$hosts_json" ]]; then
    echo "No hosts configured."
    echo ""
  else
    printf "  %-20s %-30s %-12s %s\n" "NAME" "ADDRESS" "METHOD" "STATUS"
    printf "  %-20s %-30s %-12s %s\n" "────" "───────" "──────" "──────"
    while IFS=$'\t' read -r name address method; do
      local status="testing..."
      if ssh_exec "$address" "$method" "echo ok" &>/dev/null; then
        status="reachable"
      else
        status="unreachable"
      fi
      printf "  %-20s %-30s %-12s %s\n" "$name" "$address" "$method" "$status"
    done <<< "$hosts_json"
    echo ""
  fi

  # Scan Tailscale for new hosts not yet in config
  if command -v tailscale &>/dev/null && command -v jq &>/dev/null; then
    local self_host
    self_host="$(tailscale status --json 2>/dev/null | jq -r '.Self.HostName // empty' 2>/dev/null | tr '[:upper:]' '[:lower:]')" || true
    local identity
    identity="$(json_get "$CONFIG_FILE" '.identity' 2>/dev/null | tr '[:upper:]' '[:lower:]')" || true

    local peers
    peers="$(tailscale status --json 2>/dev/null | jq -r '
      .Peer | to_entries[] |
      select(.value.OS != "iOS" and .value.OS != "android") |
      "\(.value.HostName)\t\(.value.TailscaleIPs[0])\t\(.value.OS)\t\(.value.Online)"
    ' 2>/dev/null)" || true

    if [[ -n "$peers" ]]; then
      local existing_lower=""
      if [[ -n "$hosts_json" ]]; then
        existing_lower="$(echo "$hosts_json" | cut -f1 | tr '[:upper:]' '[:lower:]')"
      fi

      local new_names=() new_info=()
      while IFS=$'\t' read -r p_name p_ip p_os p_online; do
        local p_lower
        p_lower="$(echo "$p_name" | tr '[:upper:]' '[:lower:]')"
        [[ "$p_lower" == "$self_host" ]] && continue
        [[ "$p_lower" == "$identity" ]] && continue
        echo "$existing_lower" | grep -qx "$p_lower" 2>/dev/null && continue

        local status_str="offline"
        [[ "$p_online" == "true" ]] && status_str="online"
        new_names+=("$p_lower")
        new_info+=("$p_name ($p_os, $status_str, $p_ip)")
      done <<< "$peers"

      if [[ ${#new_names[@]} -gt 0 ]]; then
        echo "=== New hosts on Tailscale ==="
        echo ""
        for i in "${!new_info[@]}"; do
          echo "  $((i+1))) ${new_info[$i]}"
        done
        echo "  0) Skip"
        echo ""
        read -r -p "Add hosts (e.g. 1 3): " selections </dev/tty 2>/dev/null || selections=""

        for sel in $selections; do
          [[ "$sel" == "0" ]] && break
          local idx=$((sel - 1))
          if [[ $idx -ge 0 && $idx -lt ${#new_names[@]} ]]; then
            local sel_name="${new_names[$idx]}"
            if command -v jq &>/dev/null; then
              jq --arg name "$sel_name" --arg addr "$sel_name" --arg method "tailscale" \
                '.hosts[$name] = {"address": $addr, "ssh_method": $method}' "$CONFIG_FILE" > "$CONFIG_FILE.tmp" && mv "$CONFIG_FILE.tmp" "$CONFIG_FILE"
            else
              CMAIL_CONFIG="$CONFIG_FILE" CMAIL_HOST="$sel_name" python3 -c "
import json, os
cfg = os.environ['CMAIL_CONFIG']
host = os.environ['CMAIL_HOST']
with open(cfg, 'r') as f: data = json.load(f)
data.setdefault('hosts', {})[host] = {'address': host, 'ssh_method': 'tailscale'}
with open(cfg, 'w') as f: json.dump(data, f, indent=2)
"
            fi
            echo "  Added: $sel_name (tailscale)"
          fi
        done
      fi
    fi
  fi
}

notify_new_message() {
  local file="$1"
  local from=""
  # Small delay + retry — fswatch fires before the file is fully written
  local attempt
  for attempt in 1 2 3; do
    if [[ -f "$file" ]]; then
      from="$(json_get "$file" '.from' 2>/dev/null)" || true
      [[ -n "$from" && "$from" != "null" ]] && break
    fi
    sleep 0.2
  done
  touch "$UNREAD_MARKER"
  # Desktop notification (platform-dependent, silently skipped if unavailable)
  osascript -e "display notification \"New message from ${from:-unknown}\" with title \"cmail\"" 2>/dev/null \
    || notify-send "cmail" "New message from ${from:-unknown}" 2>/dev/null \
    || true
  echo "New message received: $(basename "$file")"

  # Trigger cmail-agent if enabled
  local agent_script="$SCRIPT_DIR/cmail-agent.sh"
  if [[ -f "$COMMS_DIR/.agent-enabled" ]] && [[ -x "$agent_script" ]]; then
    mkdir -p "$COMMS_DIR/.agent"
    "$agent_script" >> "$COMMS_DIR/.agent/agent.log" 2>&1 &
  fi
}

cmd_watch_stop() {
  local pidfile="$COMMS_DIR/.watch.pid"
  if [[ -f "$pidfile" ]]; then
    local pid
    pid="$(cat "$pidfile")"
    if kill -0 "$pid" 2>/dev/null; then
      # Kill the watcher and its fswatch child
      kill "$pid" 2>/dev/null
      # Also kill any fswatch watching our inbox
      pgrep -f "fswatch.*\\.cmail/inbox" 2>/dev/null | xargs kill 2>/dev/null || true
      rm -f "$pidfile"
      sleep 0.3
      echo "Watcher stopped (was PID: $pid)."
      return 0
    fi
    rm -f "$pidfile"
  fi
  echo "Watcher is not running."
  return 0
}

cmd_watch() {
  local daemon=false
  local subcmd=""

  while [[ $# -gt 0 ]]; do
    case "$1" in
      --daemon) daemon=true; shift ;;
      stop)    subcmd="stop"; shift ;;
      restart) subcmd="restart"; shift ;;
      -h|--help|help) show_watch_help; return 0 ;;
      *) shift ;;
    esac
  done

  if [[ "$subcmd" == "stop" ]]; then
    cmd_watch_stop
    return 0
  fi

  if [[ "$subcmd" == "restart" ]]; then
    cmd_watch_stop
    echo "Starting fresh watcher..."
    # Re-exec ourselves with --daemon
    cmd_watch --daemon &
    sleep 0.5
    local pidfile="$COMMS_DIR/.watch.pid"
    if [[ -f "$pidfile" ]] && kill -0 "$(cat "$pidfile")" 2>/dev/null; then
      echo "Watcher restarted (PID: $(cat "$pidfile"))."
    else
      echo "Warning: watcher may not have started correctly."
    fi
    return 0
  fi

  ensure_dirs

  # Prevent duplicate watchers — always check PID file
  local pidfile="$COMMS_DIR/.watch.pid"
  if [[ -f "$pidfile" ]] && kill -0 "$(cat "$pidfile")" 2>/dev/null; then
    if [[ "$daemon" == true ]]; then
      return 0
    else
      echo "Watcher already running (PID: $(cat "$pidfile")). Stop it first or use --daemon."
      return 1
    fi
  fi
  echo $$ > "$pidfile"
  trap 'rm -f "$pidfile"' EXIT

  if [[ "$daemon" != true ]]; then
    echo "Watching for new messages in $INBOX_DIR ..."
    echo "Press Ctrl+C to stop."
  fi

  local _notified_files=""
  if command -v fswatch &>/dev/null; then
    echo "(using fswatch)"
    fswatch -0 "$INBOX_DIR" | while IFS= read -r -d '' event; do
      [[ "$event" == *.json ]] || continue
      # Deduplicate — fswatch fires multiple events per file (create, modify, etc.)
      local basename_ev
      basename_ev="$(basename "$event")"
      if [[ "$_notified_files" == *"|$basename_ev|"* ]]; then
        continue
      fi
      _notified_files+="|$basename_ev|"
      notify_new_message "$event"
    done
  elif command -v inotifywait &>/dev/null; then
    echo "(using inotifywait)"
    inotifywait -m -e create --format '%w%f' "$INBOX_DIR" | while IFS= read -r event; do
      [[ "$event" == *.json ]] || continue
      notify_new_message "$event"
    done
  else
    echo "(using polling — install fswatch or inotify-tools for instant detection)"
    local poll_interval="${CMAIL_POLL_INTERVAL:-5}"
    local known_files
    known_files="$(ls -1 "$INBOX_DIR"/*.json 2>/dev/null | sort)" || true
    while true; do
      sleep "$poll_interval"
      local current_files
      current_files="$(ls -1 "$INBOX_DIR"/*.json 2>/dev/null | sort)" || true
      if [[ "$current_files" != "$known_files" ]]; then
        # Find new files
        local new_files
        new_files="$(comm -13 <(echo "$known_files") <(echo "$current_files"))" || true
        while IFS= read -r file; do
          [[ -n "$file" ]] && notify_new_message "$file"
        done <<< "$new_files"
        known_files="$current_files"
      fi
    done
  fi
}

cmd_agent() {
  local subcmd="${1:-status}"
  local agent_marker="$COMMS_DIR/.agent-enabled"
  local agent_log="$COMMS_DIR/.agent/agent.log"
  local agent_lock="$COMMS_DIR/.agent/.lock"
  local agent_session="$COMMS_DIR/.agent/session_id"

  case "$subcmd" in
    on|enable)
      mkdir -p "$COMMS_DIR/.agent"
      touch "$agent_marker"
      echo "cmail-agent enabled. The watcher will auto-respond to incoming messages."
      echo "  Model: ${CMAIL_AGENT_MODEL:-claude-sonnet-4-5-20250929}"
      echo "  Timeout: ${CMAIL_AGENT_TIMEOUT:-120}s"
      echo "  Log: $agent_log"
      ;;
    off|disable)
      rm -f "$agent_marker"
      echo "cmail-agent disabled."
      ;;
    status)
      if [[ -f "$agent_marker" ]]; then
        echo "cmail-agent: enabled"
      else
        echo "cmail-agent: disabled"
      fi
      if [[ -f "$agent_lock" ]] && kill -0 "$(cat "$agent_lock" 2>/dev/null)" 2>/dev/null; then
        echo "  Status: running (PID: $(cat "$agent_lock"))"
      else
        echo "  Status: idle"
      fi
      if [[ -f "$agent_session" ]]; then
        echo "  Session: $(cat "$agent_session")"
      else
        echo "  Session: none"
      fi
      echo "  Model: ${CMAIL_AGENT_MODEL:-claude-sonnet-4-5-20250929}"
      echo "  Timeout: ${CMAIL_AGENT_TIMEOUT:-120}s"
      if [[ -f "$agent_log" ]]; then
        echo "  Log: $agent_log ($(wc -l < "$agent_log" | tr -d ' ') lines)"
      fi
      ;;
    log|logs)
      if [[ -f "$agent_log" ]]; then
        tail -50 "$agent_log"
      else
        echo "No agent log yet."
      fi
      ;;
    reset)
      rm -f "$agent_session" "$agent_lock"
      echo "Agent session and lock cleared."
      ;;
    run)
      # Manually trigger the agent now
      local agent_script="$SCRIPT_DIR/cmail-agent.sh"
      if [[ -x "$agent_script" ]]; then
        echo "Running cmail-agent..."
        "$agent_script"
      else
        echo "Agent script not found: $agent_script" >&2
        exit 1
      fi
      ;;
    *)
      echo "Usage: cmail agent [on|off|status|log|reset|run]" >&2
      echo ""
      echo "  on      Enable auto-respond (watcher triggers agent on new messages)"
      echo "  off     Disable auto-respond"
      echo "  status  Show agent status"
      echo "  log     Show recent agent log"
      echo "  reset   Clear session and lock"
      echo "  run     Manually trigger agent now"
      ;;
  esac
}

cmd_update() {
  # Walk up from SCRIPT_DIR looking for a .git directory
  find_git_root() {
    local dir="$1"
    while [[ "$dir" != "/" ]]; do
      if [[ -d "$dir/.git" ]]; then
        echo "$dir"
        return 0
      fi
      dir="$(dirname "$dir")"
    done
    return 1
  }

  local repo_dir=""
  # First try from SCRIPT_DIR directly
  repo_dir="$(find_git_root "$SCRIPT_DIR")" || true
  # If not found, try after resolving symlinks
  if [[ -z "$repo_dir" ]]; then
    local resolved
    resolved="$(readlink -f "$SCRIPT_DIR" 2>/dev/null || echo "")"
    if [[ -n "$resolved" ]]; then
      repo_dir="$(find_git_root "$resolved")" || true
    fi
  fi

  if [[ -z "$repo_dir" ]]; then
    echo "Could not find cmail git repo." >&2
    echo "" >&2
    echo "If you installed cmail from a standalone copy, update manually:" >&2
    echo "  git clone https://github.com/ORDIGSEC/cmail.git" >&2
    echo "  cd cmail && ./install.sh" >&2
    return 1
  fi

  echo "Pulling latest code..."
  if (cd "$repo_dir" && git pull); then
    echo ""
    echo "Restarting watcher..."
    cmd_watch restart
  else
    echo "git pull failed." >&2
    return 1
  fi
}

# --- Help text ---

show_usage() {
  echo "cmail — File-based messaging over Tailscale SSH"
  echo ""
  echo "USAGE: cmail <command> [options]"
  echo ""
  echo "COMMANDS:"
  echo "  send      Send a message to a remote host"
  echo "  inbox     List messages in your inbox"
  echo "  read      Read a specific message"
  echo "  reply     Reply to a message (preserves threading)"
  echo "  hosts     List configured hosts and scan for new ones"
  echo "  setup     Interactive setup wizard"
  echo "  watch     Background watcher for incoming messages"
  echo "  agent     Auto-respond agent (uses claude --print)"
  echo "  update    Pull latest code and restart services"
  echo "  deps      Check and install dependencies"
  echo ""
  echo "Run 'cmail <command> --help' for details on a specific command."
}

show_send_help() {
  echo "Send a message to a remote host"
  echo ""
  echo "USAGE: cmail send <host> [options] <message>"
  echo ""
  echo "ARGUMENTS:"
  echo "  <host>       Name of the remote host (as configured)"
  echo "  <message>    Message body text"
  echo ""
  echo "OPTIONS:"
  echo "  --subject <text>   Add a subject line"
  echo "  -h, --help         Show this help"
  echo ""
  echo "EXAMPLES:"
  echo "  cmail send biggirl \"How's the build going?\""
  echo "  cmail send smoke --subject \"Deploy\" \"Ready to push to prod\""
}

show_inbox_help() {
  echo "List or manage messages in your inbox"
  echo ""
  echo "USAGE: cmail inbox <subcommand> [options]"
  echo ""
  echo "SUBCOMMANDS:"
  echo "  show     List messages (has further options, see 'cmail inbox show --help')"
  echo "  clear    Delete all messages (requires confirmation)"
  echo ""
  echo "OPTIONS:"
  echo "  -h, --help   Show this help"
  echo ""
  echo "EXAMPLES:"
  echo "  cmail inbox show"
  echo "  cmail inbox show detail"
  echo "  cmail inbox show --if-new"
  echo "  cmail inbox clear"
}

show_show_help() {
  echo "List messages in your inbox"
  echo ""
  echo "USAGE: cmail inbox show [subcommand] [options]"
  echo ""
  echo "SUBCOMMANDS:"
  echo "  detail       Show full contents of the most recent message"
  echo "  detail -N    Show full contents of the N most recent messages"
  echo ""
  echo "OPTIONS:"
  echo "  --if-new     Only show messages if there are unread ones"
  echo "  -h, --help   Show this help"
  echo ""
  echo "EXAMPLES:"
  echo "  cmail inbox show              List all messages (summary)"
  echo "  cmail inbox show --if-new     List only if new messages exist"
  echo "  cmail inbox show detail       Read the most recent message"
  echo "  cmail inbox show detail -3    Read the 3 most recent messages"
}

show_read_help() {
  echo "Read a specific message"
  echo ""
  echo "USAGE: cmail read <id>"
  echo ""
  echo "ARGUMENTS:"
  echo "  <id>   Message ID or prefix (first 8 chars is enough)"
  echo ""
  echo "OPTIONS:"
  echo "  -h, --help   Show this help"
}

show_reply_help() {
  echo "Reply to a message (preserves threading)"
  echo ""
  echo "USAGE: cmail reply <id> [options] <message>"
  echo ""
  echo "ARGUMENTS:"
  echo "  <id>         Message ID to reply to"
  echo "  <message>    Reply body text"
  echo ""
  echo "OPTIONS:"
  echo "  --subject <text>   Override the subject line"
  echo "  -h, --help         Show this help"
  echo ""
  echo "EXAMPLES:"
  echo "  cmail reply a9c1c8d6 \"Got it, thanks!\""
}

show_hosts_help() {
  echo "List configured hosts and scan for new Tailscale peers"
  echo ""
  echo "USAGE: cmail hosts"
  echo ""
  echo "Shows all configured hosts with connectivity status, then"
  echo "scans the Tailscale network for new hosts you can add."
  echo ""
  echo "OPTIONS:"
  echo "  -h, --help   Show this help"
}

show_watch_help() {
  echo "Background watcher for incoming messages"
  echo ""
  echo "USAGE: cmail watch [subcommand] [options]"
  echo ""
  echo "Watches ~/.cmail/inbox/ for new messages and sends desktop"
  echo "notifications. Triggers the auto-respond agent if enabled."
  echo ""
  echo "SUBCOMMANDS:"
  echo "  stop       Stop the running watcher"
  echo "  restart    Stop and restart the watcher (picks up code changes)"
  echo ""
  echo "OPTIONS:"
  echo "  --daemon     Run silently, exit if already running"
  echo "  -h, --help   Show this help"
  echo ""
  echo "EXAMPLES:"
  echo "  cmail watch              Start watcher interactively"
  echo "  cmail watch --daemon     Start in background (idempotent)"
  echo "  cmail watch restart      Restart after code updates"
  echo "  cmail watch stop         Stop the watcher"
}

show_agent_help() {
  echo "Auto-respond agent (uses claude --print)"
  echo ""
  echo "USAGE: cmail agent <subcommand>"
  echo ""
  echo "SUBCOMMANDS:"
  echo "  on       Enable auto-respond (watcher triggers agent on new messages)"
  echo "  off      Disable auto-respond"
  echo "  status   Show agent status, session, and config"
  echo "  log      Show recent agent log entries"
  echo "  reset    Clear session and lock file"
  echo "  run      Manually trigger agent now"
  echo ""
  echo "OPTIONS:"
  echo "  -h, --help   Show this help"
  echo ""
  echo "ENVIRONMENT:"
  echo "  CMAIL_AGENT_MODEL     Model to use (default: claude-sonnet-4-5-20250929)"
  echo "  CMAIL_AGENT_TIMEOUT   Timeout in seconds (default: 120)"
  echo "  CMAIL_CLAUDE_PATH     Path to claude binary"
}

show_update_help() {
  echo "Pull latest code and restart services"
  echo ""
  echo "USAGE: cmail update"
  echo ""
  echo "Runs 'git pull' in the cmail repo directory, then restarts"
  echo "the watcher so it picks up any code changes."
  echo ""
  echo "OPTIONS:"
  echo "  -h, --help   Show this help"
}

show_deps_help() {
  echo "Check and install dependencies"
  echo ""
  echo "USAGE: cmail deps"
  echo ""
  echo "Checks for required tools (jq, fswatch/inotifywait, ssh,"
  echo "tailscale) and offers to install missing ones."
  echo ""
  echo "OPTIONS:"
  echo "  -h, --help   Show this help"
}

show_setup_help() {
  echo "Interactive setup wizard"
  echo ""
  echo "USAGE: cmail setup"
  echo ""
  echo "Walks through 6 steps:"
  echo "  1. Identity     — set your hostname for messaging"
  echo "  2. Remote Hosts — auto-discover Tailscale peers or add manually"
  echo "  3. Hooks        — install Claude Code hooks for message awareness"
  echo "  4. Status Line  — add inbox count to Claude Code status line"
  echo "  5. Watcher      — start the background inbox watcher"
  echo "  6. Agent        — enable auto-respond via claude --print"
  echo ""
  echo "OPTIONS:"
  echo "  -h, --help   Show this help"
}

# Check if first arg is a help flag
is_help_flag() {
  [[ "${1:-}" == "-h" || "${1:-}" == "--help" || "${1:-}" == "help" ]]
}

# --- Main ---

cmd="${1:-}"
shift || true

# No command = show usage (Mullvad-style, no error)
if [[ -z "$cmd" || "$cmd" == "help" || "$cmd" == "--help" || "$cmd" == "-h" ]]; then
  show_usage
  exit 0
fi

# Auto-check deps on first run (skip for deps to avoid chicken-and-egg)
if [[ "$cmd" != "deps" ]]; then
  check_deps
fi

case "$cmd" in
  setup)
    if is_help_flag "${1:-}"; then show_setup_help; exit 0; fi
    cmd_setup "$@" ;;
  send)
    if is_help_flag "${1:-}" || [[ $# -eq 0 ]]; then show_send_help; exit 0; fi
    cmd_send "$@" ;;
  inbox)
    cmd_inbox "$@" ;;
  read)
    if is_help_flag "${1:-}" || [[ $# -eq 0 ]]; then show_read_help; exit 0; fi
    cmd_read "$@" ;;
  reply)
    if is_help_flag "${1:-}" || [[ $# -eq 0 ]]; then show_reply_help; exit 0; fi
    cmd_reply "$@" ;;
  hosts)
    if is_help_flag "${1:-}"; then show_hosts_help; exit 0; fi
    cmd_hosts "$@" ;;
  watch)
    if is_help_flag "${1:-}"; then show_watch_help; exit 0; fi
    cmd_watch "$@" ;;
  agent)
    if is_help_flag "${1:-}" || [[ $# -eq 0 ]]; then show_agent_help; exit 0; fi
    cmd_agent "$@" ;;
  update)
    if is_help_flag "${1:-}"; then show_update_help; exit 0; fi
    cmd_update "$@" ;;
  deps)
    if is_help_flag "${1:-}"; then show_deps_help; exit 0; fi
    cmd_deps "$@" ;;
  *)
    echo "Unknown command: $cmd"
    echo ""
    show_usage
    exit 1
    ;;
esac
