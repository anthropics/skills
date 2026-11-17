#!/usr/bin/env bash
# permission-auditor.sh — Check file and system permissions for security issues
# Part of arc-sentinel OpenClaw security skill

set -uo pipefail

VERSION="1.0.0"
SCRIPT_NAME="$(basename "$0")"

RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
BOLD='\033[1m'
RESET='\033[0m'

FINDINGS=0
CRITICAL=0
WARNING=0
INFO=0
OUTPUT_FORMAT="human"

usage() {
    cat <<EOF
${SCRIPT_NAME} v${VERSION} — Check file and system permissions

USAGE:
    ${SCRIPT_NAME} [OPTIONS]

OPTIONS:
    --format FORMAT Output format: human (default) or json
    --help          Show this help message
    --version       Show version

WHAT IT CHECKS:
    • SSH key and config permissions (~/.ssh/)
    • Sensitive config file permissions (~/.config/, tokens, etc.)
    • World-readable/writable sensitive files
    • Exposed network ports (listening services)
    • LaunchAgent/LaunchDaemon review
    • Unsecured config files

EXIT CODES:
    0   No findings
    1   Warnings found
    2   Critical findings
EOF
    exit 0
}

for arg in "$@"; do
    case "$arg" in
        --help) usage ;;
        --version) echo "${SCRIPT_NAME} v${VERSION}"; exit 0 ;;
        --format=json) OUTPUT_FORMAT="json" ;;
    esac
done

emit_finding() {
    local severity="$1" category="$2" detail="$3"
    FINDINGS=$((FINDINGS + 1))
    case "$severity" in
        CRITICAL) CRITICAL=$((CRITICAL + 1)) ;;
        WARNING)  WARNING=$((WARNING + 1)) ;;
        INFO)     INFO=$((INFO + 1)) ;;
    esac

    if [[ "$OUTPUT_FORMAT" == "json" ]]; then
        printf '{"severity":"%s","category":"%s","detail":"%s"}\n' "$severity" "$category" "$detail"
    else
        local color="$GREEN"
        case "$severity" in
            CRITICAL) color="$RED" ;;
            WARNING)  color="$YELLOW" ;;
        esac
        printf "${color}[%s]${RESET} ${BOLD}%s${RESET} — %s\n" "$severity" "$category" "$detail"
    fi
}

echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo -e "${BOLD}${CYAN}  🔐 Arc Sentinel — Permission Auditor${RESET}"
echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo ""

# ── Check SSH directory ──
echo -e "${BOLD}Checking SSH configuration...${RESET}"

SSH_DIR="$HOME/.ssh"
if [[ -d "$SSH_DIR" ]]; then
    # Check .ssh directory permissions (should be 700)
    ssh_perms=$(stat -f '%Lp' "$SSH_DIR" 2>/dev/null) || true
    if [[ -n "$ssh_perms" && "$ssh_perms" != "700" ]]; then
        emit_finding "CRITICAL" "SSH Directory" "$SSH_DIR has permissions $ssh_perms (should be 700)"
    else
        emit_finding "INFO" "SSH Directory" "$SSH_DIR permissions OK (700)"
    fi

    # Check individual key files
    for keyfile in "$SSH_DIR"/id_* "$SSH_DIR"/*.pem; do
        [[ -f "$keyfile" ]] || continue
        # Skip public keys
        [[ "$keyfile" == *.pub ]] && continue
        perms=$(stat -f '%Lp' "$keyfile" 2>/dev/null) || true
        if [[ -n "$perms" && "$perms" != "600" && "$perms" != "400" ]]; then
            emit_finding "CRITICAL" "SSH Key" "$keyfile has permissions $perms (should be 600 or 400)"
        fi
    done

    # Check authorized_keys
    if [[ -f "$SSH_DIR/authorized_keys" ]]; then
        ak_perms=$(stat -f '%Lp' "$SSH_DIR/authorized_keys" 2>/dev/null) || true
        if [[ -n "$ak_perms" && "$ak_perms" != "600" && "$ak_perms" != "644" ]]; then
            emit_finding "WARNING" "SSH authorized_keys" "Permissions $ak_perms (should be 600 or 644)"
        fi
    fi

    # Check config
    if [[ -f "$SSH_DIR/config" ]]; then
        cfg_perms=$(stat -f '%Lp' "$SSH_DIR/config" 2>/dev/null) || true
        if [[ -n "$cfg_perms" && "$cfg_perms" != "600" && "$cfg_perms" != "644" ]]; then
            emit_finding "WARNING" "SSH Config" "$SSH_DIR/config has permissions $cfg_perms"
        fi
    fi
else
    emit_finding "INFO" "SSH Directory" "No ~/.ssh directory found"
fi

# ── Check sensitive config directories ──
echo ""
echo -e "${BOLD}Checking sensitive config files...${RESET}"

SENSITIVE_PATHS=(
    "$HOME/.config/fulcra/token.json"
    "$HOME/.config/gh/hosts.yml"
    "$HOME/.netrc"
    "$HOME/.npmrc"
    "$HOME/.pypirc"
    "$HOME/.docker/config.json"
    "$HOME/.kube/config"
    "$HOME/.aws/credentials"
    "$HOME/.aws/config"
    "$HOME/.gnupg"
    "$HOME/.secrets"
    "$HOME/.env"
)

for spath in "${SENSITIVE_PATHS[@]}"; do
    if [[ -e "$spath" ]]; then
        perms=$(stat -f '%Lp' "$spath" 2>/dev/null) || true
        if [[ -z "$perms" ]]; then continue; fi

        # Check for world-readable (perms end in 4,5,6,7 for "other" read)
        other_perms=${perms: -1}
        if [[ "$other_perms" =~ [4567] ]]; then
            emit_finding "CRITICAL" "World-Readable" "$spath is world-readable (perms: $perms)"
        elif [[ "$other_perms" =~ [2367] ]]; then
            emit_finding "CRITICAL" "World-Writable" "$spath is world-writable (perms: $perms)"
        else
            # Check group readable for very sensitive files
            group_perms=${perms:(-2):1}
            case "$spath" in
                *credentials*|*token*|*.netrc|*.pypirc|*hosts.yml)
                    if [[ "$group_perms" =~ [4567] ]]; then
                        emit_finding "WARNING" "Group-Readable" "$spath is group-readable (perms: $perms)"
                    fi
                    ;;
            esac
        fi
    fi
done

# Check for world-writable files in home directory (top level only)
echo ""
echo -e "${BOLD}Checking for world-writable files in home...${RESET}"
world_writable=$(find "$HOME" -maxdepth 2 -type f -perm +002 2>/dev/null | head -20) || true
if [[ -n "$world_writable" ]]; then
    while IFS= read -r wf; do
        emit_finding "WARNING" "World-Writable" "$wf is world-writable"
    done <<< "$world_writable"
fi

# ── Network ports ──
echo ""
echo -e "${BOLD}Checking exposed network ports...${RESET}"

# Use lsof on macOS
listening=$(lsof -iTCP -sTCP:LISTEN -nP 2>/dev/null | tail -n +2) || true
if [[ -n "$listening" ]]; then
    while IFS= read -r line; do
        proc=$(echo "$line" | awk '{print $1}')
        pid=$(echo "$line" | awk '{print $2}')
        addr=$(echo "$line" | awk '{print $9}')

        # Check if listening on all interfaces (*)
        if echo "$addr" | grep -qE '^\*:|^0\.0\.0\.0:'; then
            emit_finding "WARNING" "Open Port" "$proc (PID $pid) listening on ALL interfaces: $addr"
        else
            emit_finding "INFO" "Listening Port" "$proc (PID $pid) on $addr"
        fi
    done <<< "$listening"
else
    emit_finding "INFO" "Network Ports" "No listening TCP ports found (or insufficient permissions)"
fi

# ── LaunchAgents / LaunchDaemons ──
echo ""
echo -e "${BOLD}Checking LaunchAgents and LaunchDaemons...${RESET}"

LAUNCH_DIRS=(
    "$HOME/Library/LaunchAgents"
    "/Library/LaunchAgents"
    "/Library/LaunchDaemons"
)

for ldir in "${LAUNCH_DIRS[@]}"; do
    if [[ -d "$ldir" ]]; then
        plist_count=$(find "$ldir" -name '*.plist' -type f 2>/dev/null | wc -l | tr -d ' ')
        if [[ "$plist_count" -gt 0 ]]; then
            emit_finding "INFO" "LaunchAgent/Daemon" "$ldir contains $plist_count plist files"

            # Check for suspicious plists (running scripts from tmp, downloads, etc.)
            while IFS= read -r plist; do
                content=$(cat "$plist" 2>/dev/null) || continue
                if echo "$content" | grep -qiE '/tmp/|/var/tmp/|/Downloads/|curl |wget '; then
                    emit_finding "WARNING" "Suspicious LaunchAgent" "$plist references temp/download dirs or network tools"
                fi
                # Check permissions
                pl_perms=$(stat -f '%Lp' "$plist" 2>/dev/null) || true
                other=${pl_perms: -1}
                if [[ "$other" =~ [2367] ]]; then
                    emit_finding "CRITICAL" "Writable LaunchAgent" "$plist is world-writable (perms: $pl_perms)"
                fi
            done < <(find "$ldir" -name '*.plist' -type f 2>/dev/null)
        fi
    fi
done

# ── Summary ──
echo ""
echo -e "${BOLD}${CYAN}───────────────────────────────────────────${RESET}"
echo -e "${BOLD}Permission Auditor Summary${RESET}"
echo -e "  Total findings: ${FINDINGS}"
echo -e "  Critical:       ${RED}${CRITICAL}${RESET}"
echo -e "  Warnings:       ${YELLOW}${WARNING}${RESET}"
echo -e "  Info:           ${GREEN}${INFO}${RESET}"
echo -e "${BOLD}${CYAN}───────────────────────────────────────────${RESET}"

if [[ $CRITICAL -gt 0 ]]; then
    exit 2
elif [[ $WARNING -gt 0 ]]; then
    exit 1
else
    exit 0
fi
