#!/usr/bin/env bash
# token-watchdog.sh — Track auth token expiry and status
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
${SCRIPT_NAME} v${VERSION} — Track auth token expiry and status

USAGE:
    ${SCRIPT_NAME} [OPTIONS]

OPTIONS:
    --format FORMAT Output format: human (default) or json
    --help          Show this help message
    --version       Show version

WHAT IT CHECKS:
    • Fulcra token (~/.config/fulcra/token.json)
    • GitHub CLI auth status
    • Docker credentials
    • NPM tokens
    • AWS credentials
    • Kubernetes configs
    • SSH key passphrases (checks if keys are password-protected)

EXIT CODES:
    0   All tokens healthy
    1   Warnings (tokens expiring soon)
    2   Critical (expired tokens)
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

emit_token() {
    local status="$1" name="$2" detail="$3"
    FINDINGS=$((FINDINGS + 1))
    case "$status" in
        EXPIRED|CRITICAL) CRITICAL=$((CRITICAL + 1)) ;;
        EXPIRING|WARNING)  WARNING=$((WARNING + 1)) ;;
        *)     INFO=$((INFO + 1)) ;;
    esac

    if [[ "$OUTPUT_FORMAT" == "json" ]]; then
        printf '{"status":"%s","token":"%s","detail":"%s"}\n' "$status" "$name" "$detail"
    else
        local color="$GREEN" icon="✅"
        case "$status" in
            EXPIRED|CRITICAL) color="$RED"; icon="❌" ;;
            EXPIRING|WARNING) color="$YELLOW"; icon="⚠️" ;;
            OK|VALID|INFO)    color="$GREEN"; icon="✅" ;;
            MISSING)          color="$CYAN"; icon="—" ;;
        esac
        printf " ${icon} ${color}%-12s${RESET} %-28s %s\n" "[$status]" "$name" "$detail"
    fi
}

now_epoch() {
    date +%s
}

echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo -e "${BOLD}${CYAN}  🐕 Arc Sentinel — Token Watchdog${RESET}"
echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo ""
echo -e "${BOLD} Status       Token                        Detail${RESET}"
echo -e " ─────────── ──────────────────────────── ─────────────────────────"

NOW=$(now_epoch)
WARN_THRESHOLD=$((24 * 3600))  # 24 hours

# ── Fulcra Token ──
FULCRA_TOKEN="$HOME/.config/fulcra/token.json"
if [[ -f "$FULCRA_TOKEN" ]]; then
    # Try to parse expiry
    expiry=""
    if command -v python3 &>/dev/null; then
        expiry=$(python3 -c "
import json, sys
try:
    with open('$FULCRA_TOKEN') as f:
        d = json.load(f)
    # Check common expiry field names
    for key in ['expires_at', 'expiry', 'exp', 'expiresAt', 'expires']:
        if key in d:
            print(d[key])
            sys.exit(0)
    # Try to decode JWT access_token
    for key in ['access_token', 'token', 'id_token']:
        if key in d:
            import base64
            parts = d[key].split('.')
            if len(parts) >= 2:
                payload = parts[1] + '==' # pad
                decoded = json.loads(base64.urlsafe_b64decode(payload))
                if 'exp' in decoded:
                    print(decoded['exp'])
                    sys.exit(0)
    print('unknown')
except Exception as e:
    print('error')
" 2>/dev/null) || expiry="error"
    fi

    if [[ "$expiry" == "error" || "$expiry" == "unknown" || -z "$expiry" ]]; then
        emit_token "WARNING" "Fulcra Token" "Found but cannot parse expiry"
    elif [[ "$expiry" =~ ^[0-9]+$ ]]; then
        remaining=$((expiry - NOW))
        if [[ $remaining -lt 0 ]]; then
            emit_token "EXPIRED" "Fulcra Token" "Expired $(( -remaining / 3600 ))h ago"
        elif [[ $remaining -lt $WARN_THRESHOLD ]]; then
            emit_token "EXPIRING" "Fulcra Token" "Expires in $((remaining / 3600))h $((remaining % 3600 / 60))m"
        else
            emit_token "VALID" "Fulcra Token" "Expires in $((remaining / 86400))d $((remaining % 86400 / 3600))h"
        fi
    else
        # Try ISO date format
        if expiry_epoch=$(date -jf "%Y-%m-%dT%H:%M:%S" "$expiry" +%s 2>/dev/null || date -jf "%Y-%m-%d" "$expiry" +%s 2>/dev/null); then
            remaining=$((expiry_epoch - NOW))
            if [[ $remaining -lt 0 ]]; then
                emit_token "EXPIRED" "Fulcra Token" "Expired"
            elif [[ $remaining -lt $WARN_THRESHOLD ]]; then
                emit_token "EXPIRING" "Fulcra Token" "Expires in $((remaining / 3600))h"
            else
                emit_token "VALID" "Fulcra Token" "Expires in $((remaining / 86400))d"
            fi
        else
            emit_token "WARNING" "Fulcra Token" "Cannot parse expiry: $expiry"
        fi
    fi
else
    emit_token "MISSING" "Fulcra Token" "Not found at $FULCRA_TOKEN"
fi

# ── GitHub CLI ──
if command -v gh &>/dev/null; then
    gh_status=$(gh auth status 2>&1) || true
    if echo "$gh_status" | grep -q "Logged in"; then
        gh_user=$(echo "$gh_status" | grep -oE 'account [^ ]+' | head -1 | awk '{print $2}') || gh_user="unknown"
        gh_scopes=$(echo "$gh_status" | grep -oE 'Token scopes:.*' | head -1) || gh_scopes=""
        emit_token "VALID" "GitHub CLI" "Logged in as $gh_user ${gh_scopes:+(${gh_scopes})}"
    elif echo "$gh_status" | grep -qi "expired"; then
        emit_token "EXPIRED" "GitHub CLI" "Token expired"
    else
        emit_token "WARNING" "GitHub CLI" "Not authenticated"
    fi
else
    emit_token "MISSING" "GitHub CLI" "gh not installed"
fi

# ── Docker ──
DOCKER_CONFIG="$HOME/.docker/config.json"
if [[ -f "$DOCKER_CONFIG" ]]; then
    has_auths=$(python3 -c "
import json
with open('$DOCKER_CONFIG') as f:
    d = json.load(f)
auths = d.get('auths', {})
if auths:
    print(','.join(auths.keys()))
else:
    print('none')
" 2>/dev/null) || has_auths="error"

    if [[ "$has_auths" == "none" || "$has_auths" == "error" ]]; then
        emit_token "MISSING" "Docker" "No stored credentials"
    else
        emit_token "INFO" "Docker" "Credentials for: $has_auths"
    fi
else
    emit_token "MISSING" "Docker" "No docker config found"
fi

# ── NPM ──
NPMRC="$HOME/.npmrc"
if [[ -f "$NPMRC" ]]; then
    if grep -q '_authToken' "$NPMRC" 2>/dev/null; then
        emit_token "INFO" "NPM" "Auth token present in ~/.npmrc"
    else
        emit_token "MISSING" "NPM" "No auth token in ~/.npmrc"
    fi
else
    emit_token "MISSING" "NPM" "No ~/.npmrc found"
fi

# ── AWS ──
AWS_CREDS="$HOME/.aws/credentials"
if [[ -f "$AWS_CREDS" ]]; then
    profiles=$(grep -c '^\[' "$AWS_CREDS" 2>/dev/null) || profiles=0
    emit_token "INFO" "AWS" "$profiles profile(s) in credentials file"

    # Check if using temporary credentials (have session token)
    if grep -q 'aws_session_token' "$AWS_CREDS" 2>/dev/null; then
        emit_token "WARNING" "AWS Session" "Temporary credentials found — may expire"
    fi
else
    if [[ -n "${AWS_ACCESS_KEY_ID:-}" ]]; then
        emit_token "INFO" "AWS" "Credentials via environment variables"
    else
        emit_token "MISSING" "AWS" "No credentials found"
    fi
fi

# ── Kubernetes ──
KUBE_CONFIG="${KUBECONFIG:-$HOME/.kube/config}"
if [[ -f "$KUBE_CONFIG" ]]; then
    contexts=$(grep -c 'name:' "$KUBE_CONFIG" 2>/dev/null) || contexts=0
    current=$(grep 'current-context:' "$KUBE_CONFIG" 2>/dev/null | awk '{print $2}') || current="none"
    emit_token "INFO" "Kubernetes" "Config found, current context: ${current:-none}"

    # Check for client certificates that might expire
    if grep -q 'client-certificate-data' "$KUBE_CONFIG" 2>/dev/null; then
        emit_token "INFO" "Kubernetes" "Using embedded client certificates"
    fi
else
    emit_token "MISSING" "Kubernetes" "No kubeconfig found"
fi

# ── SSH Keys (check if password-protected) ──
SSH_DIR="$HOME/.ssh"
if [[ -d "$SSH_DIR" ]]; then
    for keyfile in "$SSH_DIR"/id_*; do
        [[ -f "$keyfile" ]] || continue
        [[ "$keyfile" == *.pub ]] && continue
        keyname=$(basename "$keyfile")
        if head -5 "$keyfile" 2>/dev/null | grep -q 'ENCRYPTED'; then
            emit_token "VALID" "SSH: $keyname" "Password-protected"
        elif head -1 "$keyfile" 2>/dev/null | grep -q 'PRIVATE KEY'; then
            emit_token "WARNING" "SSH: $keyname" "NOT password-protected"
        fi
    done
fi

# ── Summary ──
echo ""
echo -e "${BOLD}${CYAN}───────────────────────────────────────────${RESET}"
echo -e "${BOLD}Token Watchdog Summary${RESET}"
echo -e "  Tokens checked: ${FINDINGS}"
echo -e "  Critical/Expired: ${RED}${CRITICAL}${RESET}"
echo -e "  Warnings/Expiring: ${YELLOW}${WARNING}${RESET}"
echo -e "  Healthy/Info:      ${GREEN}${INFO}${RESET}"
echo -e "${BOLD}${CYAN}───────────────────────────────────────────${RESET}"

if [[ $CRITICAL -gt 0 ]]; then
    exit 2
elif [[ $WARNING -gt 0 ]]; then
    exit 1
else
    exit 0
fi
