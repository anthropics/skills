#!/usr/bin/env bash
# secret-scanner.sh — Scan workspace files for leaked secrets
# Part of arc-sentinel OpenClaw security skill

set -uo pipefail

VERSION="1.0.0"
SCRIPT_NAME="$(basename "$0")"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SKILL_DIR="$(dirname "$SCRIPT_DIR")"

# Colors
RED='\033[0;31m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
RESET='\033[0m'

# Defaults
SCAN_DIR=""
FINDINGS=0
CRITICAL=0
WARNING=0
OUTPUT_FORMAT="human"

usage() {
    cat <<EOF
${SCRIPT_NAME} v${VERSION} — Scan workspace files for leaked secrets

USAGE:
    ${SCRIPT_NAME} [OPTIONS] [DIRECTORY]

ARGUMENTS:
    DIRECTORY       Directory to scan (default: current directory)

OPTIONS:
    --format FORMAT Output format: human (default) or json
    --help          Show this help message
    --version       Show version

WHAT IT CHECKS:
    • API keys (generic, AWS, Google, GitHub, Slack, Stripe, etc.)
    • Passwords and tokens in config files
    • Private keys (SSH, PGP, RSA)
    • .gitignore coverage of secret-looking files
    • Git history (last 20 commits) for accidentally committed secrets

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
        --format=json|--format=JSON) OUTPUT_FORMAT="json" ;;
        --format=*) OUTPUT_FORMAT="human" ;;
        *)
            if [[ -d "$arg" ]]; then
                SCAN_DIR="$arg"
            fi
            ;;
    esac
done

# Default to current directory
SCAN_DIR="${SCAN_DIR:-.}"
SCAN_DIR="$(cd "$SCAN_DIR" 2>/dev/null && pwd)" || { echo "Error: Cannot access directory"; exit 1; }

emit_finding() {
    local severity="$1" file="$2" line="$3" pattern="$4" match="$5"
    FINDINGS=$((FINDINGS + 1))
    if [[ "$severity" == "CRITICAL" ]]; then
        CRITICAL=$((CRITICAL + 1))
    else
        WARNING=$((WARNING + 1))
    fi

    if [[ "$OUTPUT_FORMAT" == "json" ]]; then
        local escaped_match
        escaped_match=$(echo "$match" | sed 's/"/\\"/g' | head -c 120)
        printf '{"severity":"%s","file":"%s","line":%s,"pattern":"%s","match":"%s"}\n' \
            "$severity" "$file" "$line" "$pattern" "$escaped_match"
    else
        local color="$YELLOW"
        [[ "$severity" == "CRITICAL" ]] && color="$RED"
        printf "${color}[%s]${RESET} %s:%s — ${BOLD}%s${RESET}\n" \
            "$severity" "$file" "$line" "$pattern"
    fi
}

echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo -e "${BOLD}${CYAN}  🔍 Arc Sentinel — Secret Scanner${RESET}"
echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo -e "Scanning: ${SCAN_DIR}"
echo ""

# ── Phase 1: Regex scan of workspace files ──
echo -e "${BOLD}Phase 1: Scanning files for secret patterns...${RESET}"

# Combined grep pattern for efficiency — one pass per file
COMBINED_PATTERN='AKIA[0-9A-Z]{16}|ghp_[A-Za-z0-9]{36}|github_pat_[A-Za-z0-9_]{82}|gho_[A-Za-z0-9]{36}|xox[baprs]-[0-9A-Za-z-]{10,}|sk_live_[0-9a-zA-Z]{24,}|pk_live_[0-9a-zA-Z]{24,}|AIza[0-9A-Za-z_-]{35}|-----BEGIN (RSA |EC |DSA |OPENSSH )?PRIVATE KEY-----|SG\.[A-Za-z0-9_-]{22}\.[A-Za-z0-9_-]{43}|SK[0-9a-fA-F]{32}'

# Secondary patterns (case-insensitive, checked separately)
CI_PATTERN='(api[_-]?key|apikey|secret|password|passwd|pwd)[[:space:]]*[=:][[:space:]]*["\x27][^\x27"]{8,}["\x27]'

# Use grep -r for efficiency instead of find+loop
# Exclude arc-sentinel skill directory, .git, node_modules, binaries
grep_results=$(grep -rnE "$COMBINED_PATTERN" "$SCAN_DIR" \
    --include='*.js' --include='*.ts' --include='*.py' --include='*.rb' \
    --include='*.go' --include='*.rs' --include='*.java' --include='*.sh' \
    --include='*.bash' --include='*.zsh' --include='*.yml' --include='*.yaml' \
    --include='*.json' --include='*.xml' --include='*.toml' --include='*.ini' \
    --include='*.cfg' --include='*.conf' --include='*.config' --include='*.env' \
    --include='*.env.*' --include='*.properties' --include='*.tf' \
    --include='*.md' --include='*.txt' --include='*.html' --include='*.css' \
    --include='*.dockerfile' --include='Dockerfile' --include='*.csv' \
    --include='Makefile' --include='*.mk' --include='*.gradle' \
    --include='*.swift' --include='*.kt' --include='*.php' --include='*.pl' \
    --include='*.r' --include='*.R' --include='*.lua' --include='*.vim' \
    2>/dev/null | grep -v "arc-sentinel/" | head -200) || true

if [[ -n "$grep_results" ]]; then
    while IFS= read -r line; do
        file_path=$(echo "$line" | cut -d: -f1)
        line_num=$(echo "$line" | cut -d: -f2)
        match_text=$(echo "$line" | cut -d: -f3- | head -c 120)
        rel_file="${file_path#$SCAN_DIR/}"

        # Classify the finding
        pattern_name="Secret Pattern"
        severity="WARNING"
        if echo "$match_text" | grep -qE 'AKIA[0-9A-Z]{16}'; then
            pattern_name="AWS Access Key"; severity="CRITICAL"
        elif echo "$match_text" | grep -qE 'ghp_[A-Za-z0-9]{36}'; then
            pattern_name="GitHub Token"; severity="CRITICAL"
        elif echo "$match_text" | grep -qE 'gho_[A-Za-z0-9]{36}'; then
            pattern_name="GitHub OAuth Token"; severity="CRITICAL"
        elif echo "$match_text" | grep -qE 'xox[baprs]-'; then
            pattern_name="Slack Token"; severity="CRITICAL"
        elif echo "$match_text" | grep -qE 'sk_live_'; then
            pattern_name="Stripe Secret Key"; severity="CRITICAL"
        elif echo "$match_text" | grep -qE 'pk_live_'; then
            pattern_name="Stripe Publishable Key"; severity="WARNING"
        elif echo "$match_text" | grep -qE 'AIza'; then
            pattern_name="Google API Key"; severity="WARNING"
        elif echo "$match_text" | grep -qE 'PRIVATE KEY'; then
            pattern_name="Private Key"; severity="CRITICAL"
        elif echo "$match_text" | grep -qE 'SG\.'; then
            pattern_name="SendGrid API Key"; severity="CRITICAL"
        elif echo "$match_text" | grep -qE 'SK[0-9a-fA-F]{32}'; then
            pattern_name="Twilio API Key"; severity="CRITICAL"
        fi

        emit_finding "$severity" "$rel_file" "$line_num" "$pattern_name" "$match_text"
    done <<< "$grep_results"
fi

# Case-insensitive scan for generic secrets (separate pass for -i flag)
ci_results=$(grep -rniE "$CI_PATTERN" "$SCAN_DIR" \
    --include='*.js' --include='*.ts' --include='*.py' --include='*.yml' \
    --include='*.yaml' --include='*.json' --include='*.toml' --include='*.ini' \
    --include='*.cfg' --include='*.conf' --include='*.env' --include='*.env.*' \
    --include='*.properties' --include='*.sh' --include='*.tf' \
    2>/dev/null | grep -v "arc-sentinel/" | head -50) || true

if [[ -n "$ci_results" ]]; then
    while IFS= read -r line; do
        file_path=$(echo "$line" | cut -d: -f1)
        line_num=$(echo "$line" | cut -d: -f2)
        match_text=$(echo "$line" | cut -d: -f3- | head -c 120)
        rel_file="${file_path#$SCAN_DIR/}"
        emit_finding "WARNING" "$rel_file" "$line_num" "Generic Secret/Password" "$match_text"
    done <<< "$ci_results"
fi

# ── Phase 2: Check .gitignore coverage ──
echo ""
echo -e "${BOLD}Phase 2: Checking .gitignore coverage...${RESET}"

SENSITIVE_PATTERNS=(".env" ".secrets" "*.key" "*.pem" "*.p12" "*.pfx" "*.jks" "id_rsa" "id_ed25519" "*.keystore" "credentials.json" "token.json" "service-account*.json")

if [[ -f "$SCAN_DIR/.gitignore" ]]; then
    gitignore_content=$(cat "$SCAN_DIR/.gitignore")
    for pat in "${SENSITIVE_PATTERNS[@]}"; do
        if ! echo "$gitignore_content" | grep -qF "$pat"; then
            emit_finding "WARNING" ".gitignore" "0" "Missing gitignore pattern" "$pat not in .gitignore"
        fi
    done
else
    emit_finding "WARNING" ".gitignore" "0" "No .gitignore" "No .gitignore found in scan root"
fi

# Check if sensitive files are tracked by git
if [[ -d "$SCAN_DIR/.git" ]]; then
    tracked=$(cd "$SCAN_DIR" && git ls-files 2>/dev/null) || true
    if [[ -n "$tracked" ]]; then
        while IFS= read -r tf; do
            case "$tf" in
                *.env|*.env.*|*.pem|*.key|*.p12|*.pfx|*id_rsa*|*id_ed25519*|*.keystore|*credentials.json|*secret*)
                    emit_finding "CRITICAL" "$tf" "0" "Sensitive file tracked" "File is tracked by git"
                    ;;
            esac
        done <<< "$tracked"
    fi
fi

# ── Phase 3: Check git history ──
echo ""
echo -e "${BOLD}Phase 3: Scanning recent git history (last 20 commits)...${RESET}"

if [[ -d "$SCAN_DIR/.git" ]]; then
    cd "$SCAN_DIR"
    HISTORY_PATTERNS="AKIA[0-9A-Z]{16}|ghp_[A-Za-z0-9]{36}|sk_live_[0-9a-zA-Z]{24,}|-----BEGIN (RSA |EC )?PRIVATE KEY-----|xox[baprs]-[0-9A-Za-z-]{10,}"

    commits=$(git log --oneline -20 --format='%H' 2>/dev/null) || true
    if [[ -n "$commits" ]]; then
        while IFS= read -r commit; do
            diff_output=$(git diff-tree -p "$commit" 2>/dev/null | grep -cE "$HISTORY_PATTERNS" 2>/dev/null) || diff_output=0
            if [[ "$diff_output" -gt 0 ]]; then
                short=$(git log --oneline -1 "$commit" 2>/dev/null)
                emit_finding "CRITICAL" "git-history" "0" "Secret in commit" "$short"
            fi
        done <<< "$commits"
    fi
fi

# ── Summary ──
echo ""
echo -e "${BOLD}${CYAN}───────────────────────────────────────────${RESET}"
echo -e "${BOLD}Secret Scanner Summary${RESET}"
echo -e "  Total findings: ${FINDINGS}"
echo -e "  Critical:       ${RED}${CRITICAL}${RESET}"
echo -e "  Warnings:       ${YELLOW}${WARNING}${RESET}"
echo -e "${BOLD}${CYAN}───────────────────────────────────────────${RESET}"

if [[ $CRITICAL -gt 0 ]]; then
    exit 2
elif [[ $WARNING -gt 0 ]]; then
    exit 1
else
    echo -e "  ✅ ${BOLD}No secrets found!${RESET}"
    exit 0
fi
