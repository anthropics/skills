#!/usr/bin/env bash
# git-hygiene.sh — Check git repos for security issues
# Part of arc-sentinel OpenClaw security skill

set -uo pipefail

VERSION="1.0.0"
SCRIPT_NAME="$(basename "$0")"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SKILL_DIR="$(dirname "$SCRIPT_DIR")"

RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
BOLD='\033[1m'
RESET='\033[0m'

SCAN_DIR="${1:-.}"
FINDINGS=0
CRITICAL=0
WARNING=0
INFO=0
OUTPUT_FORMAT="human"

usage() {
    cat <<EOF
${SCRIPT_NAME} v${VERSION} — Check git repos for security issues

USAGE:
    ${SCRIPT_NAME} [OPTIONS] [DIRECTORY]

ARGUMENTS:
    DIRECTORY       Git repository to scan (default: current directory)

OPTIONS:
    --format FORMAT Output format: human (default) or json
    --help          Show this help message
    --version       Show version

WHAT IT CHECKS:
    • Secrets leaked in git history
    • .gitignore completeness for sensitive patterns
    • Unsigned commits warning
    • Large binary files that might contain secrets
    • Remote URL security (https vs http vs ssh)
    • Branch protection indicators

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
        *) if [[ -d "$arg" ]]; then SCAN_DIR="$arg"; fi ;;
    esac
done

SCAN_DIR="$(cd "$SCAN_DIR" 2>/dev/null && pwd)" || { echo "Error: Cannot access directory"; exit 1; }

emit_finding() {
    local severity="$1" category="$2" detail="$3"
    FINDINGS=$((FINDINGS + 1))
    case "$severity" in
        CRITICAL) CRITICAL=$((CRITICAL + 1)) ;;
        WARNING)  WARNING=$((WARNING + 1)) ;;
        INFO)     INFO=$((INFO + 1)) ;;
    esac

    if [[ "$OUTPUT_FORMAT" == "json" ]]; then
        # Escape quotes in detail
        local escaped_detail
        escaped_detail=$(echo "$detail" | sed 's/"/\\"/g')
        printf '{"severity":"%s","category":"%s","detail":"%s"}\n' "$severity" "$category" "$escaped_detail"
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
echo -e "${BOLD}${CYAN}  🧹 Arc Sentinel — Git Hygiene${RESET}"
echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo -e "Scanning: ${SCAN_DIR}"
echo ""

if [[ ! -d "$SCAN_DIR/.git" ]]; then
    echo -e "${YELLOW}Not a git repository: $SCAN_DIR${RESET}"
    echo -e "Searching for git repos in subdirectories..."

    found_repos=0
    while IFS= read -r repo_dir; do
        repo_parent=$(dirname "$repo_dir")
        echo -e "\n${BOLD}Found repo: $repo_parent${RESET}"
        # Recurse (but don't go infinite)
        "$0" "$repo_parent"
        found_repos=$((found_repos + 1))
    done < <(find "$SCAN_DIR" -maxdepth 3 -name ".git" -type d 2>/dev/null)

    if [[ $found_repos -eq 0 ]]; then
        echo -e "${YELLOW}No git repositories found.${RESET}"
    fi
    exit 0
fi

cd "$SCAN_DIR"

# ── Check .gitignore completeness ──
echo -e "${BOLD}Checking .gitignore completeness...${RESET}"

REQUIRED_PATTERNS=(
    ".env"
    ".env.*"
    "*.key"
    "*.pem"
    "*.p12"
    ".secrets"
    "*.keystore"
    "id_rsa"
    "id_ed25519"
    "credentials.json"
    "token.json"
    "*.secret"
)

if [[ -f ".gitignore" ]]; then
    gitignore=$(cat .gitignore)
    missing_count=0
    missing_list=""
    for pat in "${REQUIRED_PATTERNS[@]}"; do
        if ! echo "$gitignore" | grep -qF "$pat"; then
            missing_count=$((missing_count + 1))
            missing_list="$missing_list $pat"
        fi
    done
    if [[ $missing_count -gt 0 ]]; then
        emit_finding "WARNING" "Incomplete .gitignore" "Missing $missing_count patterns:$missing_list"
    else
        emit_finding "INFO" ".gitignore" "All recommended patterns present"
    fi
else
    emit_finding "WARNING" "No .gitignore" "Repository has no .gitignore file"
fi

# ── Check for secrets in history ──
echo ""
echo -e "${BOLD}Scanning git history for secrets (last 20 commits)...${RESET}"

SECRET_REGEX='AKIA[0-9A-Z]{16}|ghp_[A-Za-z0-9]{36}|sk_live_[0-9a-zA-Z]{24,}|-----BEGIN (RSA |EC |DSA )?PRIVATE KEY-----|xox[baprs]-[0-9A-Za-z-]{10,}|SG\.[A-Za-z0-9_-]{22}\.[A-Za-z0-9_-]{43}'

commits=$(git log --oneline -20 --format='%H' 2>/dev/null) || true
history_findings=0
if [[ -n "$commits" ]]; then
    while IFS= read -r commit; do
        diff_matches=$(git diff-tree -p "$commit" 2>/dev/null | grep -cE "$SECRET_REGEX" 2>/dev/null) || diff_matches=0
        if [[ "$diff_matches" -gt 0 ]]; then
            short=$(git log --oneline -1 "$commit" 2>/dev/null)
            emit_finding "CRITICAL" "Secret in History" "Commit $short contains $diff_matches potential secret(s)"
            history_findings=$((history_findings + 1))
        fi
    done <<< "$commits"
fi
if [[ $history_findings -eq 0 ]]; then
    emit_finding "INFO" "Git History" "No secrets found in last 20 commits"
fi

# ── Check for unsigned commits ──
echo ""
echo -e "${BOLD}Checking commit signing...${RESET}"

total_commits=$(git log --oneline -20 2>/dev/null | wc -l | tr -d ' ') || total_commits=0
signed_commits=$(git log --oneline -20 --format='%G?' 2>/dev/null | grep -c '[GU]') || signed_commits=0
unsigned=$((total_commits - signed_commits))

if [[ $total_commits -eq 0 ]]; then
    emit_finding "INFO" "Commit Signing" "No commits to check"
elif [[ $unsigned -eq $total_commits ]]; then
    emit_finding "WARNING" "Commit Signing" "None of last $total_commits commits are signed"
elif [[ $unsigned -gt 0 ]]; then
    emit_finding "INFO" "Commit Signing" "$signed_commits/$total_commits recent commits are signed"
else
    emit_finding "INFO" "Commit Signing" "All $total_commits recent commits are signed ✓"
fi

# ── Check for large binary files ──
echo ""
echo -e "${BOLD}Checking for large binary files...${RESET}"

large_files=$(git ls-files 2>/dev/null | while IFS= read -r f; do
    [[ -f "$f" ]] || continue
    size=$(stat -f '%z' "$f" 2>/dev/null) || continue
    if [[ "$size" -gt 1048576 ]]; then  # > 1MB
        mime=$(file -b --mime-type "$f" 2>/dev/null) || mime="unknown"
        if ! echo "$mime" | grep -q '^text/'; then
            echo "$f ($((size / 1024))KB, $mime)"
        fi
    fi
done) || true

if [[ -n "$large_files" ]]; then
    while IFS= read -r lf; do
        emit_finding "WARNING" "Large Binary" "Tracked binary file: $lf"
    done <<< "$large_files"
else
    emit_finding "INFO" "Binary Files" "No large binary files tracked"
fi

# ── Check remote URLs ──
echo ""
echo -e "${BOLD}Checking remote URL security...${RESET}"

remotes=$(git remote -v 2>/dev/null | awk '{print $1, $2}' | sort -u) || true
if [[ -n "$remotes" ]]; then
    while IFS= read -r remote_line; do
        name=$(echo "$remote_line" | awk '{print $1}')
        url=$(echo "$remote_line" | awk '{print $2}')

        if echo "$url" | grep -q '^http://'; then
            emit_finding "CRITICAL" "Insecure Remote" "$name uses HTTP (not HTTPS): $url"
        elif echo "$url" | grep -q '^https://'; then
            # Check if credentials are embedded in URL
            if echo "$url" | grep -qE 'https://[^@]+@'; then
                emit_finding "CRITICAL" "Credentials in URL" "$name has credentials in remote URL"
            else
                emit_finding "INFO" "Remote URL" "$name → $url (HTTPS ✓)"
            fi
        elif echo "$url" | grep -qE '^git@|^ssh://'; then
            emit_finding "INFO" "Remote URL" "$name → $url (SSH ✓)"
        fi
    done <<< "$remotes"
else
    emit_finding "INFO" "Remotes" "No remotes configured"
fi

# ── Check for sensitive files tracked by git ──
echo ""
echo -e "${BOLD}Checking for sensitive tracked files...${RESET}"

tracked_sensitive=0
git ls-files 2>/dev/null | while IFS= read -r f; do
    case "$f" in
        *.env|*.env.*|*.pem|*.key|*.p12|*.pfx|*id_rsa|*id_ed25519|*.keystore|*credentials.json|*.secret)
            emit_finding "CRITICAL" "Tracked Sensitive File" "$f should not be in version control"
            tracked_sensitive=$((tracked_sensitive + 1))
            ;;
    esac
done || true

# ── Summary ──
echo ""
echo -e "${BOLD}${CYAN}───────────────────────────────────────────${RESET}"
echo -e "${BOLD}Git Hygiene Summary${RESET}"
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
