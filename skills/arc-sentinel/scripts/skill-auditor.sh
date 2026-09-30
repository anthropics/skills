#!/usr/bin/env bash
# skill-auditor.sh — Analyze installed OpenClaw skills for suspicious patterns
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

SKILLS_ROOT="${1:-$HOME/.openclaw/workspace/skills}"
FINDINGS=0
CRITICAL=0
WARNING=0
INFO=0
OUTPUT_FORMAT="human"

usage() {
    cat <<EOF
${SCRIPT_NAME} v${VERSION} — Analyze installed OpenClaw skills for suspicious patterns

USAGE:
    ${SCRIPT_NAME} [OPTIONS] [SKILLS_DIRECTORY]

ARGUMENTS:
    SKILLS_DIRECTORY    Path to skills directory (default: ~/.openclaw/workspace/skills)

OPTIONS:
    --format FORMAT Output format: human (default) or json
    --help          Show this help message
    --version       Show version

WHAT IT CHECKS:
    • curl/wget calls to unknown or suspicious URLs
    • eval/exec of untrusted input
    • File exfiltration patterns (uploading files to external services)
    • Obfuscated code (base64 encoded commands, hex escapes)
    • Excessive permission requests
    • Suspicious environment variable access

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
        *) if [[ -d "$arg" ]]; then SKILLS_ROOT="$arg"; fi ;;
    esac
done

emit_finding() {
    local severity="$1" skill="$2" detail="$3"
    FINDINGS=$((FINDINGS + 1))
    case "$severity" in
        CRITICAL) CRITICAL=$((CRITICAL + 1)) ;;
        WARNING)  WARNING=$((WARNING + 1)) ;;
        INFO)     INFO=$((INFO + 1)) ;;
    esac

    if [[ "$OUTPUT_FORMAT" == "json" ]]; then
        printf '{"severity":"%s","skill":"%s","detail":"%s"}\n' "$severity" "$skill" "$detail"
    else
        local color="$GREEN"
        case "$severity" in
            CRITICAL) color="$RED" ;;
            WARNING)  color="$YELLOW" ;;
        esac
        printf "${color}[%s]${RESET} ${BOLD}%s${RESET} — %s\n" "$severity" "$skill" "$detail"
    fi
}

is_self() {
    local path="$1"
    local abs_path
    abs_path="$(cd "$(dirname "$path")" 2>/dev/null && pwd)/$(basename "$path")" 2>/dev/null || return 1
    [[ "$abs_path" == "$SKILL_DIR"/* ]] && return 0
    return 1
}

echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo -e "${BOLD}${CYAN}  🛡️  Arc Sentinel — Skill Auditor${RESET}"
echo -e "${BOLD}${CYAN}═══════════════════════════════════════════${RESET}"
echo -e "Scanning: ${SKILLS_ROOT}"
echo ""

if [[ ! -d "$SKILLS_ROOT" ]]; then
    echo -e "${YELLOW}No skills directory found at $SKILLS_ROOT${RESET}"
    exit 0
fi

# Find all skill directories (contain SKILL.md)
skill_count=0
for skill_dir in "$SKILLS_ROOT"/*/; do
    [[ -d "$skill_dir" ]] || continue
    skill_name=$(basename "$skill_dir")

    # Skip self
    abs_skill_dir="$(cd "$skill_dir" && pwd)"
    [[ "$abs_skill_dir" == "$SKILL_DIR" ]] && continue

    skill_count=$((skill_count + 1))
    echo -e "${BOLD}Auditing skill: ${skill_name}${RESET}"

    has_skill_md=false
    [[ -f "$skill_dir/SKILL.md" ]] && has_skill_md=true

    if ! $has_skill_md; then
        emit_finding "WARNING" "$skill_name" "No SKILL.md found — non-standard skill"
    fi

    # Scan all text files in the skill
    file_list=$(find "$skill_dir" -type f -size -1M \
        -not -path '*/.git/*' \
        -not -path '*/node_modules/*' \
        -not -name '*.png' -not -name '*.jpg' -not -name '*.gif' \
        -not -name '*.zip' -not -name '*.tar*' -not -name '*.gz' \
        2>/dev/null) || true

    [[ -z "$file_list" ]] && continue

    while IFS= read -r file; do
        [[ -f "$file" ]] || continue
        # Skip binary files
        file -b --mime-type "$file" 2>/dev/null | grep -q '^text/' || continue

        rel_file="${file#$SKILLS_ROOT/}"
        content=$(cat "$file" 2>/dev/null) || continue

        # Check for network calls to external URLs
        ext_urls=$(echo "$content" | grep -noE '(curl|wget|fetch|http\.get|requests\.(get|post))\s+["\x27]?https?://[^"\x27\s]+' 2>/dev/null | head -5) || true
        if [[ -n "$ext_urls" ]]; then
            while IFS= read -r match; do
                line_num=$(echo "$match" | cut -d: -f1)
                url_text=$(echo "$match" | cut -d: -f2- | head -c 100)
                # Check if URL is to a known safe domain
                if echo "$url_text" | grep -qvE 'github\.com|githubusercontent\.com|npmjs\.org|pypi\.org|brew\.sh|apple\.com'; then
                    emit_finding "WARNING" "$skill_name" "External network call at $rel_file:$line_num — $url_text"
                fi
            done <<< "$ext_urls"
        fi

        # Check for eval/exec of variables or command substitution
        evals=$(echo "$content" | grep -noE '(eval\s+["$]|exec\s+["$]|\$\(.*\$\{)' 2>/dev/null | head -5) || true
        if [[ -n "$evals" ]]; then
            while IFS= read -r match; do
                line_num=$(echo "$match" | cut -d: -f1)
                emit_finding "WARNING" "$skill_name" "eval/exec of dynamic input at $rel_file:$line_num"
            done <<< "$evals"
        fi

        # Check for file exfiltration patterns
        exfil=$(echo "$content" | grep -noE '(curl.*-F|curl.*--upload-file|curl.*-d @|scp\s|rsync\s.*@)' 2>/dev/null | head -5) || true
        if [[ -n "$exfil" ]]; then
            while IFS= read -r match; do
                line_num=$(echo "$match" | cut -d: -f1)
                emit_finding "CRITICAL" "$skill_name" "Potential file exfiltration at $rel_file:$line_num"
            done <<< "$exfil"
        fi

        # Check for base64 obfuscation
        obfuscated=$(echo "$content" | grep -noE '(base64\s+-d|base64\s+--decode|\$\(echo\s+[A-Za-z0-9+/=]{20,}\s*\|\s*base64)' 2>/dev/null | head -3) || true
        if [[ -n "$obfuscated" ]]; then
            while IFS= read -r match; do
                line_num=$(echo "$match" | cut -d: -f1)
                emit_finding "CRITICAL" "$skill_name" "Obfuscated code (base64) at $rel_file:$line_num"
            done <<< "$obfuscated"
        fi

        # Check for environment variable harvesting
        env_harvest=$(echo "$content" | grep -noE '(env\s*$|printenv|set\s*$|\$\{?[A-Z_]*TOKEN|\$\{?[A-Z_]*SECRET|\$\{?[A-Z_]*PASSWORD|\$\{?[A-Z_]*KEY)' 2>/dev/null | head -5) || true
        if [[ -n "$env_harvest" ]]; then
            env_count=$(echo "$env_harvest" | wc -l | tr -d ' ')
            if [[ "$env_count" -gt 3 ]]; then
                emit_finding "WARNING" "$skill_name" "Accesses $env_count+ sensitive env vars in $rel_file"
            fi
        fi

        # Check for chmod 777 or overly permissive operations
        bad_chmod=$(echo "$content" | grep -noE 'chmod\s+(777|666|a\+[rwx])' 2>/dev/null | head -3) || true
        if [[ -n "$bad_chmod" ]]; then
            while IFS= read -r match; do
                line_num=$(echo "$match" | cut -d: -f1)
                emit_finding "WARNING" "$skill_name" "Overly permissive chmod at $rel_file:$line_num"
            done <<< "$bad_chmod"
        fi

    done <<< "$file_list"
    echo ""
done

echo -e "${BOLD}${CYAN}───────────────────────────────────────────${RESET}"
echo -e "${BOLD}Skill Auditor Summary${RESET}"
echo -e "  Skills scanned: ${skill_count}"
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
    echo -e "  ✅ ${BOLD}All skills look clean!${RESET}"
    exit 0
fi
