#!/usr/bin/env bash
# full-audit.sh — Run all arc-sentinel scanners and produce a combined report
# Part of arc-sentinel OpenClaw security skill

set -uo pipefail

VERSION="1.0.0"
SCRIPT_NAME="$(basename "$0")"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
BOLD='\033[1m'
RESET='\033[0m'

SCAN_DIR="${1:-.}"
OUTPUT_FORMAT="human"
REPORT_FILE=""
VERBOSE=false

usage() {
    cat <<EOF
${SCRIPT_NAME} v${VERSION} — Run all arc-sentinel security scanners

USAGE:
    ${SCRIPT_NAME} [OPTIONS] [DIRECTORY]

ARGUMENTS:
    DIRECTORY           Directory to scan (default: current directory)

OPTIONS:
    --format FORMAT     Output format: human (default) or json
    --report FILE       Save report to file (in addition to stdout)
    --verbose           Show full output from each scanner
    --help              Show this help message
    --version           Show version

SCANNERS RUN:
    1. secret-scanner.sh    — Find leaked secrets in files and git history
    2. permission-auditor.sh — Check file and system permissions
    3. skill-auditor.sh     — Audit installed OpenClaw skills
    4. token-watchdog.sh    — Check auth token expiry
    5. git-hygiene.sh       — Git repository security checks

EXIT CODES:
    0   Clean — no issues found
    1   Warnings found
    2   Critical findings detected
EOF
    exit 0
}

for arg in "$@"; do
    case "$arg" in
        --help) usage ;;
        --version) echo "${SCRIPT_NAME} v${VERSION}"; exit 0 ;;
        --format=json) OUTPUT_FORMAT="json" ;;
        --verbose) VERBOSE=true ;;
        --report=*) REPORT_FILE="${arg#--report=}" ;;
        *) if [[ -d "$arg" ]]; then SCAN_DIR="$arg"; fi ;;
    esac
done

# Handle --report FILE (two-arg form)
i=0
args=("$@")
while [[ $i -lt ${#args[@]} ]]; do
    if [[ "${args[$i]}" == "--report" && $((i+1)) -lt ${#args[@]} ]]; then
        REPORT_FILE="${args[$((i+1))]}"
    fi
    i=$((i + 1))
done

SCAN_DIR="$(cd "$SCAN_DIR" 2>/dev/null && pwd)" || { echo "Error: Cannot access directory"; exit 1; }

# Setup output capture
TMPDIR_AUDIT=$(mktemp -d)
trap 'rm -rf "$TMPDIR_AUDIT"' EXIT

TOTAL_CRITICAL=0
TOTAL_WARNING=0
TOTAL_INFO=0
SCANNER_RESULTS=()

run_scanner() {
    local name="$1" script="$2" args="${3:-}"
    local output_file="$TMPDIR_AUDIT/$name.txt"
    local exit_code=0

    echo -e "\n${BOLD}${CYAN}┌─────────────────────────────────────────┐${RESET}"
    echo -e "${BOLD}${CYAN}│  Running: $name${RESET}"
    echo -e "${BOLD}${CYAN}└─────────────────────────────────────────┘${RESET}"

    if [[ ! -x "$script" ]]; then
        echo -e "${RED}Script not found or not executable: $script${RESET}"
        return 1
    fi

    # Run scanner, capture output and exit code
    if $VERBOSE; then
        "$script" $args 2>&1 | tee "$output_file" || exit_code=$?
    else
        "$script" $args > "$output_file" 2>&1 || exit_code=$?
        # Show just summary lines
        grep -E '^\[|Summary|Total|Critical|Warning|Info|✅|❌|⚠️' "$output_file" 2>/dev/null || true
        # Show findings
        grep -E '^\[CRITICAL\]|\[WARNING\]|^\s*(❌|⚠️|✅)' "$output_file" 2>/dev/null | head -20 || true
    fi

    # Count findings from output
    local crit warn info
    crit=$(grep -c '\[CRITICAL\]\|\[EXPIRED\]' "$output_file" 2>/dev/null) || crit=0
    warn=$(grep -c '\[WARNING\]\|\[EXPIRING\]' "$output_file" 2>/dev/null) || warn=0
    info=$(grep -c '\[INFO\]\|\[VALID\]\|\[MISSING\]\|\[OK\]' "$output_file" 2>/dev/null) || info=0

    TOTAL_CRITICAL=$((TOTAL_CRITICAL + crit))
    TOTAL_WARNING=$((TOTAL_WARNING + warn))
    TOTAL_INFO=$((TOTAL_INFO + info))

    local status_icon="✅"
    [[ $exit_code -eq 1 ]] && status_icon="⚠️"
    [[ $exit_code -eq 2 ]] && status_icon="❌"

    SCANNER_RESULTS+=("$status_icon $name: ${crit} critical, ${warn} warnings, ${info} info")

    return 0
}

START_TIME=$(date +%s)
AUDIT_DATE=$(date '+%Y-%m-%d %H:%M:%S %Z')

echo -e "${BOLD}${CYAN}"
echo "╔═══════════════════════════════════════════════╗"
echo "║                                               ║"
echo "║    🛡️  ARC SENTINEL — Full Security Audit     ║"
echo "║                                               ║"
echo "╚═══════════════════════════════════════════════╝"
echo -e "${RESET}"
echo -e "  Date:      $AUDIT_DATE"
echo -e "  Target:    $SCAN_DIR"
echo -e "  Host:      $(hostname)"
echo -e "  User:      $(whoami)"
echo -e "  OS:        $(sw_vers -productName 2>/dev/null || echo 'Unknown') $(sw_vers -productVersion 2>/dev/null || echo '')"

# Run all scanners
run_scanner "Secret Scanner" "$SCRIPT_DIR/secret-scanner.sh" "$SCAN_DIR"
run_scanner "Permission Auditor" "$SCRIPT_DIR/permission-auditor.sh" ""
run_scanner "Skill Auditor" "$SCRIPT_DIR/skill-auditor.sh" ""
run_scanner "Token Watchdog" "$SCRIPT_DIR/token-watchdog.sh" ""
run_scanner "Git Hygiene" "$SCRIPT_DIR/git-hygiene.sh" "$SCAN_DIR"

END_TIME=$(date +%s)
DURATION=$((END_TIME - START_TIME))

# ── Combined Summary ──
echo ""
echo -e "${BOLD}${CYAN}"
echo "╔═══════════════════════════════════════════════╗"
echo "║           AUDIT SUMMARY                       ║"
echo "╚═══════════════════════════════════════════════╝"
echo -e "${RESET}"

TOTAL_FINDINGS=$((TOTAL_CRITICAL + TOTAL_WARNING + TOTAL_INFO))

echo -e "  ${BOLD}Scanner Results:${RESET}"
for result in "${SCANNER_RESULTS[@]}"; do
    echo -e "    $result"
done

echo ""
echo -e "  ${BOLD}Totals:${RESET}"
echo -e "    Total findings:  ${TOTAL_FINDINGS}"
echo -e "    ${RED}Critical:        ${TOTAL_CRITICAL}${RESET}"
echo -e "    ${YELLOW}Warnings:        ${TOTAL_WARNING}${RESET}"
echo -e "    ${GREEN}Info:            ${TOTAL_INFO}${RESET}"
echo -e "    Duration:        ${DURATION}s"
echo ""

# Overall verdict
if [[ $TOTAL_CRITICAL -gt 0 ]]; then
    echo -e "  ${RED}${BOLD}❌ VERDICT: CRITICAL issues found — immediate attention required${RESET}"
    OVERALL_EXIT=2
elif [[ $TOTAL_WARNING -gt 0 ]]; then
    echo -e "  ${YELLOW}${BOLD}⚠️  VERDICT: Warnings found — review recommended${RESET}"
    OVERALL_EXIT=1
else
    echo -e "  ${GREEN}${BOLD}✅ VERDICT: All clear — no security issues detected${RESET}"
    OVERALL_EXIT=0
fi

echo ""

# Machine-parseable summary (always output)
echo -e "${BOLD}Machine-parseable summary:${RESET}"
echo "---BEGIN-AUDIT-SUMMARY---"
echo "date=$AUDIT_DATE"
echo "target=$SCAN_DIR"
echo "host=$(hostname)"
echo "user=$(whoami)"
echo "duration=${DURATION}s"
echo "total_findings=$TOTAL_FINDINGS"
echo "critical=$TOTAL_CRITICAL"
echo "warnings=$TOTAL_WARNING"
echo "info=$TOTAL_INFO"
echo "exit_code=$OVERALL_EXIT"
for result in "${SCANNER_RESULTS[@]}"; do
    echo "scanner=$result"
done
echo "---END-AUDIT-SUMMARY---"

# Save report if requested
if [[ -n "$REPORT_FILE" ]]; then
    {
        echo "Arc Sentinel Full Audit Report"
        echo "=============================="
        echo "Date: $AUDIT_DATE"
        echo "Target: $SCAN_DIR"
        echo ""
        for f in "$TMPDIR_AUDIT"/*.txt; do
            [[ -f "$f" ]] || continue
            echo ""
            echo "=== $(basename "$f" .txt) ==="
            # Strip ANSI color codes for file output
            sed 's/\x1b\[[0-9;]*m//g' "$f"
        done
        echo ""
        echo "=== Summary ==="
        echo "Critical: $TOTAL_CRITICAL"
        echo "Warnings: $TOTAL_WARNING"
        echo "Info: $TOTAL_INFO"
        echo "Exit code: $OVERALL_EXIT"
    } > "$REPORT_FILE"
    echo -e "Report saved to: $REPORT_FILE"
fi

exit $OVERALL_EXIT
