#!/usr/bin/env bash
# arc-shield.sh - Output sanitization for agent responses
# Scans outbound messages for leaked secrets, tokens, keys, passwords, and PII

set -euo pipefail

VERSION="1.0.0"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONFIG_FILE="${ARC_SHIELD_CONFIG:-${SCRIPT_DIR}/../config/patterns.conf}"

# Mode flags
MODE="scan"  # scan, redact, report, strict
SEVERITY_THRESHOLD="WARN"  # WARN, HIGH, CRITICAL
FOUND_CRITICAL=0
FOUND_HIGH=0
FOUND_WARN=0

# Colors for output
RED='\033[0;31m'
YELLOW='\033[1;33m'
ORANGE='\033[0;33m'
NC='\033[0m' # No Color

usage() {
    cat << EOF
arc-shield ${VERSION} - Output sanitization for agent responses

USAGE:
    arc-shield.sh [OPTIONS] < input.txt
    echo "message" | arc-shield.sh [OPTIONS]

OPTIONS:
    --strict        Exit with code 1 if CRITICAL findings detected
    --redact        Replace detected secrets with [REDACTED]
    --report        Show findings report only (no output pass-through)
    --quiet         Suppress warnings, only show critical
    -h, --help      Show this help

MODES:
    Default: Scan and pass through with warnings to stderr
    --redact: Replace secrets and output sanitized text
    --report: Analyze and report findings only

EXAMPLES:
    # Scan agent output before sending
    agent-response.txt | arc-shield.sh --strict
    
    # Sanitize and replace secrets
    echo "My token is ghp_abc123" | arc-shield.sh --redact
    
    # Audit mode
    arc-shield.sh --report < conversation.log

EOF
    exit 0
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --strict) MODE="strict"; shift ;;
        --redact) MODE="redact"; shift ;;
        --report) MODE="report"; shift ;;
        --quiet) SEVERITY_THRESHOLD="CRITICAL"; shift ;;
        -h|--help) usage ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# Read input
INPUT=$(cat)

# Detection functions
detect_1password_tokens() {
    echo "$INPUT" | grep -oE 'ops_[a-zA-Z0-9_-]{40,}' || true
}

detect_github_pats() {
    echo "$INPUT" | grep -oE 'ghp_[a-zA-Z0-9]{32,}' || true
}

detect_openai_keys() {
    echo "$INPUT" | grep -oE 'sk-[a-zA-Z0-9]{20,}' || true
}

detect_stripe_keys() {
    echo "$INPUT" | grep -oE 'sk_(test|live)_[a-zA-Z0-9]{24,}' || true
}

detect_aws_keys() {
    echo "$INPUT" | grep -oE 'AKIA[0-9A-Z]{16}' || true
}

detect_bearer_tokens() {
    echo "$INPUT" | grep -oE 'Bearer [a-zA-Z0-9_\-\.]{20,}' || true
}

detect_passwords() {
    # Match password assignments and similar patterns
    # Use [[:space:]] for whitespace to be portable
    echo "$INPUT" | grep -iE '(password|passwd|pwd)[[:space:]"]*[:=][[:space:]"]*[^[:space:]"]{6,}' || true
}

detect_eth_private_keys() {
    # 0x followed by 64 hex chars
    echo "$INPUT" | grep -oE '0x[0-9a-fA-F]{64}' || true
}

detect_ssh_keys() {
    echo "$INPUT" | grep -E -- '-----BEGIN (RSA|OPENSSH|DSA|EC) PRIVATE KEY-----' || true
}

detect_pgp_blocks() {
    echo "$INPUT" | grep -E -- '-----BEGIN PGP PRIVATE KEY BLOCK-----' || true
}

detect_mnemonics() {
    # 12 or 24 word phrases (simplified detection)
    echo "$INPUT" | grep -iE '\b([a-z]{3,}[\s]+){11,23}[a-z]{3,}\b' | \
        grep -iwE '(abandon|ability|able|about|above|absent|absorb|abstract|absurd|abuse|access|accident|account|accuse|achieve|acid|acoustic|acquire|across|act|action|actor|actress|actual|adapt|add|addict|address|adjust|admit|adult|advance|advice|aerobic|affair|afford|afraid|again|age|agent|agree|ahead|aim|air|airport|aisle|alarm|album|alcohol|alert|alien|all|alley|allow|almost|alone|alpha|already|also|alter|always|amateur|amazing|among|amount|amused|analyst|anchor|ancient|anger|angle|angry|animal|ankle|announce|annual|another|answer|antenna|antique|anxiety|any|apart|apology|appear|apple|approve|april|arch|arctic|area|arena|argue|arm|armed|armor|army|around|arrange|arrest|arrive|arrow|art|artefact|artist|artwork|ask|aspect|assault|asset|assist|assume|asthma|athlete|atom|attack|attend|attitude|attract|auction|audit|august|aunt|author|auto|autumn|average|avocado|avoid|awake|aware|away|awesome|awful|awkward|axis|baby|bachelor|bacon|badge|bag|balance|balcony|ball|bamboo|banana|banner|bar|barely|bargain|barrel|base|basic|basket|battle|beach|bean|beauty|because|become|beef|before|begin|behave|behind|believe|below|belt|bench|benefit|best|betray|better|between|beyond|bicycle|bid|bike|bind|biology|bird|birth|bitter|black|blade|blame|blanket|blast|bleak|bless|blind|blood|blossom|blouse|blue|blur|blush|board|boat|body|boil|bomb|bone|bonus|book|boost|border|boring|borrow|boss|bottom|bounce|box|boy|bracket|brain|brand|brass|brave|bread|breeze|brick|bridge|brief|bright|bring|brisk|broccoli|broken|bronze|broom|brother|brown|brush|bubble|buddy|budget|buffalo|build|bulb|bulk|bullet|bundle|bunker|burden|burger|burst|bus|business|busy|butter|buyer|buzz)' || true
}

detect_secret_paths() {
    echo "$INPUT" | grep -E '(~\/\.secrets\/|\/\.?secrets?\/|[^\s]*\/(password|token|key|secret)[^\s]*\.[a-z]{2,4})' || true
}

detect_env_vars() {
    echo "$INPUT" | grep -E '^[A-Z_][A-Z0-9_]*=[^\s]{10,}' || true
}

detect_emails_sensitive() {
    # Only flag emails in sensitive contexts (near password, token, etc)
    echo "$INPUT" | grep -iB2 -A2 'password\|token\|secret\|key' | grep -oE '[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}' || true
}

detect_ssn() {
    echo "$INPUT" | grep -oE '\b[0-9]{3}-[0-9]{2}-[0-9]{4}\b' || true
}

detect_credit_cards() {
    echo "$INPUT" | grep -oE '\b[0-9]{4}[\s-]?[0-9]{4}[\s-]?[0-9]{4}[\s-]?[0-9]{4}\b' || true
}

detect_phone_numbers() {
    # Only in sensitive contexts
    echo "$INPUT" | grep -iB2 -A2 'password\|token\|secret\|2fa\|verification' | \
        grep -oE '(\+?1[\s.-]?)?\(?[0-9]{3}\)?[\s.-]?[0-9]{3}[\s.-]?[0-9]{4}' || true
}

# Report finding
report_finding() {
    local severity=$1
    local category=$2
    local matches=$3
    
    if [[ -z "$matches" ]]; then
        return
    fi
    
    case $severity in
        CRITICAL) ((FOUND_CRITICAL++)) ;;
        HIGH) ((FOUND_HIGH++)) ;;
        WARN) ((FOUND_WARN++)) ;;
    esac
    
    if [[ "$SEVERITY_THRESHOLD" == "CRITICAL" && "$severity" != "CRITICAL" ]]; then
        return
    fi
    
    local color=$NC
    case $severity in
        CRITICAL) color=$RED ;;
        HIGH) color=$ORANGE ;;
        WARN) color=$YELLOW ;;
    esac
    
    echo -e "${color}[${severity}]${NC} ${category}" >&2
    echo "$matches" | while IFS= read -r match; do
        # Truncate long matches for display
        if [[ ${#match} -gt 60 ]]; then
            match="${match:0:57}..."
        fi
        echo "  → ${match}" >&2
    done
}

# Redaction function
redact_patterns() {
    local text="$1"
    
    # Redact in order of specificity
    text=$(echo "$text" | sed -E 's/ops_[a-zA-Z0-9_-]{40,}/[REDACTED:1PASSWORD_TOKEN]/g')
    text=$(echo "$text" | sed -E 's/ghp_[a-zA-Z0-9]{32,}/[REDACTED:GITHUB_PAT]/g')
    text=$(echo "$text" | sed -E 's/sk-[a-zA-Z0-9]{20,}/[REDACTED:OPENAI_KEY]/g')
    text=$(echo "$text" | sed -E 's/sk_(test|live)_[a-zA-Z0-9]{24,}/[REDACTED:STRIPE_KEY]/g')
    text=$(echo "$text" | sed -E 's/AKIA[0-9A-Z]{16}/[REDACTED:AWS_KEY]/g')
    text=$(echo "$text" | sed -E 's/Bearer [a-zA-Z0-9_\-\.]{20,}/Bearer [REDACTED:TOKEN]/g')
    text=$(echo "$text" | sed -E 's/(password|passwd|pwd)([[:space:]"]*[:=][[:space:]"]*)[^[:space:]"]{6,}/[REDACTED:PASSWORD]/gI')
    text=$(echo "$text" | sed -E 's/0x[0-9a-fA-F]{64}/[REDACTED:PRIVATE_KEY]/g')
    text=$(echo "$text" | sed -E 's/-----BEGIN (RSA|OPENSSH|DSA|EC) PRIVATE KEY-----/-----BEGIN PRIVATE KEY [REDACTED]-----/g')
    text=$(echo "$text" | sed -E 's/~\/\.secrets\/[^\s]*/[REDACTED:SECRET_PATH]/g')
    text=$(echo "$text" | sed -E 's/[0-9]{3}-[0-9]{2}-[0-9]{4}/[REDACTED:SSN]/g')
    text=$(echo "$text" | sed -E 's/[0-9]{4}[\s-]?[0-9]{4}[\s-]?[0-9]{4}[\s-]?[0-9]{4}/[REDACTED:CC]/g')
    
    echo "$text"
}

# Main detection
main() {
    # Run all detectors
    local findings_1pass=$(detect_1password_tokens)
    local findings_github=$(detect_github_pats)
    local findings_openai=$(detect_openai_keys)
    local findings_stripe=$(detect_stripe_keys)
    local findings_aws=$(detect_aws_keys)
    local findings_bearer=$(detect_bearer_tokens)
    local findings_passwords=$(detect_passwords)
    local findings_eth=$(detect_eth_private_keys)
    local findings_ssh=$(detect_ssh_keys)
    local findings_pgp=$(detect_pgp_blocks)
    local findings_paths=$(detect_secret_paths)
    local findings_env=$(detect_env_vars)
    local findings_ssn=$(detect_ssn)
    local findings_cc=$(detect_credit_cards)
    
    # Report findings
    report_finding "CRITICAL" "1Password Service Account Token" "$findings_1pass"
    report_finding "CRITICAL" "GitHub Personal Access Token" "$findings_github"
    report_finding "CRITICAL" "OpenAI API Key" "$findings_openai"
    report_finding "CRITICAL" "Stripe API Key" "$findings_stripe"
    report_finding "CRITICAL" "AWS Access Key" "$findings_aws"
    report_finding "CRITICAL" "Bearer Token" "$findings_bearer"
    report_finding "CRITICAL" "Password Assignment" "$findings_passwords"
    report_finding "CRITICAL" "Ethereum Private Key" "$findings_eth"
    report_finding "CRITICAL" "SSH Private Key" "$findings_ssh"
    report_finding "CRITICAL" "PGP Private Key" "$findings_pgp"
    report_finding "CRITICAL" "Social Security Number" "$findings_ssn"
    report_finding "HIGH" "Credit Card Number" "$findings_cc"
    report_finding "WARN" "Secret File Path" "$findings_paths"
    report_finding "WARN" "Environment Variable Assignment" "$findings_env"
    
    # Mode-specific output
    if [[ "$MODE" == "report" ]]; then
        echo -e "\n=== ARC-SHIELD SCAN REPORT ===" >&2
        echo -e "CRITICAL: ${FOUND_CRITICAL}" >&2
        echo -e "HIGH: ${FOUND_HIGH}" >&2
        echo -e "WARN: ${FOUND_WARN}" >&2
    elif [[ "$MODE" == "redact" ]]; then
        redact_patterns "$INPUT"
    elif [[ "$MODE" == "strict" ]]; then
        echo "$INPUT"
        if [[ $FOUND_CRITICAL -gt 0 ]]; then
            echo -e "\n${RED}[BLOCKED]${NC} Critical secrets detected. Message blocked." >&2
            exit 1
        fi
    else
        # Default: pass through
        echo "$INPUT"
    fi
    
    # Exit code based on findings
    if [[ $FOUND_CRITICAL -gt 0 && "$MODE" == "strict" ]]; then
        exit 1
    fi
}

main
