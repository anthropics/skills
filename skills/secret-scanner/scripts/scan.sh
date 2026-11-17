#!/usr/bin/env bash
# secret-scanner: high-precision scan for leaked credentials.
#
# See ../SKILL.md for when and how to use this. See
# ../reference/patterns.md for the pattern catalog and rationale.
#
# Exit codes:
#   0  clean
#   1  one or more high-confidence matches
#   2  usage / IO error

set -u

usage() {
    cat <<'EOF'
Usage:
  scan.sh --diff [--staged|--working]   Scan a git diff (default: staged)
  scan.sh --stdin                       Scan text piped on stdin
  scan.sh --dir <path>                  Scan a directory, honoring .gitignore
  scan.sh <file> [<file> ...]           Scan one or more files
  scan.sh --self-test                   Run built-in fixtures; assert hits/misses
  scan.sh --help                        Show this message

Output:
  Each finding is printed as:
    <path>:<line>  <pattern-name>  <masked-preview>

  Secrets are masked to first four + last four characters. The full
  secret is never printed.

Allowlist:
  A line containing "secret-scanner: ignore" is skipped. Use it on
  the offending line, or on the line immediately above it (the same
  suppression comment format used by most linters).
EOF
}

# --- pattern catalog -------------------------------------------------
# Each entry: "<name>|<extended-regex>"
# Keep in sync with reference/patterns.md.
PATTERNS=(
    "AWS access key ID|\\b(AKIA|ASIA)[0-9A-Z]{16}\\b"
    "AWS secret access key (assignment)|(aws_secret_access_key|AWS_SECRET_ACCESS_KEY)[[:space:]]*[=:][[:space:]]*['\"]?[A-Za-z0-9/+=]{40}['\"]?"
    "GitHub personal access token (classic)|\\bghp_[A-Za-z0-9]{36}\\b"
    "GitHub fine-grained PAT|\\bgithub_pat_[A-Za-z0-9_]{82}\\b"
    "GitHub OAuth token|\\bgho_[A-Za-z0-9]{36}\\b"
    "GitHub app / refresh token|\\b(ghu|ghs|ghr)_[A-Za-z0-9]{36}\\b"
    "Slack bot / user token|\\bxox[baprs]-[A-Za-z0-9-]{10,72}\\b"
    "Slack webhook URL|https://hooks\\.slack\\.com/services/T[A-Z0-9]+/B[A-Z0-9]+/[A-Za-z0-9]+"
    "Stripe live secret key|\\bsk_live_[0-9a-zA-Z]{24,}\\b"
    "Stripe live restricted key|\\brk_live_[0-9a-zA-Z]{24,}\\b"
    "OpenAI API key|\\bsk-(proj-)?[A-Za-z0-9_-]{20,}T3BlbkFJ[A-Za-z0-9_-]{20,}\\b"
    "Anthropic API key|\\bsk-ant-(api|admin)[0-9]{2}-[A-Za-z0-9_-]{80,}\\b"
    "Google API key|AIza[0-9A-Za-z_-]{35}"
    "GCP service account (JSON header)|\"type\"[[:space:]]*:[[:space:]]*\"service_account\""
    "OpenSSH / RSA private key|-----BEGIN (RSA |EC |DSA |OPENSSH |PGP )?PRIVATE KEY-----"
    "PKCS#8 private key|-----BEGIN ENCRYPTED PRIVATE KEY-----"
    "JWT (three-part)|\\beyJ[A-Za-z0-9_-]{10,}\\.[A-Za-z0-9_-]{10,}\\.[A-Za-z0-9_-]{10,}\\b"
    "Generic secret-shaped assignment|(password|passwd|secret|api[_-]?key|access[_-]?token|auth[_-]?token)[[:space:]]*[=:][[:space:]]*['\"][^'\"[:space:]]{16,}['\"]"
)

# --- helpers ---------------------------------------------------------

mask() {
    # first 4 + ellipsis + last 4; if the match is short, mask fully.
    local s="$1" n
    n=${#s}
    if [ "$n" -le 8 ]; then
        printf '%s' "$(printf '%*s' "$n" '' | tr ' ' '*')"
    else
        printf '%s…%s' "${s:0:4}" "${s: -4}"
    fi
}

# Return 0 if the line (or the line immediately preceding it in $file)
# carries the ignore marker.
is_allowlisted() {
    local file="$1" lineno="$2" content="$3"
    case "$content" in
        *"secret-scanner: ignore"*) return 0 ;;
    esac
    if [ "$file" != "<stdin>" ] && [ "$lineno" -gt 1 ] && [ -f "$file" ]; then
        local prev
        prev=$(sed -n "$((lineno - 1))p" "$file" 2>/dev/null || true)
        case "$prev" in
            *"secret-scanner: ignore"*) return 0 ;;
        esac
    fi
    return 1
}

# Print findings for a single file (or "<stdin>") given its content
# on stdin. Emits one finding per matching (line, pattern) pair.
scan_stream() {
    local label="$1"
    local content
    content=$(cat)

    local lineno=0
    local hits=0
    while IFS= read -r line; do
        lineno=$((lineno + 1))
        for entry in "${PATTERNS[@]}"; do
            local name="${entry%%|*}"
            local regex="${entry#*|}"
            local matches
            # grep -oE prints each match on its own line
            matches=$(printf '%s\n' "$line" | grep -oE -- "$regex" 2>/dev/null || true)
            [ -z "$matches" ] && continue
            if is_allowlisted "$label" "$lineno" "$line"; then
                continue
            fi
            while IFS= read -r m; do
                [ -z "$m" ] && continue
                printf '%s:%d  %s  %s\n' "$label" "$lineno" "$name" "$(mask "$m")"
                hits=$((hits + 1))
            done <<<"$matches"
        done
    done <<<"$content"

    return "$hits"
}

# --- entry points ----------------------------------------------------

scan_file() {
    local f="$1"
    [ -f "$f" ] || { echo "scan.sh: not a file: $f" >&2; return 2; }
    scan_stream "$f" <"$f"
}

scan_dir() {
    local d="$1"
    [ -d "$d" ] || { echo "scan.sh: not a directory: $d" >&2; return 2; }
    local total=0
    local files
    if git -C "$d" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
        files=$(git -C "$d" ls-files)
        while IFS= read -r rel; do
            [ -z "$rel" ] && continue
            local abs="$d/$rel"
            [ -f "$abs" ] || continue
            scan_file "$abs"
            total=$((total + $?))
        done <<<"$files"
    else
        while IFS= read -r -d '' abs; do
            scan_file "$abs"
            total=$((total + $?))
        done < <(find "$d" -type f -print0)
    fi
    return "$total"
}

scan_diff() {
    local mode="${1:-staged}"
    local diff_cmd
    case "$mode" in
        staged)  diff_cmd="git diff --cached --unified=0" ;;
        working) diff_cmd="git diff HEAD --unified=0" ;;
        *) echo "scan.sh: unknown diff mode: $mode" >&2; return 2 ;;
    esac
    # Only scan added lines (leading '+' but not '+++' header).
    $diff_cmd | awk '/^\+\+\+ /{next} /^\+/{sub(/^\+/,""); print}' \
        | scan_stream "<diff:$mode>"
}

self_test() {
    # Fixtures. Each line is one of:
    #   HIT|<sample>    scanner must produce at least one finding
    #   MISS|<sample>   scanner must produce no findings
    # Blank fixture lines are ignored. Ordering matters — do not place
    # an "ignore" MISS immediately before a HIT, or the allowlist rule
    # will suppress it.
    # Fixtures are built at runtime from concatenated parts so that
    # no literal secret-shaped token appears in the source file. This
    # keeps GitHub's push-protection scanner from flagging our own
    # test data as a leaked credential.
    local aws_hit sample_gh sample_slack sample_stripe sample_gcp sample_jwt
    aws_hit='AKIA'"IOSFODNN7EXAMPLE"
    sample_gh='ghp'"_1234567890abcdefghijklmnopqrstuvwxyz"
    sample_slack='xoxb'"-1234567890-1234567890-abcdefghijklmnopqrstuv"
    sample_stripe='sk'"_live_abcdef0123456789ABCDEFXYZ"
    sample_gcp='AIza'"SyA-1234567890abcdefghijklmnopqrstuv"
    sample_jwt='eyJhbGciOiJIUzI1NiJ9'"."'eyJzdWIiOiJ0ZXN0In0'"."'abcdefgHIJKLmnop'
    local fixtures=(
        "HIT|$aws_hit"
        "MISS|this is just prose talking about AKIA prefixes"
        "HIT|$sample_gh"
        "HIT|$sample_slack"
        "HIT|$sample_stripe"
        "HIT|$sample_gcp"
        "HIT|$sample_jwt"
        'HIT|password = "correct-horse-battery-staple-42"'
        'HIT|-----BEGIN RSA PRIVATE KEY-----'
        'MISS|password = "x"'
        "MISS|${aws_hit}  secret-scanner: ignore"
    )
    local tmp
    tmp=$(mktemp)
    local i=1
    declare -A expect_hit expect_miss
    for entry in "${fixtures[@]}"; do
        local kind="${entry%%|*}"
        local sample="${entry#*|}"
        printf '%s\n' "$sample" >>"$tmp"
        case "$kind" in
            HIT)  expect_hit[$i]=1 ;;
            MISS) expect_miss[$i]=1 ;;
        esac
        i=$((i + 1))
    done
    local out
    out=$(scan_file "$tmp" || true)
    printf '%s\n' "$out"
    local ok=0 fail=0
    for ln in "${!expect_hit[@]}"; do
        if printf '%s\n' "$out" | grep -q "^$tmp:$ln  "; then
            ok=$((ok + 1))
        else
            printf 'MISSING expected hit on line %s\n' "$ln" >&2
            fail=$((fail + 1))
        fi
    done
    for ln in "${!expect_miss[@]}"; do
        if printf '%s\n' "$out" | grep -q "^$tmp:$ln  "; then
            printf 'UNEXPECTED hit on MISS line %s\n' "$ln" >&2
            fail=$((fail + 1))
        else
            ok=$((ok + 1))
        fi
    done
    rm -f "$tmp"
    printf 'self-test: %d passed, %d failed\n' "$ok" "$fail"
    [ "$fail" -eq 0 ]
}

# --- dispatch --------------------------------------------------------

[ "$#" -eq 0 ] && { usage; exit 2; }

hits=0
case "$1" in
    -h|--help) usage; exit 0 ;;
    --self-test) self_test; exit $? ;;
    --stdin) scan_stream "<stdin>"; hits=$?; ;;
    --diff)
        shift
        mode="staged"
        [ "${1:-}" = "--staged" ] && mode="staged" && shift
        [ "${1:-}" = "--working" ] && mode="working" && shift
        scan_diff "$mode"; hits=$?; ;;
    --dir)
        shift
        [ "${1:-}" ] || { echo "scan.sh: --dir needs a path" >&2; exit 2; }
        scan_dir "$1"; hits=$?; ;;
    *)
        for f in "$@"; do
            scan_file "$f"
            hits=$((hits + $?))
        done
        ;;
esac

[ "$hits" -gt 0 ] && exit 1
exit 0
