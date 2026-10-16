#!/usr/bin/env bash
# gauntlet.sh — Mechanical gate for gauntlet pass G1 (correctness).
#
# Port of harness's templates/modules/gauntlet/gauntlet.sh, generalised for
# standalone repos: specs default to `.specs/` and the traceability checker is
# resolved via --trace-tool, a packaged sibling (scripts/check_traceability.py)
# or the spec-driven-development sibling skill. Same protocol v1 JSON, same
# exit codes, same anti-vacuous guards.
#
# Verifies the checkable half of a feature before any judgment pass runs:
# the spec trio exists, every task is [x], and requirement traceability has
# no gaps. Semantic judgment (does the test really verify the requirement?)
# stays with the reviewer — this script only proves the mapping exists.
#
# Usage: gauntlet.sh --feature NAME [--root DIR] [--specs-dir DIR]
#                    [--trace-tool PATH] [--json]
# Exit codes: 0 = PASS (mechanical gates green), 1 = REJECT (gaps found),
#             2 = usage error (a verdict without per-feature evidence lines
#             is a vacuous PASS, and vacuous PASSes are refused)
#
# Protocol v1 JSON (--json): {"tool": "gauntlet", "protocol": 1, ...} first.

set -uo pipefail

FEATURE=""
ROOT="."
SPECS_DIR=""
SPECS_SET=0
TRACE_TOOL=""
JSON=0
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
IMPL_GLOBS=()

while [ $# -gt 0 ]; do
  case "$1" in
    --feature=*) FEATURE="${1#*=}" ;;
    --feature) shift; FEATURE="${1:-}" ;;
    --root=*) ROOT="${1#*=}" ;;
    --root) shift; ROOT="${1:-}" ;;
    --specs-dir=*) SPECS_DIR="${1#*=}"; SPECS_SET=1 ;;
    --specs-dir) shift; SPECS_DIR="${1:-}"; SPECS_SET=1 ;;
    --trace-tool=*) TRACE_TOOL="${1#*=}" ;;
    --trace-tool) shift; TRACE_TOOL="${1:-}" ;;
    --impl-glob=*) IMPL_GLOBS+=("${1#*=}") ;;
    --impl-glob) shift; IMPL_GLOBS+=("${1:-}") ;;
    --json) JSON=1 ;;
    -h|--help)
      echo "Usage: gauntlet.sh --feature NAME [--root DIR] [--specs-dir DIR] [--trace-tool PATH] [--impl-glob GLOB]... [--json]"
      exit 0 ;;
    *) echo "gauntlet.sh: unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

# Guard 1: a named feature is mandatory — bare invocations used to pass 0/0.
if [ -z "$FEATURE" ]; then
  echo "gauntlet.sh: --feature NAME is required (refusing a vacuous PASS)" >&2
  exit 2
fi
if [ ! -d "$ROOT" ]; then
  echo "gauntlet.sh: root is not a directory: $ROOT" >&2
  exit 2
fi
if [ "$SPECS_SET" -eq 0 ]; then
  SPECS_DIR="$ROOT/.specs"
fi

SPEC_DIR="$SPECS_DIR/$FEATURE"
REQ="$SPEC_DIR/requirements.md"
TASKS="$SPEC_DIR/tasks.md"
DESIGN="$SPEC_DIR/design.md"

GAPS=()
CHECKS=()  # entries as "name:ok" / "name:fail"

# Guard 2: the spec trio must exist before anything else counts.
for f in "$REQ" "$DESIGN" "$TASKS"; do
  if [ -f "$f" ]; then
    CHECKS+=("spec-$(basename "$f" .md):ok")
  else
    CHECKS+=("spec-$(basename "$f" .md):fail")
    GAPS+=("missing spec file: $f")
  fi
done
if [ ! -f "$REQ" ]; then
  GAPS+=("no requirements.md — nothing to trace, gauntlet stops here")
fi

# Check: no unchecked tasks remain.
DONE=0
TOTAL=0
if [ -f "$TASKS" ]; then
  TOTAL="$(grep -cE '^- \[[ xX]\] T[0-9]+' "$TASKS" || true)"
  DONE="$(grep -cE '^- \[[xX]\] T[0-9]+' "$TASKS" || true)"
  if [ "$TOTAL" -eq 0 ]; then
    CHECKS+=("tasks:fail")
    GAPS+=("tasks.md declares no T<n> tasks")
  elif [ "$DONE" -lt "$TOTAL" ]; then
    CHECKS+=("tasks:fail")
    GAPS+=("$((TOTAL - DONE)) of $TOTAL tasks still [ ] in $TASKS")
  else
    CHECKS+=("tasks:ok")
  fi
fi

# Check: traceability has no gaps (delegates to the traceability checker).
resolve_trace_tool() {
  if [ -n "$TRACE_TOOL" ]; then
    if [ ! -f "$TRACE_TOOL" ]; then
      return 1
    fi
    printf '%s' "$TRACE_TOOL"
    return 0
  fi
  if [ -f "$SCRIPT_DIR/check_traceability.py" ]; then
    printf '%s' "$SCRIPT_DIR/check_traceability.py"
    return 0
  fi
  if [ -f "$SCRIPT_DIR/../../spec-driven-development/scripts/check_traceability.py" ]; then
    printf '%s' "$SCRIPT_DIR/../../spec-driven-development/scripts/check_traceability.py"
    return 0
  fi
  return 1
}

TRACE_STATUS="skipped"
TRACE_ARGS=(--feature "$FEATURE" --root "$ROOT")
if [ "$SPECS_SET" -eq 1 ]; then
  TRACE_ARGS+=(--specs-dir "$SPECS_DIR")
fi
for g in ${IMPL_GLOBS[@]+"${IMPL_GLOBS[@]}"}; do
  TRACE_ARGS+=(--impl-glob "$g")
done
if command -v python3 >/dev/null 2>&1 && TRACE_TOOL="$(resolve_trace_tool)"; then
  TRACE_OUT="$(python3 "$TRACE_TOOL" "${TRACE_ARGS[@]}" 2>&1)"
  TRACE_RC=$?
  if [ "$TRACE_RC" -eq 0 ]; then
    # A verdict without a per-feature evidence line is a vacuous PASS.
    if printf '%s\n' "$TRACE_OUT" | grep -qE "^## $FEATURE: [0-9]+/[0-9]+"; then
      CHECKS+=("traceability:ok")
      TRACE_STATUS="ok"
    else
      CHECKS+=("traceability:fail")
      TRACE_STATUS="vacuous"
      GAPS+=("traceability verdict lacks a '## $FEATURE: n/n' evidence line")
    fi
  elif [ "$TRACE_RC" -eq 2 ]; then
    CHECKS+=("traceability:fail")
    TRACE_STATUS="usage-error"
    GAPS+=("traceability guard: $TRACE_OUT")
  else
    CHECKS+=("traceability:fail")
    TRACE_STATUS="gaps"
    GAPS+=("traceability gaps: $(printf '%s' "$TRACE_OUT" | tr '\n' ' ')")
  fi
else
  CHECKS+=("traceability:fail")
  GAPS+=("traceability checker not found (--trace-tool, packaged sibling, or spec-driven-development skill)")
fi

if [ "${#GAPS[@]}" -eq 0 ]; then VERDICT="PASS"; RC=0; else VERDICT="REJECT"; RC=1; fi

json_escape() {  # json_escape <string> — quote for embedding in JSON
  printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' ' '
}

if [ "$JSON" -eq 1 ]; then
  checks_json=""
  for c in ${CHECKS[@]+"${CHECKS[@]}"}; do
    n="${c%%:*}"; s="${c##*:}"
    checks_json="${checks_json:+$checks_json,}{\"name\": \"$n\", \"status\": \"$s\"}"
  done
  gaps_json=""
  for g in ${GAPS[@]+"${GAPS[@]}"}; do
    gaps_json="${gaps_json:+$gaps_json,}\"$(json_escape "$g")\""
  done
  printf '{"tool": "gauntlet", "protocol": 1, "feature": "%s", "verdict": "%s", "checks": [%s], "gaps": [%s]}\n' \
    "$(json_escape "$FEATURE")" "$VERDICT" "$checks_json" "$gaps_json"
else
  echo "# Gauntlet G1 — feature $FEATURE: $VERDICT"
  echo ""
  for c in ${CHECKS[@]+"${CHECKS[@]}"}; do echo "- $c"; done
  if [ "${#GAPS[@]}" -gt 0 ]; then
    echo ""
    echo "## Gaps"
    for g in ${GAPS[@]+"${GAPS[@]}"}; do echo "- $g"; done
  fi
  echo ""
  echo "Traceability detail: $TRACE_STATUS"
fi

exit "$RC"
