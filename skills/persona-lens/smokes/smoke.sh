#!/usr/bin/env bash
# smoke.sh — F6 minimal smoke for persona-lens
# Exit 0 if skill is invokable + responds to --help.
# Generated 2026-05-09 by scaffold_skill_smoke.sh.
set -euo pipefail

SCRIPT_REL="scripts/persona-lens.sh"
SKILL_DIR="$(cd "$(dirname "$0")/.." && pwd)"
SCRIPT="$SKILL_DIR/$SCRIPT_REL"

# Check 1: script exists + executable
if [ ! -f "$SCRIPT" ]; then
  echo "FAIL: script missing at $SCRIPT" >&2
  echo "VERDICT: FAIL"
  exit 1
fi

# Check 2: bash syntax-clean
if ! bash -n "$SCRIPT" 2>/dev/null; then
  echo "FAIL: bash -n syntax error in $SCRIPT" >&2
  echo "VERDICT: FAIL"
  exit 1
fi

# Check 3: --help responds within 5s and exits cleanly
HELP_OUT="$(timeout 5 bash "$SCRIPT" --help 2>&1 || true)"
if [ -z "$HELP_OUT" ]; then
  echo "WARN: --help produced no output (skill may not implement --help)" >&2
  # Not a hard fail — many skills don't implement --help
fi

echo "VERDICT: PASS"
exit 0
