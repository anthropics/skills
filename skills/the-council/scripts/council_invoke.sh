#!/usr/bin/env bash
# council_invoke.sh — Invoke Codex and Gemini in parallel, capture responses
#
# Usage: council_invoke.sh [--codex-only|--gemini-only] <prompt_file> [working_directory]
#   --codex-only:      Only invoke Codex (skip Gemini)
#   --gemini-only:     Only invoke Gemini (skip Codex)
#   prompt_file:       Path to a text file containing the advisory prompt
#   working_directory: defaults to current directory
#
# Outputs: Paths to response files (one per line, last lines of stdout)
#   Full mode:   codex response path, then gemini response path
#   Single mode: only the active advisor's response path
#
# Environment:
#   CODEX_MODEL    — Override Codex model (default: gpt-5.3-codex)
#   GEMINI_MODEL   — Override Gemini model (default: gemini-3-pro-preview)
#   COUNCIL_TIMEOUT — Max seconds to wait per advisor (default: 300)

set -euo pipefail

# --- Parse flags ---
RUN_CODEX=true
RUN_GEMINI=true

while [[ "${1:-}" == --* ]]; do
  case "$1" in
    --codex-only)
      RUN_GEMINI=false
      shift
      ;;
    --gemini-only)
      RUN_CODEX=false
      shift
      ;;
    *)
      echo "ERROR: Unknown flag: $1" >&2
      exit 1
      ;;
  esac
done

# --- Resolve timeout command (macOS compatibility) ---
if command -v gtimeout &>/dev/null; then
  TIMEOUT_CMD="gtimeout"
elif command -v timeout &>/dev/null; then
  TIMEOUT_CMD="timeout"
else
  # Fallback: no timeout enforcement
  TIMEOUT_CMD=""
fi

# --- Load nvm/node environment if needed (CLIs installed via npm) ---
export NVM_DIR="${NVM_DIR:-$HOME/.nvm}"
if [[ -s "$NVM_DIR/nvm.sh" ]]; then
  source "$NVM_DIR/nvm.sh" --no-use 2>/dev/null
  # Ensure the default node version's bin is in PATH
  NODE_BIN="$(nvm which default 2>/dev/null | xargs dirname 2>/dev/null)" || true
  if [[ -n "$NODE_BIN" && -d "$NODE_BIN" ]]; then
    export PATH="$NODE_BIN:$PATH"
  fi
fi

PROMPT_FILE="${1:?Usage: council_invoke.sh [--codex-only|--gemini-only] <prompt_file> [working_directory]}"
WORK_DIR="${2:-.}"
WORK_DIR="$(cd "$WORK_DIR" && pwd)"

CODEX_MODEL="${CODEX_MODEL:-gpt-5.3-codex}"
GEMINI_MODEL="${GEMINI_MODEL:-gemini-3-pro-preview}"
TIMEOUT_SECS="${COUNCIL_TIMEOUT:-300}"

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo "ERROR: Prompt file not found: $PROMPT_FILE" >&2
  exit 1
fi

# Verify required CLIs are available
if [[ "$RUN_CODEX" == "true" ]] && ! command -v codex &>/dev/null; then
  echo "ERROR: 'codex' not found in PATH. Install it or check your shell environment." >&2
  exit 1
fi
if [[ "$RUN_GEMINI" == "true" ]] && ! command -v gemini &>/dev/null; then
  echo "ERROR: 'gemini' not found in PATH. Install it or check your shell environment." >&2
  exit 1
fi

PROMPT="$(cat "$PROMPT_FILE")"
TIMESTAMP="$(date +%Y%m%d_%H%M%S)"
TMPDIR_COUNCIL="${TMPDIR:-/tmp}/council_${TIMESTAMP}"
mkdir -p "$TMPDIR_COUNCIL"

CODEX_OUT="$TMPDIR_COUNCIL/codex_response.md"
GEMINI_OUT="$TMPDIR_COUNCIL/gemini_response.md"
CODEX_ERR="$TMPDIR_COUNCIL/codex_error.log"
GEMINI_ERR="$TMPDIR_COUNCIL/gemini_error.log"

# Determine mode label
if [[ "$RUN_CODEX" == "true" && "$RUN_GEMINI" == "true" ]]; then
  MODE="Full Council"
elif [[ "$RUN_CODEX" == "true" ]]; then
  MODE="Codex-only"
else
  MODE="Gemini-only"
fi

echo "Invoking The Council ($MODE)..."
[[ "$RUN_CODEX" == "true" ]] && echo "  Codex model:  $CODEX_MODEL"
[[ "$RUN_GEMINI" == "true" ]] && echo "  Gemini model: $GEMINI_MODEL"
echo "  Working dir:  $WORK_DIR"
echo "  Timeout:      ${TIMEOUT_SECS}s (${TIMEOUT_CMD:-none})"
echo ""

# Helper: run a command with optional timeout
run_with_timeout() {
  if [[ -n "$TIMEOUT_CMD" ]]; then
    "$TIMEOUT_CMD" "$TIMEOUT_SECS" "$@"
  else
    "$@"
  fi
}

CODEX_PID=""
GEMINI_PID=""

# --- Invoke Codex (non-interactive, read-only sandbox) ---
if [[ "$RUN_CODEX" == "true" ]]; then
  (
    cd "$WORK_DIR"
    run_with_timeout codex exec \
      -m "$CODEX_MODEL" \
      --full-auto \
      --sandbox read-only \
      -o "$CODEX_OUT" \
      "$PROMPT" \
      2>"$CODEX_ERR" || {
        echo "Codex invocation failed (exit $?). See $CODEX_ERR" >&2
        echo "[Codex failed to respond. Check $CODEX_ERR for details.]" > "$CODEX_OUT"
      }
  ) &
  CODEX_PID=$!
fi

# --- Invoke Gemini (non-interactive, plan/read-only mode) ---
if [[ "$RUN_GEMINI" == "true" ]]; then
  (
    cd "$WORK_DIR"
    run_with_timeout gemini \
      -m "$GEMINI_MODEL" \
      --approval-mode plan \
      -p "$PROMPT" \
      --output-format text \
      > "$GEMINI_OUT" \
      2>"$GEMINI_ERR" || {
        echo "Gemini invocation failed (exit $?). See $GEMINI_ERR" >&2
        echo "[Gemini failed to respond. Check $GEMINI_ERR for details.]" > "$GEMINI_OUT"
      }
  ) &
  GEMINI_PID=$!
fi

# --- Wait for advisors ---
CODEX_STATUS=0
GEMINI_STATUS=0

if [[ -n "$CODEX_PID" ]]; then
  wait "$CODEX_PID" || CODEX_STATUS=$?
fi
if [[ -n "$GEMINI_PID" ]]; then
  wait "$GEMINI_PID" || GEMINI_STATUS=$?
fi

echo ""
echo "Council responses ready:"
if [[ "$RUN_CODEX" == "true" ]]; then
  echo "  Codex:  $CODEX_OUT $([ $CODEX_STATUS -eq 0 ] && echo '(success)' || echo '(failed)')"
fi
if [[ "$RUN_GEMINI" == "true" ]]; then
  echo "  Gemini: $GEMINI_OUT $([ $GEMINI_STATUS -eq 0 ] && echo '(success)' || echo '(failed)')"
fi
echo ""

# Output the paths for the caller to read
if [[ "$RUN_CODEX" == "true" ]]; then
  echo "$CODEX_OUT"
fi
if [[ "$RUN_GEMINI" == "true" ]]; then
  echo "$GEMINI_OUT"
fi
