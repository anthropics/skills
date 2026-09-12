#!/usr/bin/env bash
# council_preflight.sh — Check CLI availability and authentication
# Exit codes: 0 = at least one advisor available, 1 = none available
# Outputs key=value status lines to stdout
# Caches result in /tmp/council_preflight_<uid> for session reuse

set -euo pipefail

CACHE_FILE="/tmp/council_preflight_$(id -u)"

# Return cached result if fresh (less than 2 hours old)
if [[ -f "$CACHE_FILE" ]]; then
  FILE_AGE=$(( $(date +%s) - $(stat -f %m "$CACHE_FILE" 2>/dev/null || stat -c %Y "$CACHE_FILE" 2>/dev/null) ))
  if (( FILE_AGE < 7200 )); then
    cat "$CACHE_FILE"
    exit 0
  fi
fi

# Load nvm/node environment if needed
export NVM_DIR="${NVM_DIR:-$HOME/.nvm}"
if [[ -s "$NVM_DIR/nvm.sh" ]]; then
  source "$NVM_DIR/nvm.sh" --no-use 2>/dev/null
  NODE_BIN="$(nvm which default 2>/dev/null | xargs dirname 2>/dev/null)" || true
  if [[ -n "$NODE_BIN" && -d "$NODE_BIN" ]]; then
    export PATH="$NODE_BIN:$PATH"
  fi
fi

CODEX_INSTALLED=false
CODEX_AUTHENTICATED=false
GEMINI_INSTALLED=false
GEMINI_AUTHENTICATED=false

# --- Check Codex CLI ---
if command -v codex &>/dev/null; then
  CODEX_INSTALLED=true
  # Check for OpenAI API key in env or config
  if [[ -n "${OPENAI_API_KEY:-}" ]] || [[ -f "$HOME/.codex/config.toml" ]]; then
    CODEX_AUTHENTICATED=true
  fi
fi

# --- Check Gemini CLI ---
if command -v gemini &>/dev/null; then
  GEMINI_INSTALLED=true
  # Check for Google credentials (OAuth or API key)
  if [[ -n "${GEMINI_API_KEY:-}" ]] || [[ -n "${GOOGLE_API_KEY:-}" ]] \
     || [[ -d "$HOME/.gemini" && -f "$HOME/.gemini/settings.json" ]]; then
    GEMINI_AUTHENTICATED=true
  fi
fi

# Build result
RESULT="CODEX_INSTALLED=$CODEX_INSTALLED
CODEX_AUTHENTICATED=$CODEX_AUTHENTICATED
GEMINI_INSTALLED=$GEMINI_INSTALLED
GEMINI_AUTHENTICATED=$GEMINI_AUTHENTICATED"

# Cache and output
echo "$RESULT" > "$CACHE_FILE"
echo "$RESULT"

# At least one advisor must be ready
if [[ "$CODEX_AUTHENTICATED" == "true" || "$GEMINI_AUTHENTICATED" == "true" ]]; then
  exit 0
else
  exit 1
fi
