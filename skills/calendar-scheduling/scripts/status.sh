#!/usr/bin/env bash
# status.sh — Check Temporal Cortex MCP server connection health
set -euo pipefail

CONFIG_DIR="${HOME}/.config/temporal-cortex"
CONFIG_FILE="${CONFIG_DIR}/config.json"
CREDS_FILE="${CONFIG_DIR}/credentials.json"

echo "=== Temporal Cortex Status ==="
echo ""

# 1. Check Node.js
echo "--- Runtime ---"
if command -v node &>/dev/null; then
  echo "  Node.js: $(node -v)"
else
  echo "  Node.js: NOT FOUND (required for npx)"
fi

if command -v npx &>/dev/null; then
  echo "  npx:     available"
else
  echo "  npx:     NOT FOUND"
fi

echo ""

# 2. Check credentials
echo "--- Credentials ---"
if [[ -f "$CREDS_FILE" ]]; then
  echo "  Credentials file: ${CREDS_FILE}"

  # List configured providers
  if command -v python3 &>/dev/null; then
    python3 -c "
import json
creds = json.load(open('${CREDS_FILE}'))
providers = set()
for key in creds:
    if key.endswith('_client'):
        providers.add(key.replace('_client', ''))
    elif key == 'access_token' or key == 'refresh_token':
        providers.add('google')
    elif '_' in key:
        providers.add(key.split('_')[0])
for p in sorted(providers):
    if p not in ('access', 'refresh', 'token', 'client', 'expiry'):
        print(f'  Provider: {p}')
" 2>/dev/null || echo "  (unable to parse credentials)"
  fi
else
  echo "  Credentials file: NOT FOUND"
  echo "  Run: bash scripts/setup.sh"
fi

echo ""

# 3. Check configuration
echo "--- Configuration ---"
if [[ -f "$CONFIG_FILE" ]]; then
  echo "  Config file: ${CONFIG_FILE}"

  if command -v python3 &>/dev/null; then
    python3 -c "
import json
config = json.load(open('${CONFIG_FILE}'))
tz = config.get('timezone', 'not set')
ws = config.get('week_start', 'monday')
providers = config.get('providers', {})
print(f'  Timezone:   {tz}')
print(f'  Week start: {ws}')
if providers:
    for name, info in providers.items():
        enabled = info.get('enabled', False)
        status = 'enabled' if enabled else 'disabled'
        print(f'  Provider:   {name} ({status})')
" 2>/dev/null || echo "  (unable to parse config)"
  fi
else
  echo "  Config file: NOT FOUND"
  echo "  Run: bash scripts/configure.sh"
fi

echo ""

# 4. Environment overrides
echo "--- Environment Overrides ---"
if [[ -n "${TIMEZONE:-}" ]]; then
  echo "  TIMEZONE=${TIMEZONE}"
else
  echo "  TIMEZONE: not set (using config/OS detection)"
fi

if [[ -n "${WEEK_START:-}" ]]; then
  echo "  WEEK_START=${WEEK_START}"
else
  echo "  WEEK_START: not set (using config default)"
fi

if [[ -n "${HTTP_PORT:-}" ]]; then
  echo "  HTTP_PORT=${HTTP_PORT} (HTTP transport enabled)"
else
  echo "  HTTP_PORT: not set (stdio transport)"
fi

echo ""

# 5. Summary
echo "--- Summary ---"
if [[ -f "$CREDS_FILE" ]] && command -v npx &>/dev/null; then
  echo "  Status: READY"
  echo "  All 11 MCP tools available"
elif command -v npx &>/dev/null; then
  echo "  Status: PARTIAL"
  echo "  Layer 1 tools available (temporal context, no calendar access)"
  echo "  Run: bash scripts/setup.sh"
else
  echo "  Status: NOT READY"
  echo "  Install Node.js 18+ from https://nodejs.org"
fi
