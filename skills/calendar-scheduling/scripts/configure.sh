#!/usr/bin/env bash
# configure.sh — Configure timezone and week start preferences
set -euo pipefail

CONFIG_DIR="${HOME}/.config/temporal-cortex"
CONFIG_FILE="${CONFIG_DIR}/config.json"

echo "=== Temporal Cortex Configuration ==="
echo ""

# Ensure config directory exists
mkdir -p "$CONFIG_DIR"

# Detect current timezone
if command -v python3 &>/dev/null; then
  DETECTED_TZ=$(python3 -c "
import subprocess, sys
try:
    result = subprocess.run(['readlink', '/etc/localtime'], capture_output=True, text=True)
    path = result.stdout.strip()
    if '/zoneinfo/' in path:
        print(path.split('/zoneinfo/')[-1])
    else:
        print('')
except Exception:
    print('')
" 2>/dev/null || echo "")
else
  DETECTED_TZ=""
fi

# Read existing config
if [[ -f "$CONFIG_FILE" ]]; then
  CURRENT_TZ=$(CONFIG_FILE="$CONFIG_FILE" python3 -c "import json, os; print(json.load(open(os.environ['CONFIG_FILE'])).get('timezone', ''))" 2>/dev/null || echo "")
  CURRENT_WS=$(CONFIG_FILE="$CONFIG_FILE" python3 -c "import json, os; print(json.load(open(os.environ['CONFIG_FILE'])).get('week_start', 'monday'))" 2>/dev/null || echo "monday")
  echo "Current configuration:"
  echo "  Timezone:   ${CURRENT_TZ:-not set}"
  echo "  Week start: ${CURRENT_WS}"
  echo ""
else
  CURRENT_TZ=""
  CURRENT_WS="monday"
fi

# Configure timezone
echo "--- Timezone ---"
if [[ -n "$DETECTED_TZ" ]]; then
  echo "Detected system timezone: ${DETECTED_TZ}"
fi

read -rp "Enter IANA timezone (e.g., America/New_York) [${CURRENT_TZ:-${DETECTED_TZ:-UTC}}]: " INPUT_TZ
TIMEZONE="${INPUT_TZ:-${CURRENT_TZ:-${DETECTED_TZ:-UTC}}}"

# Validate IANA timezone format (letters, digits, underscores, slashes, plus, minus)
if [[ ! "$TIMEZONE" =~ ^[A-Za-z0-9/_+-]+$ ]]; then
  echo "ERROR: Invalid timezone format: ${TIMEZONE}"
  echo "Expected IANA timezone like America/New_York or UTC"
  exit 1
fi

echo "Timezone set to: ${TIMEZONE}"
echo ""

# Configure week start
echo "--- Week Start ---"
echo "1) Monday (ISO 8601 standard)"
echo "2) Sunday"
read -rp "Choose week start [${CURRENT_WS}]: " INPUT_WS

case "${INPUT_WS,,}" in
  2|sunday|sun)
    WEEK_START="sunday"
    ;;
  *)
    WEEK_START="monday"
    ;;
esac

echo "Week start set to: ${WEEK_START}"
echo ""

# Write config
if [[ -f "$CONFIG_FILE" ]]; then
  # Update existing config preserving other fields
  CONFIG_FILE="$CONFIG_FILE" TIMEZONE="$TIMEZONE" WEEK_START="$WEEK_START" python3 -c "
import json, os
cf = os.environ['CONFIG_FILE']
config = json.load(open(cf))
config['timezone'] = os.environ['TIMEZONE']
config['week_start'] = os.environ['WEEK_START']
json.dump(config, open(cf, 'w'), indent=2)
print('Configuration updated.')
"
else
  # Create new config
  CONFIG_FILE="$CONFIG_FILE" TIMEZONE="$TIMEZONE" WEEK_START="$WEEK_START" python3 -c "
import json, os
cf = os.environ['CONFIG_FILE']
config = {'timezone': os.environ['TIMEZONE'], 'week_start': os.environ['WEEK_START']}
json.dump(config, open(cf, 'w'), indent=2)
print('Configuration created.')
"
fi

echo ""
echo "Saved to ${CONFIG_FILE}"
echo ""
echo "These can be overridden per-session with environment variables:"
echo "  TIMEZONE=${TIMEZONE}"
echo "  WEEK_START=${WEEK_START}"
