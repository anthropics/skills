#!/usr/bin/env bash
# compuute-scan skill — thin wrapper around the hosted scan API.
#
# Usage:
#   bash scan.sh <github_url>
#
# Returns: pretty-printed JSON report from scan.compuute.se with severity
# counts, score, top findings, and the honest-framing _disclaimer field.
#
# Exit codes:
#   0 — scan completed (report printed to stdout)
#   1 — bad usage (missing or malformed URL argument)
#   2 — API error (HTTP non-2xx)
set -euo pipefail

REPO_URL="${1:-}"
if [ -z "$REPO_URL" ]; then
  echo "usage: bash scan.sh <github_url>" >&2
  echo "example: bash scan.sh https://github.com/modelcontextprotocol/servers" >&2
  exit 1
fi

case "$REPO_URL" in
  https://github.com/*) ;;
  *)
    echo "error: only public GitHub HTTPS URLs are supported" >&2
    exit 1
    ;;
esac

API="https://scan.compuute.se/v1/scan"
TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

HTTP_CODE="$(curl -sS -o "$TMP" -w '%{http_code}' \
  -X POST "$API" \
  -H 'Content-Type: application/json' \
  -H 'User-Agent: compuute-scan-skill/0.1' \
  --data "{\"repo_url\": \"$REPO_URL\"}")"

if [ "$HTTP_CODE" != "200" ]; then
  echo "error: scan API returned HTTP $HTTP_CODE" >&2
  cat "$TMP" >&2
  exit 2
fi

if command -v jq >/dev/null 2>&1; then
  jq . "$TMP"
else
  cat "$TMP"
fi
