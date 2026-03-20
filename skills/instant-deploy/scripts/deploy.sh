#!/usr/bin/env bash
# instant-deploy/scripts/deploy.sh — FIXED v2
# Usage: bash deploy.sh "Page Title"
# Env:   CLOUDFLARE_API_TOKEN (required)

set -euo pipefail

PAGE_TITLE="${1:-instant-page}"

# Slugify
SLUG=$(echo "$PAGE_TITLE" \
  | tr '[:upper:]' '[:lower:]' \
  | sed 's/[^a-z0-9 _-]//g' \
  | sed 's/[ _]\+/-/g' \
  | sed 's/-\+/-/g' \
  | sed 's/^-//; s/-$//' \
  | cut -c1-50)
SLUG="${SLUG:-instant-page}"

OUTPUT_DIR="${HOME}/deploy-output"

echo ""
echo "▶  instant-deploy"
echo "   Title   : $PAGE_TITLE"
echo "   Slug    : $SLUG"
echo "   Source  : $OUTPUT_DIR/"
echo ""

# ─── Validate ────────────────────────────────────────────────────────────────
if [[ -z "${CLOUDFLARE_API_TOKEN:-}" ]]; then
  echo "❌  CLOUDFLARE_API_TOKEN not set."
  echo "    export CLOUDFLARE_API_TOKEN=your_token"
  exit 1
fi

if [[ ! -f "$OUTPUT_DIR/index.html" ]]; then
  echo "❌  No index.html at $OUTPUT_DIR/index.html"
  exit 1
fi

# ─── Wrangler ────────────────────────────────────────────────────────────────
if ! command -v wrangler &>/dev/null; then
  echo "⚙   Installing wrangler..."
  npm install -g wrangler --silent
fi

# ─── Get account ID ──────────────────────────────────────────────────────────
echo "⚙   Fetching Cloudflare account..."
ACCOUNT_RESP=$(curl -sf "https://api.cloudflare.com/client/v4/accounts" \
  -H "Authorization: Bearer $CLOUDFLARE_API_TOKEN" \
  -H "Content-Type: application/json")

ACCOUNT_ID=$(echo "$ACCOUNT_RESP" | grep -o '"id":"[^"]*"' | head -1 | cut -d'"' -f4)

if [[ -z "$ACCOUNT_ID" ]]; then
  echo "❌  Could not fetch account ID. Check token permissions."
  exit 1
fi
echo "✓   Account: $ACCOUNT_ID"

# ─── Check / create project ──────────────────────────────────────────────────
echo "⚙   Checking project: $SLUG"

# Use HTTP status code — 200 = exists, anything else = needs creating
HTTP_STATUS=$(curl -s -o /dev/null -w "%{http_code}" \
  "https://api.cloudflare.com/client/v4/accounts/$ACCOUNT_ID/pages/projects/$SLUG" \
  -H "Authorization: Bearer $CLOUDFLARE_API_TOKEN")

if [[ "$HTTP_STATUS" == "200" ]]; then
  echo "✓   Project exists"
else
  echo "⚙   Creating project: $SLUG"
  CREATE=$(curl -s -X POST \
    "https://api.cloudflare.com/client/v4/accounts/$ACCOUNT_ID/pages/projects" \
    -H "Authorization: Bearer $CLOUDFLARE_API_TOKEN" \
    -H "Content-Type: application/json" \
    -d "{\"name\":\"$SLUG\",\"production_branch\":\"main\"}")

  if echo "$CREATE" | grep -q '"success":true'; then
    echo "✓   Project created"
  elif echo "$CREATE" | grep -q 'already exists'; then
    echo "✓   Project already exists"
  else
    echo "❌  Failed to create project:"
    echo "$CREATE" | grep -o '"message":"[^"]*"' | head -3 | sed 's/"message":"//g;s/"//g'
    exit 1
  fi
fi

# ─── Deploy ──────────────────────────────────────────────────────────────────
echo "🚀  Deploying..."
echo ""

DEPLOY_LOG=$(mktemp)

wrangler pages deploy "$OUTPUT_DIR" \
  --project-name "$SLUG" \
  --branch main \
  --commit-dirty=true \
  2>&1 | tee "$DEPLOY_LOG"

# ─── Extract URL ─────────────────────────────────────────────────────────────
LIVE_URL=$(grep -Eo 'https://[a-zA-Z0-9._-]+\.pages\.dev[^ ]*' "$DEPLOY_LOG" \
  | grep -v '\.wrangler\.' | tail -1 || true)

# Fallback to canonical project URL
[[ -z "$LIVE_URL" ]] && LIVE_URL="https://${SLUG}.pages.dev"

rm -f "$DEPLOY_LOG"

echo ""
echo "✅  LIVE: $LIVE_URL"
echo "$LIVE_URL" > /tmp/instant-deploy-url.txt
echo ""
