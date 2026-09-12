#!/bin/bash
# Endpoints API helper script
# Requires: ENDPOINTS_API_URL, ENDPOINTS_API_KEY

set -e

# Validate environment
if [[ -z "$ENDPOINTS_API_URL" ]]; then
  echo "Error: ENDPOINTS_API_URL not set" >&2
  echo "Set it with: export ENDPOINTS_API_URL=https://endpoints.work" >&2
  exit 1
fi

if [[ -z "$ENDPOINTS_API_KEY" ]]; then
  echo "Error: ENDPOINTS_API_KEY not set" >&2
  echo "Generate an API key from your dashboard and set it with:" >&2
  echo "  export ENDPOINTS_API_KEY=ep_your_key_here" >&2
  exit 1
fi

AUTH="Authorization: Bearer $ENDPOINTS_API_KEY"

usage() {
  cat <<EOF
Endpoints API Helper

Usage: endpoints.sh <command> [arguments]

Commands:
  overview                      List all endpoints by category
  inspect <path>                Get endpoint details (e.g., /category/slug)
  scan-text <text> <prompt>     Scan text content with prompt
  scan-file <file> <prompt>     Scan file with prompt
  create <path>                 Create new empty endpoint
  delete <path>                 Delete endpoint and all its data
  delete-item <itemId>          Delete individual item by ID
  file-url <key>                Get presigned URL for file
  stats                         Show usage statistics

Environment:
  ENDPOINTS_API_URL             Base API URL (required)
  ENDPOINTS_API_KEY             API key with ep_ prefix (required)

Examples:
  endpoints.sh overview
  endpoints.sh inspect /job-tracker/january
  endpoints.sh scan-text "Meeting notes here" "meeting tracker"
  endpoints.sh scan-file ./invoice.pdf "invoice tracker"
  endpoints.sh create /receipts/2026
  endpoints.sh delete /category/slug
  endpoints.sh delete-item abc12345
  endpoints.sh stats
EOF
}

case "${1:-}" in
  overview)
    curl -s -H "$AUTH" "$ENDPOINTS_API_URL/api/endpoints/tree"
    ;;
  inspect)
    [[ -z "$2" ]] && { echo "Error: path required (e.g., /category/slug)"; exit 1; }
    path="${2#/}"  # Remove leading slash if present
    curl -s -H "$AUTH" "$ENDPOINTS_API_URL/api/endpoints/$path"
    ;;
  scan-text)
    [[ -z "$2" || -z "$3" ]] && { echo "Error: text and prompt required"; exit 1; }
    curl -s -X POST -H "$AUTH" \
      -F "texts=$2" \
      -F "prompt=$3" \
      "$ENDPOINTS_API_URL/api/scan"
    ;;
  scan-file)
    [[ -z "$2" || -z "$3" ]] && { echo "Error: file and prompt required"; exit 1; }
    [[ ! -f "$2" ]] && { echo "Error: file not found: $2"; exit 1; }
    curl -s -X POST -H "$AUTH" \
      -F "files=@$2" \
      -F "prompt=$3" \
      "$ENDPOINTS_API_URL/api/scan"
    ;;
  create)
    [[ -z "$2" ]] && { echo "Error: path required (e.g., /category/slug)"; exit 1; }
    curl -s -X POST -H "$AUTH" -H "Content-Type: application/json" \
      -d "{\"path\": \"$2\", \"items\": []}" \
      "$ENDPOINTS_API_URL/api/endpoints"
    ;;
  delete)
    [[ -z "$2" ]] && { echo "Error: path required (e.g., /category/slug)"; exit 1; }
    path="${2#/}"
    curl -s -X DELETE -H "$AUTH" "$ENDPOINTS_API_URL/api/endpoints/$path"
    ;;
  delete-item)
    [[ -z "$2" ]] && { echo "Error: itemId required (e.g., abc12345)"; exit 1; }
    curl -s -X DELETE -H "$AUTH" "$ENDPOINTS_API_URL/api/items/$2"
    ;;
  file-url)
    [[ -z "$2" ]] && { echo "Error: file key required"; exit 1; }
    curl -s -H "$AUTH" "$ENDPOINTS_API_URL/api/files/$2?format=json"
    ;;
  stats)
    curl -s -H "$AUTH" "$ENDPOINTS_API_URL/api/billing/stats"
    ;;
  --help|-h|"")
    usage
    ;;
  *)
    echo "Unknown command: $1" >&2
    usage
    exit 1
    ;;
esac
