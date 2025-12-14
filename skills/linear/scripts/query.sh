#!/bin/bash
#
# Shell wrapper for Linear GraphQL queries
#
# Usage:
#   LINEAR_API_KEY=lin_api_xxx ./query.sh "query { viewer { id name } }"
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [ -z "${LINEAR_API_KEY:-}" ]; then
  echo "Error: LINEAR_API_KEY environment variable is required" >&2
  echo "" >&2
  echo "Usage:" >&2
  echo "  LINEAR_API_KEY=lin_api_xxx ./query.sh \"query { viewer { id name } }\"" >&2
  exit 1
fi

npx tsx "$SCRIPT_DIR/query.ts" "$@"
