#!/usr/bin/env bash
# _lens-pool.sh — emit live list of active lens slugs from the registry
#
# Used internally by lens-wiki-digest.sh to populate the digest set from
# the live registry (not a hardcoded list).
#
# Usage:
#   bash _lens-pool.sh                                # all active
#   bash _lens-pool.sh --bucket founders              # active in bucket
#   bash _lens-pool.sh --include-candidates           # active + candidate
#   bash _lens-pool.sh --format lines|json            # output shape

set -uo pipefail

SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DB="${LENSES_DB_PATH:-$SKILL_DIR/data/persona-lens.db}"

BUCKET=""
INCLUDE_CANDIDATES=0
FORMAT="lines"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --bucket)               BUCKET="$2"; shift 2 ;;
    --include-candidates)   INCLUDE_CANDIDATES=1; shift ;;
    --format)               FORMAT="$2"; shift 2 ;;
    *) echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

[[ ! -f "$DB" ]] && { echo "WARN: registry DB not found at $DB — run an add first" >&2; exit 0; }

_sq() { printf "%s" "$1" | sed "s/'/''/g"; }

where="persona_lens != ''"
if (( INCLUDE_CANDIDATES )); then
  where="$where AND promotion_status IN ('active','candidate')"
else
  where="$where AND promotion_status='active'"
fi
[[ -n "$BUCKET" ]] && where="$where AND bucket='$(_sq "$BUCKET")'"

slugs=$(sqlite3 "$DB" "SELECT persona_lens FROM patterns WHERE $where ORDER BY bucket, persona_lens")

case "$FORMAT" in
  lines)
    echo "$slugs"
    ;;
  json)
    echo "$slugs" | python3 -c "import json, sys; print(json.dumps([l.strip() for l in sys.stdin if l.strip()]))"
    ;;
  *)
    echo "ERROR: --format must be lines | json" >&2; exit 1 ;;
esac
