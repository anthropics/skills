#!/usr/bin/env bash
# lens-wiki-digest — generate per-lens markdown digest from the registry
#
# For each active (and candidate, when included) lens, write:
#   $LENSES_WIKI_DIR/<slug>.md   — per-lens state snapshot
#   $LENSES_WIKI_DIR/index.md    — grouped-by-bucket index
#
# Usage:
#   bash lens-wiki-digest.sh                          # all active + candidate
#   bash lens-wiki-digest.sh --week 2026-W18          # specific ISO week label
#   bash lens-wiki-digest.sh --lens steve-jobs        # single lens
#   bash lens-wiki-digest.sh --dry-run                # plan only
#   bash lens-wiki-digest.sh --selftest

set -uo pipefail

SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DB="${LENSES_DB_PATH:-$SKILL_DIR/data/persona-lens.db}"
WIKI_DIR="${LENSES_WIKI_DIR:-$SKILL_DIR/wiki}"
LOG_DIR="${LENSES_LOG_DIR:-$SKILL_DIR/logs}"
INTEL_DIR="${LENSES_INTEL_DIR:-$SKILL_DIR/intel}"
mkdir -p "$WIKI_DIR" "$LOG_DIR"

WEEK=$(date +%G-W%V)
LENS=""
DRY_RUN=0
SELFTEST=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --week)    WEEK="$2"; shift 2 ;;
    --lens)    LENS="$2"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    --selftest) SELFTEST=1; shift ;;
    --help|-h) sed -n '2,18p' "$0"; exit 0 ;;
    *) echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

log() { echo "[$(date +%H:%M:%S)] lens-wiki-digest: $*" >&2; }
_sq() { printf "%s" "$1" | sed "s/'/''/g"; }

# ---- Selftest ----
if (( SELFTEST )); then
  echo "[lens-wiki-digest] selftest: starting"
  st_tmp=$(mktemp -d -t lens-wiki-st.XXXXXX)
  export LENSES_DB_PATH="$st_tmp/persona-lens.db"
  export LENSES_DIR="$st_tmp/patterns"
  export LENSES_WIKI_DIR="$st_tmp/wiki"
  export LENSES_LOG_DIR="$st_tmp/logs"
  export LENSES_INTEL_DIR="$st_tmp/intel"

  bash "$SKILL_DIR/scripts/persona-lens.sh" add steve-jobs \
    --bucket founders --register founder-confident --rationale "first principles" --live >/dev/null
  bash "$SKILL_DIR/scripts/persona-lens.sh" add rick-rubin \
    --bucket producers --register quiet-mystic --rationale "less but better" --live >/dev/null

  bash "$SKILL_DIR/scripts/lens-wiki-digest.sh" 2>/dev/null

  if [[ -f "$st_tmp/wiki/index.md" && -f "$st_tmp/wiki/steve-jobs.md" && -f "$st_tmp/wiki/rick-rubin.md" ]]; then
    echo "[lens-wiki-digest] selftest: PASS"
    echo "  index: $st_tmp/wiki/index.md"
    rm -rf "$st_tmp"
    echo "VERDICT: PASS"
    exit 0
  else
    echo "[lens-wiki-digest] selftest: FAIL — missing wiki files"
    ls -la "$st_tmp/wiki/" 2>&1 || true
    rm -rf "$st_tmp"
    exit 1
  fi
fi

if [[ ! -f "$DB" ]]; then
  echo "ERROR: registry DB not found at $DB — add some lenses first" >&2
  exit 1
fi

POOL_SH="$SKILL_DIR/scripts/_lens-pool.sh"
ALL_LENSES=$(bash "$POOL_SH" --include-candidates 2>/dev/null | tr '\n' ' ')

if [[ -n "$LENS" ]]; then
  TARGET_LENSES="$LENS"
else
  TARGET_LENSES="$ALL_LENSES"
fi

write_lens_digest() {
  local slug="$1"
  local out_md="$WIKI_DIR/${slug}.md"
  local lens_id="${slug}-lens-v1"
  local lens_name lens_register body_size use_count vlm_avg promo
  lens_name=$(sqlite3 "$DB" "SELECT name FROM patterns WHERE id='$(_sq "$lens_id")'" 2>/dev/null)
  lens_register=$(sqlite3 "$DB" "SELECT register FROM patterns WHERE id='$(_sq "$lens_id")'" 2>/dev/null)
  body_size=$(sqlite3 "$DB" "SELECT length(body) FROM patterns WHERE id='$(_sq "$lens_id")'" 2>/dev/null)
  use_count=$(sqlite3 "$DB" "SELECT COALESCE(use_count,0) FROM patterns WHERE id='$(_sq "$lens_id")'" 2>/dev/null)
  vlm_avg=$(sqlite3 "$DB" "SELECT printf('%.2f', COALESCE(vlm_score_avg,0)) FROM patterns WHERE id='$(_sq "$lens_id")'" 2>/dev/null)
  promo=$(sqlite3 "$DB" "SELECT promotion_status FROM patterns WHERE id='$(_sq "$lens_id")'" 2>/dev/null)

  local sidecar_count=0
  if [[ -d "$INTEL_DIR/$slug" ]]; then
    sidecar_count=$(ls "$INTEL_DIR/$slug"/*.json 2>/dev/null | wc -l | tr -d ' ')
  fi

  local top_brands
  top_brands=$(sqlite3 "$DB" "SELECT brand, COUNT(*) AS uses FROM use_log WHERE pattern_id='$(_sq "$lens_id")' AND brand != '' GROUP BY brand ORDER BY uses DESC LIMIT 3" 2>/dev/null | sed 's/|/: /g; s/^/  - /')
  [[ -z "$top_brands" ]] && top_brands="  - (no use_log entries yet — fires when apply usage starts logging)"

  if (( DRY_RUN )); then
    log "DRY: would write $out_md (lens_name=$lens_name body=${body_size:-0}B sidecars=$sidecar_count)"
    return 0
  fi

  cat > "$out_md" << EOF
# ${lens_name:-$slug} — Lens Digest ${WEEK}

**Generated.** $(date +%Y-%m-%dT%H:%M:%S) by lens-wiki-digest
**Source.** persona-lens registry where persona_lens=${slug}

## State

| Metric | Value |
|---|---|
| Lens ID | \`$lens_id\` |
| Status | $promo |
| Register | $lens_register |
| Pattern body size | ${body_size:-0} bytes |
| Decompositions | $sidecar_count |
| Total uses (use_log) | $use_count |
| Avg VLM score | $vlm_avg |

## Top cross-brand applications

$top_brands

## Decompositions ($INTEL_DIR/${slug}/)

$(if [[ -d "$INTEL_DIR/$slug" ]]; then
    ls "$INTEL_DIR/$slug"/*.json 2>/dev/null | head -5 | while read -r f; do
      echo "- \`$(basename "$f")\`"
    done
  else
    echo "- (none yet — run lens-decomposer.sh --lens $slug --url ... --live to add)"
  fi)

## How to apply this lens

\`\`\`bash
bash scripts/lens-apply.sh --lens $slug --brand-dna /path/to/BRAND-DNA.md --use-case <slug>
\`\`\`
EOF

  echo "$out_md"
}

write_index() {
  local index_md="$WIKI_DIR/index.md"
  if (( DRY_RUN )); then log "DRY: would write $index_md"; return 0; fi

  local sections
  sections=$(sqlite3 "$DB" "SELECT bucket, persona_lens, promotion_status FROM patterns WHERE persona_lens != '' ORDER BY bucket, persona_lens" -separator '|||' | python3 -c "
import sys
from collections import defaultdict
groups = defaultdict(list)
for line in sys.stdin:
    parts = line.strip().split('|||')
    if len(parts) != 3: continue
    bucket, slug, status = parts
    groups[bucket].append((slug, status))
out = []
for bucket in sorted(groups.keys()):
    out.append(f'### {bucket.title()}')
    for slug, status in groups[bucket]:
        mark = '[active]' if status == 'active' else ('[candidate]' if status == 'candidate' else '[deprecated]')
        out.append(f'- {mark} [{slug}]({slug}.md)')
    out.append('')
print('\n'.join(out))
")

  local active_count candidate_count
  active_count=$(sqlite3 "$DB" "SELECT COUNT(*) FROM patterns WHERE persona_lens != '' AND promotion_status='active'")
  candidate_count=$(sqlite3 "$DB" "SELECT COUNT(*) FROM patterns WHERE persona_lens != '' AND promotion_status='candidate'")

  cat > "$index_md" << EOF
# Persona-Lens Wiki — Index ($(date +%Y-%m-%d))

**$active_count active + $candidate_count candidate lenses** queryable.

## Live registry

$sections

**Legend.** [active] in pool · [candidate] awaits promote · [deprecated] out of pool

## Commands

\`\`\`bash
bash scripts/persona-lens.sh add <slug> --bucket <X> --register <Y> --live
bash scripts/persona-lens.sh propose <slug> --by agent:scout --evidence <url> --live
bash scripts/persona-lens.sh promote <slug> --live
bash scripts/persona-lens.sh fuse <a> <b> --live
bash scripts/persona-lens.sh digest --bucket <X> --live
bash scripts/lens-apply.sh --lens <slug> --brand-dna PATH --use-case <X>
\`\`\`
EOF
  echo "$index_md"
}

log "week=$WEEK target_lenses=$(echo "$TARGET_LENSES" | wc -w | tr -d ' ')"

written=0
for slug in $TARGET_LENSES; do
  out=$(write_lens_digest "$slug")
  [[ -n "$out" ]] && written=$((written + 1))
done

if [[ -z "$LENS" ]]; then write_index; fi
log "DONE: $written lens digests written to $WIKI_DIR"
echo "$WIKI_DIR"
