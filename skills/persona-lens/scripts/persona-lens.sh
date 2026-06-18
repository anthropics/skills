#!/usr/bin/env bash
# persona-lens — dynamic lens registry CLI
#
# A self-contained lens-decomposition registry: add / propose / promote /
# deprecate / fuse / digest / list lenses against a local SQLite DB.
#
# SAFETY: Mutating verbs (add/propose/promote/deprecate/fuse/digest) default
# to DRY-RUN. Add --live to actually mutate the DB. Read-only verbs (list,
# help, --selftest) fire normally.
#
# Storage:
#   $LENSES_DB_PATH   — SQLite path. Default: <skill>/data/persona-lens.db
#   $LENSES_DIR       — Lens-markdown bodies. Default: <skill>/patterns/lenses/
#   $LENSES_INTEL_DIR — Digest outputs. Default: <skill>/intel/
#   $LENSES_LOG_DIR   — Event logs. Default: <skill>/logs/
#
# LLM (used by `digest` only):
#   $PERSONA_LENS_LLM_API_KEY — falls back to $GEMINI_API_KEY
#   $PERSONA_LENS_LLM_MODEL   — defaults to gemini-2.5-flash
#
# Usage:
#   persona-lens.sh add <slug> --name "X" --bucket founders --register founder-confident --live
#   persona-lens.sh propose <slug> --by agent:scout --evidence <url> --bucket performers --live
#   persona-lens.sh promote <slug> --live
#   persona-lens.sh deprecate <slug> --live
#   persona-lens.sh fuse <slug-a> <slug-b> [--name "A x B"] [--bucket hybrid] --live
#   persona-lens.sh digest --bucket founders [--via gemini-2.5-flash] --live
#   persona-lens.sh list [--bucket X --status Y --proposed-by Z] [--format table|json]
#   persona-lens.sh --selftest
#
# Without --live, mutating verbs print what they WOULD do and exit cleanly.

set -uo pipefail

SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# --- Paths (env-overridable, default to skill-local) -----------------
DB="${LENSES_DB_PATH:-$SKILL_DIR/data/persona-lens.db}"
LENSES_DIR="${LENSES_DIR:-$SKILL_DIR/patterns/lenses}"
INTEL_DIR="${LENSES_INTEL_DIR:-$SKILL_DIR/intel}"
LOG_DIR="${LENSES_LOG_DIR:-$SKILL_DIR/logs}"
mkdir -p "$(dirname "$DB")" "$LENSES_DIR" "$INTEL_DIR" "$LOG_DIR"

# --- DB schema bootstrap ---------------------------------------------
_ensure_db() {
  sqlite3 "$DB" <<'SQL'
CREATE TABLE IF NOT EXISTS patterns (
  id TEXT PRIMARY KEY,
  name TEXT NOT NULL,
  pattern_type TEXT NOT NULL DEFAULT 'persona',
  use_case TEXT,
  intent_tags TEXT,
  tool_targets TEXT,
  language TEXT DEFAULT 'en',
  register TEXT,
  director_persona TEXT,
  era TEXT,
  persona_lens TEXT NOT NULL,
  bucket TEXT NOT NULL,
  promotion_status TEXT NOT NULL DEFAULT 'active',
  proposed_by TEXT,
  evidence_url TEXT,
  source_url TEXT,
  source_creator TEXT,
  source_date TEXT,
  source_provenance TEXT,
  parent_id TEXT,
  validated_status TEXT,
  notes TEXT,
  body TEXT,
  body_path TEXT,
  vlm_score_avg REAL,
  use_count INTEGER DEFAULT 0,
  created_at TEXT DEFAULT (datetime('now')),
  updated_at TEXT DEFAULT (datetime('now'))
);
CREATE INDEX IF NOT EXISTS idx_patterns_lens   ON patterns(persona_lens);
CREATE INDEX IF NOT EXISTS idx_patterns_bucket ON patterns(bucket);
CREATE INDEX IF NOT EXISTS idx_patterns_status ON patterns(promotion_status);

CREATE TABLE IF NOT EXISTS use_log (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  pattern_id TEXT NOT NULL,
  brand TEXT,
  use_case TEXT,
  vlm_score REAL,
  notes TEXT,
  at TEXT DEFAULT (datetime('now'))
);
CREATE INDEX IF NOT EXISTS idx_use_log_pattern ON use_log(pattern_id);
SQL
}
_ensure_db

VERB="${1:-help}"; shift || true

# --- --live opt-in safety guard --------------------------------------
PL_LIVE=0
_filtered=()
for arg in "$@"; do
  if [[ "$arg" == "--live" ]]; then
    PL_LIVE=1
  else
    _filtered+=("$arg")
  fi
done
set -- ${_filtered[@]+"${_filtered[@]}"}

_pl_is_mutating() {
  case "$1" in
    add|propose|promote|deprecate|fuse|digest) return 0 ;;
    *) return 1 ;;
  esac
}

if _pl_is_mutating "$VERB" && (( PL_LIVE == 0 )); then
  echo "[persona-lens] MODE: dry-run (add --live to fire)" >&2
  echo "[persona-lens]   verb: $VERB" >&2
  echo "[persona-lens]   args: $*" >&2
  case "$VERB" in
    digest)  echo "[persona-lens]   estimated cost: ~\$0.005-0.02 (LLM call)" >&2 ;;
    add|propose|fuse) echo "[persona-lens]   would write: SQLite registry + markdown stub at $LENSES_DIR/" >&2 ;;
    promote|deprecate) echo "[persona-lens]   would update: patterns.promotion_status in $DB" >&2 ;;
  esac
  echo "[persona-lens] No mutation made." >&2
  exit 0
fi

(( PL_LIVE == 1 )) && echo "[persona-lens] MODE: LIVE (firing $VERB for real)" >&2

log() { echo "[$(date +%H:%M:%S)] persona-lens: $*" >&2; }

# --- sqlite single-quote escape --------------------------------------
_sq() { printf "%s" "$1" | sed "s/'/''/g"; }

cmd_help() {
  sed -n '2,36p' "$0"
  exit 0
}

# ---- add ----
cmd_add() {
  local slug="${1:-}"; shift || { echo "ERROR: slug required" >&2; exit 1; }
  local name="" bucket="" register="" intent_tags="[]" rationale=""
  local promotion_status="active" proposed_by="user:cli" evidence_url=""

  while [[ $# -gt 0 ]]; do
    case "$1" in
      --name)         name="$2"; shift 2 ;;
      --bucket)       bucket="$2"; shift 2 ;;
      --register)     register="$2"; shift 2 ;;
      --intent-tags)  intent_tags="$2"; shift 2 ;;
      --rationale)    rationale="$2"; shift 2 ;;
      --status)       promotion_status="$2"; shift 2 ;;
      --by)           proposed_by="$2"; shift 2 ;;
      --evidence)     evidence_url="$2"; shift 2 ;;
      *) echo "Unknown: $1" >&2; exit 1 ;;
    esac
  done

  [[ -z "$name" ]] && name="${slug} — thought-leader lens"
  [[ -z "$bucket" ]] && { echo "ERROR: --bucket required (founders|storytellers|designers|performers|hybrid|emerging|dtc-playbook|...)" >&2; exit 1; }
  [[ -z "$register" ]] && { echo "ERROR: --register required" >&2; exit 1; }

  local id="${slug}-lens-v1"
  local md_file="$LENSES_DIR/${slug}-lens-v1.md"
  mkdir -p "$(dirname "$md_file")"

  cat > "$md_file" << EOF
---
id: ${id}
name: ${name}
pattern_type: persona
use_case: thought-leader-lens
intent_tags: ${intent_tags}
tool_targets: ["claude","gpt","headline-gen","copy-rewrite","video-script-gen"]
language: en
register: ${register}
director_persona: ""
era: ""
persona_lens: ${slug}
bucket: ${bucket}
promotion_status: ${promotion_status}
proposed_by: ${proposed_by}
evidence_url: ${evidence_url}
source_url: ${evidence_url}
source_creator: persona-lens (registry add)
source_date: $(date +%Y-%m-%d)
source_provenance: derived
validated_status: experimental
notes: Added via persona-lens.sh add by ${proposed_by}. ${rationale}
---

# ${name}

**Bucket.** ${bucket}
**Register.** ${register}
**Status.** ${promotion_status}
**Added by.** ${proposed_by}
**Why.** ${rationale:-Pending decomposition via lens-decomposer.sh}

Body will populate via lens-decomposer.sh on seed URLs.
EOF

  # UPSERT into SQLite
  local body
  body=$(cat "$md_file")
  local id_sq name_sq register_sq bucket_sq prop_sq pby_sq evid_sq notes_sq body_sq lens_sq
  id_sq=$(_sq "$id"); name_sq=$(_sq "$name"); register_sq=$(_sq "$register")
  bucket_sq=$(_sq "$bucket"); prop_sq=$(_sq "$promotion_status")
  pby_sq=$(_sq "$proposed_by"); evid_sq=$(_sq "$evidence_url")
  notes_sq=$(_sq "$rationale"); body_sq=$(_sq "$body"); lens_sq=$(_sq "$slug")

  sqlite3 "$DB" <<SQL
INSERT INTO patterns (id, name, pattern_type, use_case, intent_tags, tool_targets, language, register, persona_lens, bucket, promotion_status, proposed_by, evidence_url, source_url, source_provenance, validated_status, notes, body, body_path)
VALUES ('$id_sq', '$name_sq', 'persona', 'thought-leader-lens', '$(_sq "$intent_tags")', '["claude","gpt"]', 'en', '$register_sq', '$lens_sq', '$bucket_sq', '$prop_sq', '$pby_sq', '$evid_sq', '$evid_sq', 'derived', 'experimental', '$notes_sq', '$body_sq', '$(_sq "$md_file")')
ON CONFLICT(id) DO UPDATE SET
  name=excluded.name,
  register=excluded.register,
  bucket=excluded.bucket,
  promotion_status=excluded.promotion_status,
  proposed_by=excluded.proposed_by,
  body=excluded.body,
  body_path=excluded.body_path,
  notes=excluded.notes,
  updated_at=datetime('now');
SQL

  log "lens added: $slug ($bucket / $register / $promotion_status)"
  echo "{\"slug\":\"$slug\",\"id\":\"$id\",\"bucket\":\"$bucket\",\"status\":\"$promotion_status\",\"by\":\"$proposed_by\",\"file\":\"$md_file\"}"
}

# ---- propose (agent path) ----
cmd_propose() {
  local slug="${1:-}"; shift || { echo "ERROR: slug required" >&2; exit 1; }
  local by_arg="agent:unknown"

  local found_by=0
  for arg in "$@"; do
    if (( found_by )); then by_arg="$arg"; break; fi
    if [[ "$arg" == "--by" ]]; then found_by=1; fi
  done
  if [[ $# -gt 0 && "$1" != --* && "$found_by" -eq 0 ]]; then
    by_arg="$1"; shift
  fi
  cmd_add "$slug" --status candidate --by "$by_arg" "$@"
  log "PROPOSED: $slug by $by_arg — promote with: persona-lens.sh promote $slug --live"
  echo "$(date +%Y-%m-%dT%H:%M:%S),propose,$slug,$by_arg" >> "$LOG_DIR/persona-lens-events.log"
}

# ---- read current promotion_status ----
_pl_read_status() {
  local slug="$1"
  if [[ ! -f "$DB" ]]; then echo ""; return 0; fi
  sqlite3 "$DB" "SELECT promotion_status FROM patterns WHERE persona_lens='$(_sq "$slug")' LIMIT 1;" 2>/dev/null
}

cmd_promote() {
  local slug="${1:-}"; [[ -z "$slug" ]] && { echo "ERROR: slug required" >&2; exit 1; }
  local current; current=$(_pl_read_status "$slug")
  if [[ -z "$current" ]]; then
    echo "[persona-lens] ERROR: lens not found in registry: $slug" >&2; exit 1
  fi
  if [[ "$current" == "active" ]]; then
    echo "[persona-lens] noop: $slug already active" >&2; exit 0
  fi
  if [[ "$current" == "deprecated" ]]; then
    echo "[persona-lens] ERROR: cannot resurrect deprecated lens $slug — add fresh slug" >&2; exit 1
  fi
  sqlite3 "$DB" "UPDATE patterns SET promotion_status='active', updated_at=datetime('now') WHERE persona_lens='$(_sq "$slug")'"
  echo "$(date +%Y-%m-%dT%H:%M:%S),promote,$slug,from=$current" >> "$LOG_DIR/persona-lens-events.log"
  log "promoted: $slug ($current → active)"
  echo "{\"slug\":\"$slug\",\"status\":\"active\",\"from\":\"$current\"}"
}

cmd_deprecate() {
  local slug="${1:-}"; [[ -z "$slug" ]] && { echo "ERROR: slug required" >&2; exit 1; }
  local current; current=$(_pl_read_status "$slug")
  if [[ -z "$current" ]]; then
    echo "[persona-lens] ERROR: lens not found in registry: $slug" >&2; exit 1
  fi
  if [[ "$current" == "deprecated" ]]; then
    echo "[persona-lens] noop: $slug already deprecated" >&2; exit 0
  fi
  sqlite3 "$DB" "UPDATE patterns SET promotion_status='deprecated', updated_at=datetime('now') WHERE persona_lens='$(_sq "$slug")'"
  echo "$(date +%Y-%m-%dT%H:%M:%S),deprecate,$slug,from=$current" >> "$LOG_DIR/persona-lens-events.log"
  log "deprecated: $slug ($current → deprecated)"
  echo "{\"slug\":\"$slug\",\"status\":\"deprecated\",\"from\":\"$current\"}"
}

# ---- fuse ----
cmd_fuse() {
  local a="${1:-}" b="${2:-}"; shift 2 2>/dev/null || true
  [[ -z "$a" || -z "$b" ]] && { echo "ERROR: usage: fuse <a> <b> [--name X] [--bucket Y]" >&2; exit 1; }

  local fused_name="${a}-x-${b}" bucket="hybrid"
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --name)   fused_name=$(echo "$2" | tr ' ' '-' | tr 'A-Z' 'a-z'); shift 2 ;;
      --bucket) bucket="$2"; shift 2 ;;
      *) echo "Unknown: $1" >&2; exit 1 ;;
    esac
  done

  local fused_slug="$fused_name"
  local body_a body_b register_a register_b
  body_a=$(sqlite3 "$DB" "SELECT body FROM patterns WHERE persona_lens='$(_sq "$a")'")
  body_b=$(sqlite3 "$DB" "SELECT body FROM patterns WHERE persona_lens='$(_sq "$b")'")
  register_a=$(sqlite3 "$DB" "SELECT register FROM patterns WHERE persona_lens='$(_sq "$a")'")
  register_b=$(sqlite3 "$DB" "SELECT register FROM patterns WHERE persona_lens='$(_sq "$b")'")

  [[ -z "$body_a" ]] && { echo "ERROR: lens not found: $a" >&2; exit 1; }
  [[ -z "$body_b" ]] && { echo "ERROR: lens not found: $b" >&2; exit 1; }

  local md_file="$LENSES_DIR/${fused_slug}-lens-v1.md"
  cat > "$md_file" << EOF
---
id: ${fused_slug}-lens-v1
name: ${a} × ${b} — hybrid lens
pattern_type: persona
use_case: thought-leader-lens
intent_tags: ["hybrid","fusion","cross-lens"]
tool_targets: ["claude","gpt","headline-gen","copy-rewrite"]
language: en
register: ${register_a}-${register_b}-hybrid
persona_lens: ${fused_slug}
bucket: ${bucket}
promotion_status: candidate
proposed_by: agent:fusion
parent_id: ${a}-lens-v1,${b}-lens-v1
validated_status: experimental
notes: Fusion lens combining $a and $b.
---

# ${a} × ${b} — Hybrid Lens

**Composition rule.** Take **${a}**'s structural skeleton (narrative arc, opening
move, framework_used) and apply **${b}**'s vocabulary register, blocked words,
and design restraint over it. Energy and humor follow ${b}; framework and
contrarian-take follow ${a}.

## Component A — ${a} body
\`\`\`
${body_a}
\`\`\`

## Component B — ${b} body
\`\`\`
${body_b}
\`\`\`

## Fusion guidance

When applying via lens-apply.sh:
1. Use A.narrative.* (arc, opening_move, framework)
2. Use B.vocabulary.* (register, signature_phrases override A, blocked_words union)
3. Use B.design.* (composition_pref, typography, restraint principles)
4. Use B.creative_direction.energy_level + humor_register
5. Use A.creative_direction.first_principles_anchor + contrarian_take
EOF

  # Persist fused lens via UPSERT
  local body_full; body_full=$(cat "$md_file")
  sqlite3 "$DB" <<SQL
INSERT INTO patterns (id, name, pattern_type, use_case, language, register, persona_lens, bucket, promotion_status, proposed_by, parent_id, validated_status, notes, body, body_path)
VALUES ('$(_sq "${fused_slug}-lens-v1")', '$(_sq "${a} × ${b} — hybrid lens")', 'persona', 'thought-leader-lens', 'en', '$(_sq "${register_a}-${register_b}-hybrid")', '$(_sq "$fused_slug")', '$(_sq "$bucket")', 'candidate', 'agent:fusion', '$(_sq "${a}-lens-v1,${b}-lens-v1")', 'experimental', '$(_sq "Fusion lens combining $a and $b.")', '$(_sq "$body_full")', '$(_sq "$md_file")')
ON CONFLICT(id) DO UPDATE SET
  body=excluded.body,
  updated_at=datetime('now');
SQL

  echo "$(date +%Y-%m-%dT%H:%M:%S),fuse,$fused_slug,parents=$a+$b" >> "$LOG_DIR/persona-lens-events.log"
  log "fused: $a × $b → $fused_slug (status=candidate)"
  echo "{\"slug\":\"$fused_slug\",\"parents\":[\"$a\",\"$b\"],\"status\":\"candidate\",\"file\":\"$md_file\"}"
}

# ---- digest (extract 底层逻辑 via LLM) ----
cmd_digest() {
  local bucket="" model="${PERSONA_LENS_LLM_MODEL:-${GEMINI_MODEL:-gemini-2.5-flash}}"
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --bucket) bucket="$2"; shift 2 ;;
      --via)    model="$2"; shift 2 ;;
      *) echo "Unknown: $1" >&2; exit 1 ;;
    esac
  done
  [[ -z "$bucket" ]] && { echo "ERROR: --bucket required" >&2; exit 1; }

  local key="${PERSONA_LENS_LLM_API_KEY:-${GEMINI_API_KEY:-}}"
  if [[ -z "$key" ]]; then
    echo "ERROR: PERSONA_LENS_LLM_API_KEY (or GEMINI_API_KEY) not set" >&2
    exit 2
  fi

  log "digesting bucket=$bucket via $model — finding 底层逻辑 (first principles)"

  local bodies
  bodies=$(sqlite3 "$DB" "SELECT body FROM patterns WHERE bucket='$(_sq "$bucket")' AND promotion_status='active' AND persona_lens != ''" -separator $'\n\n---LENS---\n\n')

  if [[ -z "$bodies" ]]; then
    echo "ERROR: no active lenses found in bucket=$bucket" >&2
    exit 3
  fi

  local out_md="$INTEL_DIR/${bucket}-meta-pattern-$(date +%Y-%m-%d).md"
  local prompt_tmp raw_tmp
  prompt_tmp=$(mktemp -t lens-digest-prompt.XXXXXX)
  raw_tmp=$(mktemp -t lens-digest-raw.XXXXXX)

  cat > "$prompt_tmp" << PROMPTEOF
You are a meta-pattern extraction engine. Below are the decomposed lenses for the "${bucket}" bucket. Each is decomposed into a 30-field schema (narrative · vocabulary · design · meta_text · creative_direction).

Find the 底层逻辑 (underlying logic / first principles) shared across these lenses. Output as a JSON object:

{
  "bucket": "${bucket}",
  "shared_principles": ["3-5 first-principles common to all lenses in this bucket"],
  "shared_narrative_arcs": ["arc patterns appearing in 3+ lenses"],
  "shared_vocabulary_register": ["register types overlapping"],
  "shared_signature_phrases": ["phrases appearing across 2+ lenses"],
  "differentiators": ["the 1-2 things that distinguish each lens within the bucket"],
  "meta_template": "A 1-paragraph 'starter template' that any new lens in this bucket should fit.",
  "candidate_seed_creators": ["3-5 creator names who fit this meta-pattern but aren't yet in registry"]
}

Decomposed lenses for bucket=${bucket}:

${bodies}

Return JSON only, no commentary.
PROMPTEOF

  local payload
  payload=$(python3 -c "
import json
text = open('$prompt_tmp').read()
print(json.dumps({
  'contents': [{'parts': [{'text': text}]}],
  'generationConfig': {'response_mime_type': 'application/json', 'temperature': 0.4}
}))
")

  local http_code
  for attempt in 1 2 3; do
    http_code=$(curl -sS -w '%{http_code}' -o "$raw_tmp" -X POST \
      "https://generativelanguage.googleapis.com/v1beta/models/${model}:generateContent?key=${key}" \
      -H 'Content-Type: application/json' -d "$payload" 2>&1) || true
    [[ "$http_code" == "200" ]] && break
    [[ "$http_code" =~ ^5 ]] && { log "LLM $model HTTP $http_code attempt $attempt — backoff"; sleep "$attempt"; }
  done

  if [[ "$http_code" != "200" ]]; then
    echo "ERROR: LLM HTTP $http_code" >&2
    head -c 500 "$raw_tmp" >&2; echo >&2
    rm -f "$prompt_tmp" "$raw_tmp"
    exit 5
  fi

  python3 -c "
import json
d = json.load(open('$raw_tmp'))
txt = d.get('candidates',[{}])[0].get('content',{}).get('parts',[{}])[0].get('text','')
try:
    print(json.dumps(json.loads(txt), indent=2, ensure_ascii=False))
except Exception:
    print(txt)
" > "$out_md.json"

  cat > "$out_md" << EOF
# ${bucket} bucket — 底层逻辑 (meta-pattern) $(date +%Y-%m-%d)

**Generated.** $(date +%Y-%m-%dT%H:%M:%S) by persona-lens.sh digest
**Model.** ${model}
**Lenses analyzed.** $(sqlite3 "$DB" "SELECT COUNT(*) FROM patterns WHERE bucket='$(_sq "$bucket")' AND promotion_status='active'")

## Meta-pattern (JSON)

\`\`\`json
$(cat "$out_md.json")
\`\`\`

## How to use

When proposing future ${bucket} lenses, inject this meta-pattern as constraint.
A new ${bucket} lens that doesn't match these shared_principles → low-confidence
candidate, requires manual review.

When fusing lenses, prefer within-bucket pairs (they share the meta-pattern,
fusion produces coherent hybrid).
EOF

  rm -f "$prompt_tmp" "$raw_tmp"
  echo "$(date +%Y-%m-%dT%H:%M:%S),digest,$bucket,$model" >> "$LOG_DIR/persona-lens-events.log"
  log "digest written: $out_md (+ $out_md.json)"
  echo "$out_md"
}

# ---- list ----
cmd_list() {
  local bucket="" status="" proposed_by="" format="table"
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --bucket)      bucket="$2"; shift 2 ;;
      --status)      status="$2"; shift 2 ;;
      --proposed-by) proposed_by="$2"; shift 2 ;;
      --format)      format="$2"; shift 2 ;;
      *) echo "Unknown: $1" >&2; exit 1 ;;
    esac
  done

  local where_parts="persona_lens != ''"
  [[ -n "$bucket" ]]      && where_parts="$where_parts AND bucket='$(_sq "$bucket")'"
  [[ -n "$status" ]]      && where_parts="$where_parts AND promotion_status='$(_sq "$status")'"
  [[ -n "$proposed_by" ]] && where_parts="$where_parts AND proposed_by='$(_sq "$proposed_by")'"
  local where_clause="WHERE $where_parts"

  case "$format" in
    json)
      sqlite3 -json "$DB" "SELECT persona_lens, bucket, promotion_status, register, proposed_by, length(body) as body_len, vlm_score_avg, use_count FROM patterns $where_clause ORDER BY bucket, persona_lens"
      ;;
    *)
      sqlite3 -column -header "$DB" "SELECT persona_lens, bucket, promotion_status, register, proposed_by, length(body) as body, vlm_score_avg as vlm, use_count as uses FROM patterns $where_clause ORDER BY bucket, persona_lens"
      ;;
  esac
}

# ---- selftest ----
cmd_selftest() {
  echo "[persona-lens] selftest: starting (DB=$DB)"
  local tmpdb tmpdir
  tmpdir=$(mktemp -d -t persona-lens-selftest.XXXXXX)
  tmpdb="$tmpdir/persona-lens.db"

  # Re-invoke this script with overridden paths
  export LENSES_DB_PATH="$tmpdb"
  export LENSES_DIR="$tmpdir/patterns"
  export LENSES_INTEL_DIR="$tmpdir/intel"
  export LENSES_LOG_DIR="$tmpdir/logs"

  # Re-source the same script (idempotent) — we'll just shell out
  local self="$0"

  echo "  [1/6] add steve-jobs (dry-run)"
  bash "$self" add steve-jobs --bucket founders --register founder-confident --rationale "first principles" >/dev/null
  echo "  [2/6] add steve-jobs (live)"
  bash "$self" add steve-jobs --bucket founders --register founder-confident --rationale "first principles" --live >/dev/null
  echo "  [3/6] add rick-rubin (live)"
  bash "$self" add rick-rubin --bucket producers --register quiet-mystic --rationale "less but better" --live >/dev/null
  echo "  [4/6] list active (json)"
  local count; count=$(bash "$self" list --format json 2>/dev/null | python3 -c "import json,sys; print(len(json.load(sys.stdin)))" 2>/dev/null || echo 0)
  echo "      → $count lenses in registry"
  if [[ "$count" -lt 2 ]]; then echo "FAIL: expected ≥2 lenses, got $count"; exit 1; fi

  echo "  [5/6] fuse steve-jobs × rick-rubin (live)"
  bash "$self" fuse steve-jobs rick-rubin --live >/dev/null

  echo "  [6/6] deprecate rick-rubin (live)"
  bash "$self" deprecate rick-rubin --live >/dev/null
  local depr; depr=$(bash "$self" list --status deprecated --format json 2>/dev/null | python3 -c "import json,sys; print(len(json.load(sys.stdin)))" 2>/dev/null || echo 0)
  if [[ "$depr" -lt 1 ]]; then echo "FAIL: expected ≥1 deprecated lens, got $depr"; exit 1; fi

  rm -rf "$tmpdir"
  echo "[persona-lens] selftest: PASS"
  echo "VERDICT: PASS"
}

# ---- dispatch ----
case "$VERB" in
  add)        cmd_add "$@" ;;
  propose)    cmd_propose "$@" ;;
  promote)    cmd_promote "$@" ;;
  deprecate)  cmd_deprecate "$@" ;;
  fuse)       cmd_fuse "$@" ;;
  digest)     cmd_digest "$@" ;;
  list)       cmd_list "$@" ;;
  --selftest|selftest) cmd_selftest ;;
  help|-h|--help|"") cmd_help ;;
  *)
    echo "ERROR: unknown verb '$VERB'" >&2
    cmd_help
    ;;
esac
