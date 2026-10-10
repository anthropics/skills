#!/usr/bin/env bash
# lens-decomposer — URL / transcript → 30-field thought-leader-lens decomposition
#
# Input: YouTube URL OR transcript file OR bulk CSV
# Pipeline:
#   1. Fetch transcript (yt-dlp for YT auto-subs; curl+strip for other URLs)
#   2. Send transcript + 30-field schema → LLM (default: gemini-2.5-flash)
#   3. Receive JSON
#   4. Append decomposition section to lens markdown + UPSERT registry
#
# Usage:
#   bash lens-decomposer.sh --url "https://youtube.com/watch?v=X" --lens steve-jobs --live
#   bash lens-decomposer.sh --transcript /path/to/text.txt --lens hormozi --live
#   bash lens-decomposer.sh --bulk-csv urls.csv --max-cost 1.00 --live
#
# Env:
#   PERSONA_LENS_LLM_API_KEY   — falls back to $GEMINI_API_KEY
#   PERSONA_LENS_LLM_MODEL     — defaults to gemini-2.5-flash
#   LENSES_DB_PATH             — registry SQLite. Defaults to <skill>/data/persona-lens.db
#   LENSES_DIR                 — lens-markdown bodies. Defaults to <skill>/patterns/lenses
#   LENSES_INTEL_DIR           — decomposition JSON sidecars. Defaults to <skill>/intel
#   PERSONA_LENS_SCHEMA_PATH   — schema JSON for the decomposition. Defaults to <skill>/schemas/lens-30field.json
#
# Cost (rough): ~$0.005/decomposition with Gemini flash · 100-URL bulk ≈ $0.50.

set -uo pipefail

SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DB="${LENSES_DB_PATH:-$SKILL_DIR/data/persona-lens.db}"
LENSES_DIR="${LENSES_DIR:-$SKILL_DIR/patterns/lenses}"
INTEL_DIR="${LENSES_INTEL_DIR:-$SKILL_DIR/intel}"
LOG_DIR="${LENSES_LOG_DIR:-$SKILL_DIR/logs}"
SCHEMA="${PERSONA_LENS_SCHEMA_PATH:-$SKILL_DIR/schemas/lens-30field.json}"
mkdir -p "$INTEL_DIR" "$LOG_DIR" "$LENSES_DIR"

URL=""
TRANSCRIPT=""
LENS=""
BULK_CSV=""
MAX_FRESH=3
MAX_COST=1.00
DRY_RUN=1   # default to dry-run; pass --live to fire LLM
SELFTEST=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --url)        URL="$2"; shift 2 ;;
    --transcript) TRANSCRIPT="$2"; shift 2 ;;
    --lens)       LENS="$2"; shift 2 ;;
    --bulk-csv)   BULK_CSV="$2"; shift 2 ;;
    --max-fresh)  MAX_FRESH="$2"; shift 2 ;;
    --max-cost)   MAX_COST="$2"; shift 2 ;;
    --live)       DRY_RUN=0; shift ;;
    --dry-run)    DRY_RUN=1; shift ;;
    --selftest)   SELFTEST=1; shift ;;
    --help|-h)    sed -n '2,30p' "$0"; exit 0 ;;
    *) echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

log() { echo "[$(date +%H:%M:%S)] lens-decomposer: $*" >&2; }

# ---- Selftest (no LLM, no network) ----
if (( SELFTEST )); then
  echo "[lens-decomposer] selftest: starting (dry-run; no LLM)"
  st_tmp=$(mktemp -d -t lens-decomp-st.XXXXXX)
  export LENSES_DB_PATH="$st_tmp/persona-lens.db"
  export LENSES_DIR="$st_tmp/patterns"
  export LENSES_INTEL_DIR="$st_tmp/intel"
  export LENSES_LOG_DIR="$st_tmp/logs"
  export PERSONA_LENS_SCHEMA_PATH="$st_tmp/schemas/lens-30field.json"

  bash "$SKILL_DIR/scripts/persona-lens.sh" add hormozi \
    --bucket founders --register direct-blunt \
    --rationale 'one hundred million offers, LTV, skin in the game' --live >/dev/null

  # Stage a fake transcript
  transcript_tmp=$(mktemp -t lens-decomp-tr.XXXXXX)
  echo "First principles thinking. Skin in the game. LTV beats CAC. Print profit." > "$transcript_tmp"

  st_out=$(bash "$SKILL_DIR/scripts/lens-decomposer.sh" --lens hormozi --transcript "$transcript_tmp" --dry-run 2>&1)
  if echo "$st_out" | grep -q "DRY-RUN: would decompose"; then
    rm -f "$transcript_tmp"
    rm -rf "$st_tmp"
    echo "[lens-decomposer] selftest: PASS"
    echo "VERDICT: PASS"
    exit 0
  else
    echo "[lens-decomposer] selftest: FAIL — DRY-RUN line not produced"
    rm -f "$transcript_tmp"
    rm -rf "$st_tmp"
    exit 1
  fi
fi

# ---- Validation ----
if [[ -z "$LENS" && -z "$BULK_CSV" ]]; then
  echo "ERROR: --lens <slug> required (or --bulk-csv path)" >&2
  exit 1
fi

# ---- Schema bootstrap (ship default if not present) ----
if [[ ! -f "$SCHEMA" ]]; then
  mkdir -p "$(dirname "$SCHEMA")"
  cat > "$SCHEMA" << 'EOF_SCHEMA'
{
  "narrative": {
    "arc": "what is the story shape?",
    "opening_move": "how does this speaker open?",
    "framework_used": "named framework or none",
    "anti_pattern": "what they explicitly reject",
    "stakes": "what hangs in the balance",
    "resolution": "where they leave the audience"
  },
  "vocabulary": {
    "register": "casual | direct-blunt | quiet-mystic | founder-confident | …",
    "signature_phrases": ["3-7 phrases this speaker uses repeatedly"],
    "blocked_words": ["words this speaker never uses"],
    "rhetorical_devices": ["repetition | tricolon | …"],
    "vocabulary_density": "dense | spare | technical | poetic",
    "metaphor_source": "domain (sports, war, biology, music, …)"
  },
  "design": {
    "composition_pref": "what visual layouts they favor (if visual)",
    "typography": "type choices (if cited)",
    "restraint": "ornate | balanced | minimal",
    "palette": ["color motifs"],
    "spacing": "tight | loose",
    "iconography": "what shapes/icons recur"
  },
  "meta_text": {
    "framework_used": "named framework",
    "anchor": "one-line first-principle anchor",
    "contrarian_take": "what mainstream they push back on",
    "self_revealing_metaphor": "metaphor they apply to themselves",
    "wisdom_source": "where they say their insights come from",
    "vulnerability_marker": "what they admit struggling with"
  },
  "creative_direction": {
    "first_principles_anchor": "one-line statement of root belief",
    "energy_level": "low-still | calm-resolute | high-intense",
    "humor_register": "none | dry | playful | absurd",
    "audience_address": "first | second | third person",
    "pacing": "slow | medium | rapid",
    "callback_density": "low | medium | high"
  }
}
EOF_SCHEMA
fi

if [[ -n "$LENS" && -z "$URL" && -z "$TRANSCRIPT" ]]; then
  log "no --url or --transcript provided"
  echo "{\"mode\":\"no-input\",\"lens\":\"$LENS\",\"note\":\"Pass --url or --transcript to decompose.\"}"
  exit 0
fi

# ---- Source API key ----
KEY="${PERSONA_LENS_LLM_API_KEY:-${GEMINI_API_KEY:-}}"
if (( DRY_RUN == 0 )) && [[ -z "$KEY" ]]; then
  echo "ERROR: PERSONA_LENS_LLM_API_KEY (or GEMINI_API_KEY) not set" >&2
  exit 2
fi

MODEL="${PERSONA_LENS_LLM_MODEL:-${GEMINI_MODEL:-gemini-2.5-flash}}"

# ---- Fetch transcript ----
fetch_transcript() {
  local src="$1" out_file="$2"
  src="${src/#\~/$HOME}"

  if [[ -f "$src" ]]; then cp "$src" "$out_file"; return 0; fi

  if [[ "$src" == *"youtube.com"* || "$src" == *"youtu.be"* ]]; then
    local tmp_dir; tmp_dir=$(mktemp -d -t lens-decompose-yt.XXXXXX)
    if command -v yt-dlp >/dev/null 2>&1; then
      yt-dlp --skip-download --write-auto-subs --sub-format vtt --sub-langs en --no-warnings \
        -o "$tmp_dir/%(id)s.%(ext)s" "$src" 2>/dev/null || true
      local vtt_file; vtt_file=$(ls "$tmp_dir"/*.en.vtt 2>/dev/null | head -1)
      if [[ -n "$vtt_file" ]]; then
        grep -v -E '^WEBVTT|^[0-9:.]+ -->|^$|^[0-9]+$' "$vtt_file" | tr '\n' ' ' | sed 's/  */ /g' > "$out_file"
        rm -rf "$tmp_dir"
        return 0
      fi
    fi
    rm -rf "$tmp_dir"
    log "no yt-dlp or no VTT — trying youtube-transcript-api"
    python3 - "$src" "$out_file" << 'PYEOF' || return 3
import re, sys
try:
    from youtube_transcript_api import YouTubeTranscriptApi
except ImportError:
    print("ERROR: pip install youtube-transcript-api or yt-dlp", file=sys.stderr)
    sys.exit(3)
url, out = sys.argv[1], sys.argv[2]
m = re.search(r'(?:v=|/shorts/|youtu\.be/)([A-Za-z0-9_-]{11})', url)
vid = m.group(1) if m else None
if not vid:
    sys.exit("no video id")
transcript = YouTubeTranscriptApi().fetch(vid)
with open(out, 'w') as f:
    f.write(' '.join(s.text for s in transcript))
PYEOF
    return 0
  fi

  log "non-YouTube URL — using curl + readability extraction"
  curl -sSL --max-time 30 "$src" 2>/dev/null \
    | python3 -c "
import sys, re, html
t = sys.stdin.read()
t = re.sub(r'<script[^>]*>.*?</script>', '', t, flags=re.S|re.I)
t = re.sub(r'<style[^>]*>.*?</style>', '', t, flags=re.S|re.I)
t = re.sub(r'<[^>]+>', ' ', t)
t = html.unescape(t)
t = re.sub(r'\s+', ' ', t).strip()
print(t)
" > "$out_file" 2>/dev/null
  [[ -s "$out_file" ]] || { echo "ERROR: empty content from $src" >&2; return 4; }
}

# ---- LLM decomposition ----
decompose_via_llm() {
  local transcript_file="$1" lens_slug="$2" out_json="$3"
  local transcript schema prompt payload raw_tmp http_code
  transcript=$(head -c 8000 "$transcript_file")
  schema=$(cat "$SCHEMA")

  prompt=$(python3 - "$schema" "$lens_slug" "$transcript" << 'PYEOF'
import sys, json
schema, lens, transcript = sys.argv[1], sys.argv[2], sys.argv[3]
print(f'''You are a cultural decomposition engine. Decompose the speaker into a JSON object matching this schema:

{schema}

Speaker persona slug: {lens}
Transcript:
"""
{transcript}
"""

Return ONLY a JSON object with the 5 top-level buckets (narrative, vocabulary, design, meta_text, creative_direction). No markdown fence, no commentary, JSON only.''')
PYEOF
)

  payload=$(python3 -c "
import json, sys
print(json.dumps({
  'contents': [{'parts': [{'text': sys.argv[1]}]}],
  'generationConfig': {'response_mime_type': 'application/json', 'temperature': 0.3}
}))
" "$prompt")

  raw_tmp=$(mktemp -t lens-llm.XXXXXX)
  for attempt in 1 2 3; do
    http_code=$(curl -sS -w '%{http_code}' -o "$raw_tmp" -X POST \
      "https://generativelanguage.googleapis.com/v1beta/models/${MODEL}:generateContent?key=${KEY}" \
      -H 'Content-Type: application/json' \
      -d "$payload" 2>&1) || true
    [[ "$http_code" == "200" ]] && break
    [[ "$http_code" =~ ^5 ]] && { log "LLM HTTP $http_code attempt $attempt — backoff"; sleep "$attempt"; } || break
  done

  if [[ "$http_code" != "200" ]]; then
    echo "ERROR: LLM HTTP $http_code" >&2
    head -c 500 "$raw_tmp" >&2; echo >&2
    return 5
  fi

  python3 -c "
import json, sys
d = json.load(open(sys.argv[1]))
txt = d.get('candidates',[{}])[0].get('content',{}).get('parts',[{}])[0].get('text','')
try:
    print(json.dumps(json.loads(txt), indent=2, ensure_ascii=False))
except Exception:
    print(txt)
" "$raw_tmp" > "$out_json"
  rm -f "$raw_tmp"
}

append_to_lens_pattern() {
  local lens_slug="$1" decomp_json="$2" source_id="$3" source_url="$4"
  local lens_md="$LENSES_DIR/${lens_slug}-lens-v1.md"

  if [[ ! -f "$lens_md" ]]; then
    log "WARNING: lens markdown not found: $lens_md — run persona-lens.sh add first"
    return 7
  fi

  cat >> "$lens_md" << EOF

---

## Decomposition: $source_id ($(date +%Y-%m-%d))

**Source.** $source_url
**Decomposed via.** lens-decomposer.sh / $MODEL

\`\`\`json
$(cat "$decomp_json")
\`\`\`

EOF

  log "appended decomposition to $lens_md (+$(wc -c < "$decomp_json") bytes)"

  # Re-UPSERT body to DB
  local body; body=$(cat "$lens_md")
  _sq() { printf "%s" "$1" | sed "s/'/''/g"; }
  local id="${lens_slug}-lens-v1"
  sqlite3 "$DB" "UPDATE patterns SET body='$(_sq "$body")', updated_at=datetime('now') WHERE id='$(_sq "$id")'"
}

cost_log() {
  local lens="$1" url="$2" status="$3"
  echo "$(date +%Y-%m-%dT%H:%M:%S),$lens,$url,$MODEL,$status,0.005" >> "$LOG_DIR/lens-decompose.log"
}

process_one() {
  local url="$1" lens="$2"
  log "process: lens=$lens url=$url"

  local lens_intel="$INTEL_DIR/$lens"
  mkdir -p "$lens_intel"

  local source_id
  source_id=$(echo "$url" | sed 's|.*/||; s|[?&].*||; s|[^A-Za-z0-9_-]|_|g' | head -c 30)
  [[ -z "$source_id" ]] && source_id="src-$(date +%s)"

  local transcript_tmp decomp_out
  transcript_tmp=$(mktemp -t lens-transcript.XXXXXX)
  decomp_out="$lens_intel/${source_id}.json"

  if ! fetch_transcript "$url" "$transcript_tmp"; then
    cost_log "$lens" "$url" "fetch_failed"
    rm -f "$transcript_tmp"
    return 1
  fi

  log "transcript: $(wc -c < "$transcript_tmp") chars"

  if (( DRY_RUN )); then
    log "DRY-RUN: would decompose via $MODEL → $decomp_out (pass --live to fire)"
    head -c 200 "$transcript_tmp" >&2; echo "..." >&2
    rm -f "$transcript_tmp"
    return 0
  fi

  if ! decompose_via_llm "$transcript_tmp" "$lens" "$decomp_out"; then
    cost_log "$lens" "$url" "decompose_failed"
    rm -f "$transcript_tmp"
    return 2
  fi

  cost_log "$lens" "$url" "ok"
  append_to_lens_pattern "$lens" "$decomp_out" "$source_id" "$url"
  rm -f "$transcript_tmp"
  return 0
}

process_bulk() {
  local csv="$1"
  if [[ ! -f "$csv" ]]; then echo "ERROR: bulk CSV not found: $csv" >&2; exit 8; fi

  local total=0 ok=0 fail=0 cost_acc=0
  while IFS=, read -r url lens; do
    [[ "$url" == "url" || -z "$url" ]] && continue
    total=$((total + 1))
    cost_acc=$(python3 -c "print(round($cost_acc + 0.005, 3))")
    if (( $(python3 -c "print(1 if $cost_acc > $MAX_COST else 0)") )); then
      log "BUDGET CAP HIT: \$$cost_acc > \$$MAX_COST — stopping at $total processed"
      break
    fi
    if process_one "$url" "$lens"; then ok=$((ok + 1)); else fail=$((fail + 1)); fi
  done < "$csv"

  log "BULK DONE: $total · $ok ok · $fail failed · \$${cost_acc}"
  echo "{\"total\":$total,\"ok\":$ok,\"fail\":$fail,\"cost\":$cost_acc,\"max_cost\":$MAX_COST}"
}

# ---- Dispatch ----
if [[ -n "$BULK_CSV" ]]; then
  process_bulk "$BULK_CSV"
elif [[ -n "$URL" ]]; then
  process_one "$URL" "$LENS"
elif [[ -n "$TRANSCRIPT" ]]; then
  process_one "$TRANSCRIPT" "$LENS"
fi
