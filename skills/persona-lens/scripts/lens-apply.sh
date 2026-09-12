#!/usr/bin/env bash
# lens-apply — compose [lens × brand-DNA × use-case × user-input] → ready prompt
#
# Pipeline:
#   1. Load lens body from registry (persona_lens=<slug>)
#   2. (Optional) policy gate via $MEMPALACE_POLICY_SH if set + executable
#   3. Load brand DNA from --brand-dna PATH (preferred) OR
#      $PERSONA_LENS_BRANDS_DIR/<brand>/BRAND-DNA.md (fallback)
#   4. Load use-case template if a pattern with use_case=<X> exists
#   5. Compose: [lens system] + [brand DNA] + [use-case] + [user input]
#   6. Emit JSON: composed_prompt + metadata
#
# Usage:
#   bash lens-apply.sh --lens steve-jobs --brand-dna /path/to/BRAND-DNA.md --use-case manifesto
#   bash lens-apply.sh --lens hormozi --brand my-brand --use-case ad-headline --user-input "..."
#   bash lens-apply.sh --selftest

set -uo pipefail

SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DB="${LENSES_DB_PATH:-$SKILL_DIR/data/persona-lens.db}"
BRANDS_DIR="${PERSONA_LENS_BRANDS_DIR:-$HOME/.persona-lens/brands}"
LOG_DIR="${LENSES_LOG_DIR:-$SKILL_DIR/logs}"
MEMPALACE_POLICY="${MEMPALACE_POLICY_SH:-}"
mkdir -p "$LOG_DIR"

LENS=""
BRAND=""
BRAND_DNA_OVERRIDE=""
USE_CASE=""
LANGUAGE="en"
USER_INPUT=""
SKIP_POLICY=0
SELFTEST=0

_sq() { printf "%s" "$1" | sed "s/'/''/g"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    --lens)        LENS="$2"; shift 2 ;;
    --brand)       BRAND="$2"; shift 2 ;;
    --brand-dna)   BRAND_DNA_OVERRIDE="$2"; shift 2 ;;
    --use-case)    USE_CASE="$2"; shift 2 ;;
    --language)    LANGUAGE="$2"; shift 2 ;;
    --user-input)  USER_INPUT="$2"; shift 2 ;;
    --skip-policy) SKIP_POLICY=1; shift ;;
    --selftest)    SELFTEST=1; shift ;;
    --help|-h)     sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

log() { echo "[$(date +%H:%M:%S)] lens-apply: $*" >&2; }

# ---- Selftest ----
if (( SELFTEST )); then
  echo "[lens-apply] selftest: starting"
  local_tmp=$(mktemp -d -t lens-apply-st.XXXXXX)
  export LENSES_DB_PATH="$local_tmp/persona-lens.db"
  export LENSES_DIR="$local_tmp/patterns"
  export LENSES_LOG_DIR="$local_tmp/logs"
  export PERSONA_LENS_BRANDS_DIR="$local_tmp/brands"

  # Seed a sample lens
  bash "$SKILL_DIR/scripts/persona-lens.sh" add steve-jobs \
    --bucket founders --register founder-confident \
    --rationale "first principles · less but better · demos > slides" --live >/dev/null

  # Seed a sample brand DNA
  mkdir -p "$PERSONA_LENS_BRANDS_DIR/example-brand"
  cat > "$PERSONA_LENS_BRANDS_DIR/example-brand/BRAND-DNA.md" << 'EOF'
# Example Brand DNA
Voice: warm, conversational, slightly playful.
Values: craft, transparency, community.
Audience: design-leaning prosumers.
Blocked: hype words, exclamation points.
EOF

  out=$(bash "$SKILL_DIR/scripts/lens-apply.sh" \
    --lens steve-jobs \
    --brand example-brand \
    --use-case manifesto \
    --user-input "Announcing the v2 launch." 2>/dev/null)

  if echo "$out" | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['lens_id']=='steve-jobs-lens-v1'; assert d['composition_token_count']>0; print('   tokens:', d['composition_token_count']); print('   brand_dna:', d['brand_dna_path'])"; then
    echo "[lens-apply] selftest: PASS"
    echo "VERDICT: PASS"
    rm -rf "$local_tmp"
    exit 0
  else
    echo "[lens-apply] selftest: FAIL"
    rm -rf "$local_tmp"
    exit 1
  fi
fi

if [[ -z "$LENS" || -z "$USE_CASE" ]]; then
  echo "ERROR: --lens and --use-case required" >&2
  echo "usage: $0 --lens <slug> --use-case <slug> [--brand <slug> | --brand-dna PATH] [--language en|ms|zh] [--user-input <text>]" >&2
  exit 1
fi

if [[ -z "$BRAND" && -z "$BRAND_DNA_OVERRIDE" ]]; then
  log "WARN: no --brand or --brand-dna supplied — composing lens + use-case only"
fi

# ---- 1. Load lens body ----
LENS_ID="${LENS}-lens-v1"
LENS_BODY=$(sqlite3 "$DB" "SELECT body FROM patterns WHERE id='$(_sq "$LENS_ID")' LIMIT 1" 2>/dev/null)
if [[ -z "$LENS_BODY" ]]; then
  echo "ERROR: lens not found: $LENS_ID" >&2
  echo "Available: $(sqlite3 "$DB" "SELECT persona_lens FROM patterns WHERE persona_lens != ''" 2>/dev/null | tr '\n' ' ')" >&2
  exit 3
fi
LENS_REGISTER=$(sqlite3 "$DB" "SELECT register FROM patterns WHERE id='$(_sq "$LENS_ID")'" 2>/dev/null)

# ---- 2. Optional policy gate ----
GATE_WARNINGS_JSON="[]"
if [[ "$SKIP_POLICY" -eq 0 && -n "$MEMPALACE_POLICY" && -x "$MEMPALACE_POLICY" ]]; then
  policy_ctx=$(python3 -c "import json; print(json.dumps({'brand':'${BRAND:-}','intent':'persona-lens-apply','urgency':'normal'}))")
  policy_out=$(bash "$MEMPALACE_POLICY" decide --task-type read --context "$policy_ctx" 2>&1) || true
  policy_action=$(echo "$policy_out" | python3 -c "import json,sys; d=json.loads(sys.stdin.read()); print(d.get('action','unknown'))" 2>/dev/null) || policy_action="parse_error"
  case "$policy_action" in
    hard_reject|reject)
      echo "ERROR: policy HARD-REJECT — $policy_out" >&2
      exit 2 ;;
    *) log "policy: action=$policy_action" ;;
  esac
elif [[ "$SKIP_POLICY" -eq 0 && -n "$MEMPALACE_POLICY" ]]; then
  log "[lens-apply] WARNING: MEMPALACE_POLICY_SH set but not executable — skipping policy gate"
fi

# ---- 3. Load brand DNA ----
BRAND_DNA_PATH=""
BRAND_DNA=""
if [[ -n "$BRAND_DNA_OVERRIDE" && -f "$BRAND_DNA_OVERRIDE" ]]; then
  BRAND_DNA_PATH="$BRAND_DNA_OVERRIDE"
  BRAND_DNA=$(cat "$BRAND_DNA_OVERRIDE")
elif [[ -n "$BRAND" ]]; then
  for candidate in "$BRANDS_DIR/$BRAND/BRAND-DNA.md" "$BRANDS_DIR/$BRAND/DNA.json" "$BRANDS_DIR/$BRAND/core.md"; do
    if [[ -f "$candidate" ]]; then
      BRAND_DNA_PATH="$candidate"
      BRAND_DNA=$(cat "$candidate")
      break
    fi
  done
fi
if [[ -z "$BRAND_DNA" ]]; then
  log "no brand DNA found — composing with lens + use-case only"
  BRAND_DNA="(no brand DNA supplied. Use --brand <slug> with file at \$PERSONA_LENS_BRANDS_DIR/<slug>/BRAND-DNA.md, or --brand-dna PATH.)"
  GATE_WARNINGS_JSON='["brand_dna_missing"]'
fi

# ---- 4. Load use-case template (optional) ----
USE_CASE_PATTERN_ID=""
USE_CASE_TEMPLATE=""
USE_CASE_ROW=$(sqlite3 "$DB" "SELECT id, body FROM patterns WHERE use_case='$(_sq "$USE_CASE")' AND pattern_type IN ('template','framework','block') ORDER BY vlm_score_avg DESC, use_count DESC LIMIT 1" -separator '|||' 2>/dev/null)
if [[ -n "$USE_CASE_ROW" ]]; then
  USE_CASE_PATTERN_ID=$(echo "$USE_CASE_ROW" | head -1 | awk -F'\\|\\|\\|' '{print $1}')
  USE_CASE_TEMPLATE=$(echo "$USE_CASE_ROW" | awk -F'\\|\\|\\|' 'NR==1 {for(i=2;i<=NF;i++) printf "%s", $i; print ""}')
  log "use-case template found: $USE_CASE_PATTERN_ID"
else
  USE_CASE_TEMPLATE="(no specific template for use_case=$USE_CASE — use lens + brand DNA to inform output.)"
fi

# ---- 5. Compose ----
COMPOSED=$(cat << EOF
# SYSTEM PROMPT — composed by persona-lens / lens-apply

You are writing in the voice of the **${LENS}** thought-leader lens for the **${BRAND:-(unbranded)}** brand. Use-case: **${USE_CASE}**. Output language: **${LANGUAGE}**.

## LENS — ${LENS} (register: ${LENS_REGISTER})

The following decomposition was extracted from primary sources (talks, essays, podcasts) and tagged into a structured schema:

\`\`\`
${LENS_BODY}
\`\`\`

## BRAND DNA — ${BRAND:-(unbranded)}

The lens supplies HOW to talk; the brand supplies WHAT can be said. Brand DNA always wins on values + facts:

\`\`\`
${BRAND_DNA}
\`\`\`

## USE-CASE — ${USE_CASE}

Apply the lens within these scaffolding constraints:

\`\`\`
${USE_CASE_TEMPLATE}
\`\`\`

## INSTRUCTIONS

1. Adopt the lens narrative arc, vocabulary register, and signature phrases — but stay within brand DNA constraints
2. Use brand-specific facts, products, audience details when supplied
3. Output in language: ${LANGUAGE}
4. Avoid blocked words from the lens vocabulary section
5. Match the lens energy_level and humor_register
6. If brand DNA contradicts the lens (e.g. lens says "high-intensity" but brand DNA says "calm-luxury"), brand DNA wins on tone — but use the lens STRUCTURAL patterns (arc, opening move, framework)

## USER INPUT (what to generate)

${USER_INPUT:-<the user request goes here — describe the specific piece of content to generate>}
EOF
)

# ---- 6. Token estimate + emit JSON ----
TOKEN_EST=$(python3 -c "
import sys
text = sys.stdin.read()
print(len(text) // 4)
" <<< "$COMPOSED")

echo "$(date +%Y-%m-%dT%H:%M:%S),$LENS,${BRAND:-},$USE_CASE,$TOKEN_EST" >> "$LOG_DIR/lens-apply.log"

META_TMP=$(mktemp -t lens-apply-meta.XXXXXX)
COMPOSED_TMP=$(mktemp -t lens-apply-composed.XXXXXX)
printf '%s' "$COMPOSED" > "$COMPOSED_TMP"
cat > "$META_TMP" << EOF_META
{
  "lens_id": "$LENS_ID",
  "lens_register": "$LENS_REGISTER",
  "brand": "${BRAND:-}",
  "brand_dna_path": "${BRAND_DNA_PATH:-(missing)}",
  "use_case": "$USE_CASE",
  "use_case_pattern_id": "${USE_CASE_PATTERN_ID:-(none)}",
  "language": "$LANGUAGE",
  "composition_token_count": $TOKEN_EST,
  "gate_warnings": $GATE_WARNINGS_JSON
}
EOF_META

python3 - "$COMPOSED_TMP" "$META_TMP" << 'PYEOF'
import json, sys
composed = open(sys.argv[1]).read()
meta = json.load(open(sys.argv[2]))
meta['composed_prompt'] = composed
print(json.dumps(meta, indent=2, ensure_ascii=False))
PYEOF
rm -f "$COMPOSED_TMP" "$META_TMP"
