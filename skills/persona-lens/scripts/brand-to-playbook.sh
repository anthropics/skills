#!/usr/bin/env bash
# brand-to-playbook — auto-route a brand to its best-fit DTC-playbook lens
# WITHOUT asking "which playbook?".
#
# Pipeline:
#   1. Detect brand category from BRAND-DNA.md (scan for keywords)
#   2. Query registry for dtc-playbook lenses
#   3. Score each by category-match + body-richness + use_count + vlm_score
#   4. (Optional) auto-apply top match via lens-apply.sh
#   5. (Optional) trial-and-error: apply top-N in parallel
#
# Usage:
#   bash brand-to-playbook.sh --brand <slug>
#   bash brand-to-playbook.sh --brand <slug> --use-case ad-headline --auto-apply
#   bash brand-to-playbook.sh --brand <slug> --top 5
#   bash brand-to-playbook.sh --brand-dna /path/to/BRAND-DNA.md --with-trial
#   bash brand-to-playbook.sh --selftest

set -uo pipefail

SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DB="${LENSES_DB_PATH:-$SKILL_DIR/data/persona-lens.db}"
BRANDS_DIR="${PERSONA_LENS_BRANDS_DIR:-$HOME/.persona-lens/brands}"
APPLY_SH="$SKILL_DIR/scripts/lens-apply.sh"
LOG_DIR="${LENSES_LOG_DIR:-$SKILL_DIR/logs}"
mkdir -p "$LOG_DIR"

BRAND=""
BRAND_DNA_OVERRIDE=""
USE_CASE="ad-headline"
TOP=3
AUTO_APPLY=0
WITH_TRIAL=0
LANGUAGE="en"
SELFTEST=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --brand)       BRAND="$2"; shift 2 ;;
    --brand-dna)   BRAND_DNA_OVERRIDE="$2"; shift 2 ;;
    --use-case)    USE_CASE="$2"; shift 2 ;;
    --top)         TOP="$2"; shift 2 ;;
    --auto-apply)  AUTO_APPLY=1; shift ;;
    --with-trial)  WITH_TRIAL=1; shift ;;
    --language)    LANGUAGE="$2"; shift 2 ;;
    --selftest)    SELFTEST=1; shift ;;
    --help|-h)     sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "Unknown: $1" >&2; exit 1 ;;
  esac
done

log() { echo "[$(date +%H:%M:%S)] brand-to-playbook: $*" >&2; }

# ---- Selftest ----
if (( SELFTEST )); then
  echo "[brand-to-playbook] selftest: starting"
  local_tmp=$(mktemp -d -t b2p-st.XXXXXX)
  export LENSES_DB_PATH="$local_tmp/persona-lens.db"
  export LENSES_DIR="$local_tmp/patterns"
  export LENSES_LOG_DIR="$local_tmp/logs"
  export PERSONA_LENS_BRANDS_DIR="$local_tmp/brands"

  # Seed a dtc-playbook lens
  bash "$SKILL_DIR/scripts/persona-lens.sh" add huel-funnel \
    --bucket dtc-playbook --register direct-response \
    --rationale "category: food. Science-authority + subscribe-and-save." \
    --live >/dev/null

  bash "$SKILL_DIR/scripts/persona-lens.sh" add ag1-funnel \
    --bucket dtc-playbook --register direct-response \
    --rationale "category: wellness. Forbes badges + risk-free trial." \
    --live >/dev/null

  # Seed brand
  mkdir -p "$PERSONA_LENS_BRANDS_DIR/example-food-brand"
  cat > "$PERSONA_LENS_BRANDS_DIR/example-food-brand/BRAND-DNA.md" << 'EOF'
# Example Food Brand
Category: food (plant-based)
Voice: warm, transparent.
EOF

  out=$(bash "$SKILL_DIR/scripts/brand-to-playbook.sh" --brand example-food-brand --use-case ad-headline 2>/dev/null)
  if echo "$out" | python3 -c "import json,sys; d=json.load(sys.stdin); assert d['detected_category']=='food'; assert d['total_candidates']>=1; print('   detected category:', d['detected_category']); print('   candidates:', d['total_candidates'])"; then
    echo "[brand-to-playbook] selftest: PASS"
    echo "VERDICT: PASS"
    rm -rf "$local_tmp"
    exit 0
  else
    echo "[brand-to-playbook] selftest: FAIL"
    rm -rf "$local_tmp"
    exit 1
  fi
fi

# ---- Resolve brand DNA path ----
BRAND_DNA_PATH=""
if [[ -n "$BRAND_DNA_OVERRIDE" && -f "$BRAND_DNA_OVERRIDE" ]]; then
  BRAND_DNA_PATH="$BRAND_DNA_OVERRIDE"
elif [[ -n "$BRAND" ]]; then
  for candidate in "$BRANDS_DIR/$BRAND/BRAND-DNA.md" "$BRANDS_DIR/$BRAND/DNA.json" "$BRANDS_DIR/$BRAND/core.md"; do
    if [[ -f "$candidate" ]]; then BRAND_DNA_PATH="$candidate"; break; fi
  done
fi

if [[ -z "$BRAND_DNA_PATH" && -z "$BRAND" ]]; then
  echo "ERROR: --brand <slug> or --brand-dna PATH required" >&2
  echo "usage: $0 --brand <slug> [--use-case X] [--top N] [--auto-apply] [--with-trial]" >&2
  [[ -d "$BRANDS_DIR" ]] && echo "  available brands: $(ls "$BRANDS_DIR" 2>/dev/null | tr '\n' ' ')" >&2
  exit 1
fi

# ---- 1. Detect brand category ----
detect_category() {
  local dna_path="$1" slug="$2"
  if [[ -f "$dna_path" ]]; then
    local content
    content=$(cat "$dna_path" | head -200 | tr '[:upper:]' '[:lower:]')
    for cat in food beverage wellness apparel beauty cookware home tech health; do
      if echo "$content" | grep -q -E "\\b${cat}\\b"; then
        echo "$cat"; return 0
      fi
    done
  fi
  # Slug-based heuristic fallback
  case "$slug" in
    *food*|*recipe*|*kitchen*)   echo "food"; return 0 ;;
    *wellness*|*spirit*|*spa*)   echo "wellness"; return 0 ;;
    *supplement*|*vitamin*)      echo "wellness"; return 0 ;;
    *bev*|*juice*|*tea*|*coffee*) echo "beverage"; return 0 ;;
    *) echo "other"; return 0 ;;
  esac
}

CATEGORY=$(detect_category "$BRAND_DNA_PATH" "${BRAND:-(none)}")
log "brand=${BRAND:-(none)} dna=${BRAND_DNA_PATH:-(none)} category=$CATEGORY use_case=$USE_CASE top=$TOP"

# ---- 2-3. Rank dtc-playbook lenses ----
RANKED_TMP=$(mktemp -t b2p-ranked.XXXXXX)
DB="$DB" CATEGORY="$CATEGORY" BRAND="${BRAND:-}" USE_CASE="$USE_CASE" TOP="$TOP" python3 << 'PYEOF' > "$RANKED_TMP"
import json, os, re, sqlite3

db = os.environ["DB"]
target_cat = os.environ.get("CATEGORY","other")
brand = os.environ.get("BRAND","")
use_case = os.environ.get("USE_CASE","")
top = int(os.environ.get("TOP","3"))

con = sqlite3.connect(db)
cur = con.cursor()
cur.execute("""
    SELECT persona_lens, length(body) AS body_len, vlm_score_avg, use_count, body, notes
    FROM patterns
    WHERE bucket='dtc-playbook' AND promotion_status='active'
""")
lenses = []
for lens, body_len, vlm, uses, body, notes in cur.fetchall():
    cat = None
    if body and '"category":' in body:
        m = re.search(r'\{[^{}]*"category"\s*:\s*"([^"]+)"', body)
        if m: cat = m.group(1).lower()
    if not cat and notes and "category:" in notes.lower():
        m = re.search(r'category:\s*([a-z\-]+)', notes.lower())
        if m: cat = m.group(1)
    score = 0
    if cat and target_cat in cat: score += 50
    if cat and cat == target_cat: score += 30
    score += min((body_len or 0) / 100, 30)
    score += (vlm or 0) * 2
    score += min(uses or 0, 10)
    lenses.append({
        "lens": lens,
        "category": cat or "?",
        "score": round(score, 1),
        "body_len": body_len or 0,
        "vlm": vlm or 0,
        "uses": uses or 0,
        "takeaway": (notes or "")[:150],
    })

lenses.sort(key=lambda x: x["score"], reverse=True)
print(json.dumps({
    "brand": brand,
    "detected_category": target_cat,
    "use_case": use_case,
    "total_candidates": len(lenses),
    "top": lenses[:top],
}, indent=2))
PYEOF

cat "$RANKED_TMP"

# ---- 4. Auto-apply top match ----
if (( AUTO_APPLY )); then
  TOP_LENS=$(python3 -c "import json; d=json.load(open('$RANKED_TMP')); print(d['top'][0]['lens'] if d['top'] else '')" 2>/dev/null)
  if [[ -n "$TOP_LENS" ]]; then
    log "auto-applying top match: $TOP_LENS"
    apply_args=(--lens "$TOP_LENS" --use-case "$USE_CASE" --language "$LANGUAGE")
    [[ -n "$BRAND" ]] && apply_args+=(--brand "$BRAND")
    [[ -n "$BRAND_DNA_OVERRIDE" ]] && apply_args+=(--brand-dna "$BRAND_DNA_OVERRIDE")
    bash "$APPLY_SH" "${apply_args[@]}"
  else
    log "WARN: no candidates to auto-apply"
  fi
fi

# ---- 5. Trial mode (apply top N) ----
if (( WITH_TRIAL )); then
  log "trial mode: applying top $TOP lenses"
  TRIALS_DIR=$(mktemp -d -t b2p-trials.XXXXXX)
  python3 -c "
import json
d = json.load(open('$RANKED_TMP'))
for x in d['top']: print(x['lens'])
" > "$TRIALS_DIR/lenses.txt"
  while read -r lens; do
    [[ -z "$lens" ]] && continue
    out="$TRIALS_DIR/${lens}.json"
    log "  trial: $lens"
    apply_args=(--lens "$lens" --use-case "$USE_CASE" --language "$LANGUAGE")
    [[ -n "$BRAND" ]] && apply_args+=(--brand "$BRAND")
    [[ -n "$BRAND_DNA_OVERRIDE" ]] && apply_args+=(--brand-dna "$BRAND_DNA_OVERRIDE")
    bash "$APPLY_SH" "${apply_args[@]}" > "$out" 2>/dev/null || true
  done < "$TRIALS_DIR/lenses.txt"
  log "trials saved: $TRIALS_DIR"
  echo "{\"trials_dir\":\"$TRIALS_DIR\",\"trial_count\":$(ls "$TRIALS_DIR"/*.json 2>/dev/null | wc -l | tr -d ' ')}"
fi

rm -f "$RANKED_TMP"
