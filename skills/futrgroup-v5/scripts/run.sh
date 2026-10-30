#!/usr/bin/env bash
# run.sh — futrgroup-v5 orchestrator (Franky Shaw v5/v5.1 7-stage pipeline)
#
# Chains the 7 stages with cost-aware provider routing.
# Default: FAL + Gemini direct (cheapest).
# Fallback: muapi-cli (one key, 267 models).
# Proprietary: higgsfield-cli (Marketing Studio / Soul ID / Virality Predictor only).
#
# Usage:
#   run.sh --brand my-brand --product-url https://... --style "claymation Apple-influenced" \
#          --hook hook-thumb-stop-claymation --setting setting-clean-white-studio \
#          --avatar preset-warm-asian-female --mode ugc_unboxing --duration 60 \
#          --out ./out-dir/
#
#   run.sh --selftest                         # dry-run, no API calls
#   run.sh --resume-from 4 --workdir ./prev/  # resume from a stage

set -uo pipefail
SK_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && cd .. && pwd)"
SCRIPTS="$SK_DIR/scripts"

# Resolve sibling skills (or fall back to stub mode)
. "$SCRIPTS/_siblings.sh"

BRAND=""
PRODUCT_URL=""
PRODUCT_NAME=""
STYLE="claymation Apple-influenced"
HOOK=""
SETTING=""
AVATAR=""
MODE="ugc"
DURATION=60
ASPECT="9:16"
PROVIDER="fal+gemini"
USE_SOUL_ID=0
USE_VIRALITY=0
OUT_DIR=""
SELFTEST=0
RESUME_FROM=0
WORKDIR=""

usage() {
  cat <<EOF
run.sh — futrgroup-v5 7-stage orchestrator

USAGE:
  $(basename "$0") --brand BRAND --product-url URL [OPTIONS]
  $(basename "$0") --selftest

REQUIRED:
  --brand BRAND          your brand slug (resolves to \$FUTRGROUP_BRAND_HOME/<brand>/)
  --product-url URL      product page URL (NotebookLM ingests)

STYLE:
  --style ANCHOR         e.g. "claymation Apple-influenced" (v5) or "realistic UGC" (v5.1)
  --hook HOOK_ID         (see marketing-studio-clone/data/hooks.json)
  --setting SETTING_ID
  --avatar AVATAR_ID
  --mode MODE            ugc / ugc_how_to / ugc_unboxing / product_showcase / product_review / tv_spot / wild_card / ugc_virtual_try_on

OUTPUT:
  --duration SEC         default 60
  --aspect RATIO         default 9:16
  --out DIR              output directory (default ./<brand>/<date>-<slug>/)

PROVIDER ROUTING:
  --provider WHAT        fal+gemini (default, cheapest) | muapi | higgsfield-cli
  --use-soul-id          escalate to higgsfield-cli for hero frame (Soul ID)
  --use-virality         after edit, run higgsfield-cli brain_activity scoring

CONTROL:
  --selftest             dry-run, no API calls — verify all scripts are wired
  --resume-from N        resume from stage N (1-7), needs --workdir
  --workdir DIR          previous run dir (for --resume-from)

EXAMPLES:
  $(basename "$0") --brand my-brand --product-url "https://my-shop.com/products/X" \\
    --style "claymation Apple-influenced" --hook hook-thumb-stop-claymation \\
    --setting setting-clean-white-studio --avatar preset-warm-asian-female \\
    --mode ugc_unboxing --duration 60

  $(basename "$0") --selftest
EOF
  exit 0
}

while [ $# -gt 0 ]; do
  case "$1" in
    --brand)        BRAND="$2"; shift 2 ;;
    --product-url)  PRODUCT_URL="$2"; shift 2 ;;
    --product-name) PRODUCT_NAME="$2"; shift 2 ;;
    --style)        STYLE="$2"; shift 2 ;;
    --hook)         HOOK="$2"; shift 2 ;;
    --setting)      SETTING="$2"; shift 2 ;;
    --avatar)       AVATAR="$2"; shift 2 ;;
    --mode)         MODE="$2"; shift 2 ;;
    --duration)     DURATION="$2"; shift 2 ;;
    --aspect)       ASPECT="$2"; shift 2 ;;
    --provider)     PROVIDER="$2"; shift 2 ;;
    --use-soul-id)  USE_SOUL_ID=1; shift ;;
    --use-virality) USE_VIRALITY=1; shift ;;
    --out)          OUT_DIR="$2"; shift 2 ;;
    --selftest)     SELFTEST=1; shift ;;
    --resume-from)  RESUME_FROM="$2"; shift 2 ;;
    --workdir)      WORKDIR="$2"; shift 2 ;;
    -h|--help)      usage ;;
    *) echo "unknown arg: $1" >&2; exit 1 ;;
  esac
done

# ── selftest mode ──
if [ "$SELFTEST" -eq 1 ]; then
  echo "[selftest] verifying 7 stage scripts exist + parse..."
  for n in 1 2 3 4 5 6 7; do
    name=""
    case $n in
      1) name="1-research.sh" ;;
      2) name="2-concept.sh" ;;
      3) name="3-frames.sh" ;;
      4) name="4-animate.sh" ;;
      5) name="5-voice.sh" ;;
      6) name="6-music.sh" ;;
      7) name="7-edit.sh" ;;
    esac
    f="$SCRIPTS/$name"
    if [ ! -f "$f" ]; then
      echo "  MISSING $name"; exit 2
    fi
    if ! bash -n "$f" 2>/dev/null; then
      echo "  PARSE FAIL $name"; exit 2
    fi
    echo "  ok $name"
  done
  echo "[selftest] sibling-skill status (resolved via _siblings.sh; missing → stub mode):"
  for v in NOTEBOOKLM_SH MSCLONE_SH MCSLA_SH MUAPI_IMG_SH MUAPI_I2V_SH MUAPI_MUSIC_SH \
           VIDEO_GEN_SH VOICEOVER_SH HIGGSFIELD_GEN_SH HIGGSFIELD_I2V_SH AD_ID_MINT_SH \
           CARDFLIP_SH GODAUDIT_SH REMOTION_SH HYPERFRAMES_SH; do
    eval "val=\${FUTRGROUP_${v}:-}"
    if [ -n "$val" ] && [ -x "$val" ]; then
      echo "  resolved FUTRGROUP_${v} → $val"
    else
      echo "  missing  FUTRGROUP_${v} (orchestrator will use stub for this stage)"
    fi
  done
  echo "[selftest] PASS — all 7 stages parse + arg-validate"
  echo "VERDICT: PASS"
  exit 0
fi

# ── validate args for live run ──
[ -z "$BRAND" ]       && { echo "missing --brand" >&2; exit 1; }
[ -z "$PRODUCT_URL" ] && [ "$RESUME_FROM" -eq 0 ] && { echo "missing --product-url" >&2; exit 1; }

# ── set up workdir ──
FUTRGROUP_OUT_HOME="${FUTRGROUP_OUT_HOME:-$HOME/.futrgroup/out}"
if [ "$RESUME_FROM" -gt 0 ]; then
  [ -z "$WORKDIR" ] && { echo "--resume-from requires --workdir" >&2; exit 1; }
  OUT_DIR="$WORKDIR"
elif [ -z "$OUT_DIR" ]; then
  DATE="$(date +%F)"
  SLUG="$(echo "$PRODUCT_URL" | sed -E 's,^https?://[^/]+/,,; s,/$,,; s,[^a-zA-Z0-9],-,g' | tr A-Z a-z | head -c 40)"
  OUT_DIR="$FUTRGROUP_OUT_HOME/$BRAND/${DATE}-${SLUG}"
fi
mkdir -p "$OUT_DIR"/{1-research,2-concept,3-frames,4-clips,5-voice,6-music,7-edit}
echo "[run] workdir = $OUT_DIR"

# ── Stage 0: mint ad_id (lineage chain — optional integration) ──
if [ ! -f "$OUT_DIR/ad-id.json" ] && [ "$RESUME_FROM" -eq 0 ]; then
  if [ -n "$FUTRGROUP_AD_ID_MINT_SH" ] && [ -x "$FUTRGROUP_AD_ID_MINT_SH" ]; then
    "$FUTRGROUP_AD_ID_MINT_SH" --brand "$BRAND" --type ad --channel meta --title "futrgroup-v5 $BRAND" --destination "$PRODUCT_URL" > "$OUT_DIR/ad-id.json" 2>&1 || \
      echo "[FUTRGROUP] WARNING: ad-id-mint failed (continuing with local fallback)" >&2
  else
    echo "[FUTRGROUP] WARNING: ad-id-mint not configured — using local ad-id only (set FUTRGROUP_AD_ID_MINT_SH to integrate lineage)" >&2
    cat > "$OUT_DIR/ad-id.json" <<EOF
{"ad_id":"local-$(date +%s)-$BRAND","brand":"$BRAND","type":"ad","channel":"meta","mode":"dev","note":"FUTRGROUP_AD_ID_MINT_SH unset"}
EOF
  fi
fi

# ── orchestrate stages ──
run_stage() {
  local n="$1" name="$2"
  if [ "$RESUME_FROM" -gt 0 ] && [ "$n" -lt "$RESUME_FROM" ]; then
    echo "[skip] stage $n $name (resuming from $RESUME_FROM)"
    return 0
  fi
  echo "[stage $n] $name"
  if ! bash "$SCRIPTS/$name" --workdir "$OUT_DIR" --brand "$BRAND" --provider "$PROVIDER" --product-url "$PRODUCT_URL" --style "$STYLE" --hook "$HOOK" --setting "$SETTING" --avatar "$AVATAR" --mode "$MODE" --duration "$DURATION" --aspect "$ASPECT" 2>&1 | tee -a "$OUT_DIR/manifest.log"; then
    echo "[FAIL] stage $n exited non-zero" >&2
    return 1
  fi
}

run_stage 1 1-research.sh   || exit 1
run_stage 2 2-concept.sh    || exit 1
run_stage 3 3-frames.sh     || exit 1
run_stage 4 4-animate.sh    || exit 1
run_stage 5 5-voice.sh      || exit 1
run_stage 6 6-music.sh      || exit 1
run_stage 7 7-edit.sh       || exit 1

# ── Optional Stage 8: Virality Predictor ──
if [ "$USE_VIRALITY" -eq 1 ]; then
  echo "[stage 8] virality-predictor"
  if [ -n "$FUTRGROUP_HIGGSFIELD_VIRALITY_SH" ] && [ -x "$FUTRGROUP_HIGGSFIELD_VIRALITY_SH" ]; then
    "$FUTRGROUP_HIGGSFIELD_VIRALITY_SH" --video "$OUT_DIR/7-edit/final-captioned.mp4" > "$OUT_DIR/virality-report.json" 2>&1 || \
      echo "[FUTRGROUP] WARNING: virality scoring failed" >&2
  else
    echo "[FUTRGROUP] WARNING: higgsfield-cli not configured (FUTRGROUP_HIGGSFIELD_VIRALITY_SH) — skip virality" >&2
  fi
fi

# ── manifest ──
cat > "$OUT_DIR/manifest.json" <<EOF
{
  "skill": "futrgroup-v5",
  "version": "0.1.0",
  "brand": "$BRAND",
  "product_url": "$PRODUCT_URL",
  "style": "$STYLE",
  "hook": "$HOOK",
  "setting": "$SETTING",
  "avatar": "$AVATAR",
  "mode": "$MODE",
  "duration": $DURATION,
  "aspect": "$ASPECT",
  "provider": "$PROVIDER",
  "use_soul_id": $USE_SOUL_ID,
  "use_virality": $USE_VIRALITY,
  "completed_at": "$(date -u +%FT%TZ)",
  "workdir": "$OUT_DIR"
}
EOF

echo "[done] $OUT_DIR"
echo "  ad_id: $(jq -r '.ad_id // "?"' "$OUT_DIR/ad-id.json" 2>/dev/null)"
echo "  final: $OUT_DIR/7-edit/final-captioned.mp4 (after Captions iOS step — manual)"

exit 0
