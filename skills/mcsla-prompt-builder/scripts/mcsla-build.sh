#!/usr/bin/env bash
# mcsla-build.sh — Compose MCSLA-structured video prompts that work on raw FAL/muapi/higgsfield models.
#
# MCSLA = Model · Camera · Subject · Look · Action
# Source: OSideMedia/higgsfield-ai-prompt-skill@3.7.0 vocab (cloned 2026-05-09)
#
# Usage:
#   mcsla-build.sh --model kling-3.0 --camera "Robo Arm" --subject "matte black mug" \
#                  --look "cinematic, warm neutrals, soft natural light" \
#                  --action "hot coffee pours, steam rises in macro close-up"
#
#   mcsla-build.sh --validate "your prompt text..."
#   mcsla-build.sh --list cameras|shot-sizes|micro-expressions|color-grades|film-stocks|lighting|styles
#   mcsla-build.sh --selftest
#
# Output:
#   stdout = composed prompt (≤200 words, named-tokens-only, Subject→Action→Camera→Style order)
#   exit 0 = ok · 1 = arg/validate fail · 2 = data missing
#
# Integrates with: prompt-bank (--register-pattern), higgsfield-preset-lib (--apply-preset)

set -uo pipefail

SK_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && cd .. && pwd)"
DATA_DIR="$SK_DIR/data"

# ---- args ----
MODEL=""
CAMERA=""
CAMERA_DETAIL=""
SHOT_SIZE=""
SUBJECT=""
SUBJECT_DETAIL=""
MICRO_EXPR=""
LOOK=""
COLOR_GRADE=""
FILM_STOCK=""
LIGHTING=""
STYLE=""
ACTION=""
ASPECT="9:16"
DURATION=""
FORMAT="text"
LIST_KIND=""
VALIDATE_TEXT=""
SELFTEST=0
REGISTER_PATTERN=0
APPLY_PRESET=""

: "${SETTING:=}"
# UGC mode (Sean Claude's Character→Product→Setting→Lighting→Camera→Tone order)
UGC_MODE=0
CHARACTER=""      # face, outfit, energy, expression
PRODUCT=""        # format, color, position
TONE="raw, unfiltered, authentic, never staged, iPhone selfie feel"

usage() {
  cat <<EOF
mcsla-build.sh — MCSLA prompt composer

USAGE:
  $(basename "$0") [SLOT FLAGS] [META FLAGS]
  $(basename "$0") --validate "prompt text"
  $(basename "$0") --list KIND
  $(basename "$0") --selftest

SLOTS (M/C/S/L/A):
  --model NAME            kling-3.0 / seedance-2.0 / veo-3.1 / wan-2.7 / nano-banana / ...
  --camera NAME           Robo Arm / Bullet Time / Snorricam / FPV Drone / Dolly In / ...
  --camera-detail TEXT    free-form trailing detail ("arcing slowly from base to lid")
  --shot-size ABBR        ELS|EWS|WS|MLS|MWS|MS|MCU|CU|ECU|Insert|OTS|POV|2S
  --subject TEXT          what's in frame
  --subject-detail TEXT   body language + props
  --micro-expression NAME Quiet Devastation / Cold Calculation / Simmering Rage / ...
  --look TEXT             complete look line OR use sub-flags
  --color-grade MOOD      Blockbuster / Cyberpunk / Romance / Noir / ...
  --film-stock NAME       Kodak Portra 400 / Fuji Velvia / Ilford HP5 / ...
  --lighting NAME         Golden hour / Volumetric / Rembrandt / Chiaroscuro / ...
  --style NAME            Cinematic / VHS / Super 8MM / Anamorphic / Abstract
  --action TEXT           what happens in the shot

META:
  --aspect RATIO          9:16 (default) / 16:9 / 1:1 / 4:5
  --duration SEC          4 / 5 / 8 (Kling/Seedance) — clip length
  --format text|json      output format (default text)
  --register-pattern      after compose, register into prompt-bank bucket=mcsla
  --apply-preset NAME     pull style+motion strings from higgsfield-preset-lib catalog and merge

UTIL:
  --validate TEXT         lint an existing prompt (≤200 words, no negatives, named tokens)
  --list KIND             KIND ∈ cameras|shot-sizes|micro-expressions|color-grades|film-stocks|lighting|styles
  --selftest              run 3 known-good builds + assert outputs valid

EXAMPLES:
  $(basename "$0") --model kling-3.0 --camera "Robo Arm" --camera-detail "arcing from base to lid" \\
                   --subject "matte black travel mug" --subject-detail "minimal, no branding" \\
                   --look "cinematic commercial, warm neutrals, soft diffused natural light" \\
                   --action "hot coffee pours, steam rises in macro close-up" \\
                   --aspect 9:16 --duration 5

  $(basename "$0") --list cameras
  $(basename "$0") --validate "make it pretty no blur sharp eyes camera dolly"
EOF
  exit 0
}

# ---- parse ----
while [ $# -gt 0 ]; do
  case "$1" in
    --model)              MODEL="$2"; shift 2 ;;
    --camera)             CAMERA="$2"; shift 2 ;;
    --camera-detail)      CAMERA_DETAIL="$2"; shift 2 ;;
    --shot-size)          SHOT_SIZE="$2"; shift 2 ;;
    --subject)            SUBJECT="$2"; shift 2 ;;
    --subject-detail)     SUBJECT_DETAIL="$2"; shift 2 ;;
    --micro-expression)   MICRO_EXPR="$2"; shift 2 ;;
    --look)               LOOK="$2"; shift 2 ;;
    --color-grade)        COLOR_GRADE="$2"; shift 2 ;;
    --film-stock)         FILM_STOCK="$2"; shift 2 ;;
    --lighting)           LIGHTING="$2"; shift 2 ;;
    --style)              STYLE="$2"; shift 2 ;;
    --action)             ACTION="$2"; shift 2 ;;
    --aspect)             ASPECT="$2"; shift 2 ;;
    --duration)           DURATION="$2"; shift 2 ;;
    --format)             FORMAT="$2"; shift 2 ;;
    --register-pattern)   REGISTER_PATTERN=1; shift ;;
    --mode)               case "$2" in ugc) UGC_MODE=1 ;; esac; shift 2 ;;
    --character)          CHARACTER="$2"; shift 2 ;;
    --product)            PRODUCT="$2"; shift 2 ;;
    --setting)            SETTING="$2"; shift 2 ;;
    --tone)               TONE="$2"; shift 2 ;;
    --apply-preset)       APPLY_PRESET="$2"; shift 2 ;;
    --validate)           VALIDATE_TEXT="$2"; shift 2 ;;
    --list)               LIST_KIND="$2"; shift 2 ;;
    --selftest)           SELFTEST=1; shift ;;
    -h|--help)            usage ;;
    *) echo "unknown arg: $1" >&2; exit 1 ;;
  esac
done

# ---- helpers ----
need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1" >&2; exit 2; }; }
need jq

data_file() { local f="$DATA_DIR/$1.json"; [ -f "$f" ] || { echo "data missing: $f" >&2; exit 2; }; echo "$f"; }

# ---- LIST mode ----
if [ -n "$LIST_KIND" ]; then
  case "$LIST_KIND" in
    cameras)
      jq -r '.categories | to_entries[] | "## \(.key)\n" + (.value | map("- \(.name): \(.what)") | join("\n"))' "$(data_file cameras)"
      ;;
    shot-sizes)
      jq -r '.shot_sizes[] | "[\(.abbr)] \(.name) — \(.frame)"' "$(data_file shot-sizes)"
      ;;
    micro-expressions)
      jq -r '.micro_expressions[] | "- \(.name): \(.description)"' "$(data_file micro-expressions)"
      ;;
    color-grades)
      jq -r '.color_grades[] | "- \(.mood): \(.description)"' "$(data_file color-grades)"
      ;;
    film-stocks)
      jq -r '.film_stocks[] | "- \(.name): \(.description)"' "$(data_file film-stocks)"
      ;;
    lighting)
      jq -r '.lighting_types[] | "- \(.name): \(.description)"' "$(data_file lighting)"
      ;;
    styles)
      jq -r '.platform_styles[] | "- \(.name): \(.description)"' "$(data_file styles)"
      ;;
    *) echo "unknown list kind: $LIST_KIND" >&2; exit 1 ;;
  esac
  exit 0
fi

# ---- VALIDATE mode ----
if [ -n "$VALIDATE_TEXT" ]; then
  errors=()
  word_count=$(echo "$VALIDATE_TEXT" | wc -w | tr -d ' ')
  [ "$word_count" -gt 200 ] && errors+=("word_count=$word_count exceeds 200")
  echo "$VALIDATE_TEXT" | grep -qiE 'no blur|not blurry|don.?t|avoid|never|without' && errors+=("contains negative phrasing — phrase positively")
  if [ ${#errors[@]} -eq 0 ]; then
    echo "OK ($word_count words, no negatives detected)"
    exit 0
  else
    printf 'FAIL:\n  - %s\n' "${errors[@]}"
    exit 1
  fi
fi

# ---- SELFTEST mode ----
if [ "$SELFTEST" -eq 1 ]; then
  echo "[selftest] data files..."
  for f in cameras shot-sizes micro-expressions color-grades film-stocks lighting styles; do
    [ -f "$DATA_DIR/$f.json" ] || { echo "  MISSING $f.json" ; exit 2; }
    jq empty "$DATA_DIR/$f.json" 2>/dev/null || { echo "  INVALID $f.json"; exit 2; }
    echo "  ok $f.json"
  done
  echo "[selftest] composing 3 known-good prompts..."
  for tc in \
    "kling-3.0|Robo Arm|matte black travel mug|cinematic commercial, warm neutrals|hot coffee pours, steam rises|5" \
    "seedance-2.0|Bullet Time|martial artist mid-kick|epic fantasy, deep jewel tones, volumetric light|opponent freezes, camera orbits|10" \
    "veo-3.1|Snorricam|nervous influencer in gym|cinematic, low-key, harsh side light|he turns to camera, breathing heavy|8"; do
    IFS='|' read -r m c s l a d <<<"$tc"
    out="$($0 --model "$m" --camera "$c" --subject "$s" --look "$l" --action "$a" --duration "$d" 2>&1)"
    [ -z "$out" ] && { echo "  FAIL $m/$c"; exit 1; }
    echo "  ok $m / $c ($(echo "$out" | wc -w | tr -d ' ') words)"
  done
  echo "[selftest] PASS"
  exit 0
fi

# ---- UGC compose mode (Sean Claude formula: Character → Product → Setting → Lighting → Camera → Tone) ----
if [ "$UGC_MODE" -eq 1 ]; then
  [ -z "$CHARACTER" ] && [ -z "$SUBJECT" ] && { echo "ugc mode needs --character (or --subject as fallback)" >&2; exit 1; }
  [ -z "$ACTION" ]  && { echo "missing --action" >&2; exit 1; }

  CHARACTER="${CHARACTER:-$SUBJECT}"
  ugc_setting="${SETTING:-${LIGHTING:+$LIGHTING setting}}"
  ugc_camera_full="$CAMERA"
  [ -n "$CAMERA_DETAIL" ] && ugc_camera_full="$ugc_camera_full $CAMERA_DETAIL"
  [ -z "$ugc_camera_full" ] && ugc_camera_full="iPhone selfie feel"

  # 6-layer order: Character → Product → Setting → Lighting → Camera → Action → Tone
  prompt="Character: $CHARACTER."
  [ -n "$PRODUCT" ]      && prompt="$prompt Product: $PRODUCT."
  [ -n "$ugc_setting" ]  && prompt="$prompt Setting: $ugc_setting."
  [ -n "$LIGHTING" ]     && prompt="$prompt Lighting: $LIGHTING."
  prompt="$prompt Camera: $ugc_camera_full."
  prompt="$prompt $ACTION."
  prompt="$prompt Tone: $TONE."
  [ -n "$ASPECT" ]   && prompt="$prompt Aspect $ASPECT."
  [ -n "$DURATION" ] && prompt="$prompt Duration ${DURATION}s."

  wc_n=$(echo "$prompt" | wc -w | tr -d ' ')
  if [ "$FORMAT" = "json" ]; then
    jq -n --arg model "$MODEL" --arg mode "ugc" --arg character "$CHARACTER" --arg product "$PRODUCT" \
          --arg setting "$ugc_setting" --arg lighting "$LIGHTING" --arg camera "$ugc_camera_full" \
          --arg action "$ACTION" --arg tone "$TONE" --arg aspect "$ASPECT" --arg duration "$DURATION" \
          --arg prompt "$prompt" --arg wc "$wc_n" \
          '{model:$model, mode:$mode, character:$character, product:$product, setting:$setting, lighting:$lighting, camera:$camera, action:$action, tone:$tone, aspect:$aspect, duration:$duration, prompt:$prompt, word_count:($wc|tonumber)}'
  else
    echo "$prompt"
  fi
  exit 0
fi

# ---- CINEMATIC compose mode (default — Subject → Action → Camera → Look) ----
[ -z "$SUBJECT" ] && { echo "missing --subject" >&2; exit 1; }
[ -z "$ACTION" ]  && { echo "missing --action" >&2; exit 1; }

# Build LOOK from sub-flags if not given verbatim
if [ -z "$LOOK" ]; then
  parts=()
  [ -n "$STYLE" ]       && parts+=("$STYLE")
  [ -n "$COLOR_GRADE" ] && parts+=("$COLOR_GRADE color grade")
  [ -n "$FILM_STOCK" ]  && parts+=("$FILM_STOCK film stock")
  [ -n "$LIGHTING" ]    && parts+=("$LIGHTING lighting")
  if [ ${#parts[@]} -gt 0 ]; then
    LOOK=$(IFS=', '; echo "${parts[*]}")
  fi
fi

# Optional preset merge from a sibling higgsfield-preset-lib skill.
# Set MCSLA_PRESET_LIB_SH to the path of your preset-apply.sh to enable.
# Without that env var, --apply-preset is a no-op (composition still works).
if [ -n "$APPLY_PRESET" ]; then
  PRESET_SH="${MCSLA_PRESET_LIB_SH:-}"
  if [ -n "$PRESET_SH" ] && [ -x "$PRESET_SH" ]; then
    pjson="$("$PRESET_SH" --name "$APPLY_PRESET" --format json 2>/dev/null)"
    if [ -n "$pjson" ]; then
      l2="$(echo "$pjson" | jq -r '.layer2 // ""')"
      l7="$(echo "$pjson" | jq -r '.layer7 // ""')"
      [ -n "$l2" ] && LOOK="${LOOK:+$LOOK, }$l2"
      [ -n "$l7" ] && CAMERA_DETAIL="${CAMERA_DETAIL:+$CAMERA_DETAIL, }$l7"
    fi
  fi
fi

# Compose subject block
subj_full="$SUBJECT"
[ -n "$SUBJECT_DETAIL" ] && subj_full="$subj_full, $SUBJECT_DETAIL"
[ -n "$MICRO_EXPR" ]     && subj_full="$subj_full, $MICRO_EXPR"

# Compose camera block
cam_full=""
if [ -n "$CAMERA" ]; then
  cam_full="Camera: $CAMERA"
  [ -n "$CAMERA_DETAIL" ] && cam_full="$cam_full $CAMERA_DETAIL"
  [ -n "$SHOT_SIZE" ]     && cam_full="$cam_full ($SHOT_SIZE)"
  cam_full="$cam_full."
fi

# Subject → Action → Camera → Style ordering (the empirical rule)
prompt="$subj_full. $ACTION."
[ -n "$cam_full" ] && prompt="$prompt $cam_full"
[ -n "$LOOK" ]     && prompt="$prompt $LOOK."

# Tail meta
tail=""
[ -n "$ASPECT" ]   && tail="$tail Aspect $ASPECT."
[ -n "$DURATION" ] && tail="$tail Duration ${DURATION}s."
prompt="$prompt$tail"

# Word-count guard
wc_n=$(echo "$prompt" | wc -w | tr -d ' ')
if [ "$wc_n" -gt 200 ]; then
  echo "[warn] $wc_n words > 200 — model may distort. Trim subject/action." >&2
fi

# Output
if [ "$FORMAT" = "json" ]; then
  jq -n --arg model "$MODEL" --arg camera "$CAMERA" --arg subject "$SUBJECT" \
        --arg look "$LOOK" --arg action "$ACTION" --arg aspect "$ASPECT" \
        --arg duration "$DURATION" --arg prompt "$prompt" --arg word_count "$wc_n" \
        '{model:$model, camera:$camera, subject:$subject, look:$look, action:$action, aspect:$aspect, duration:$duration, prompt:$prompt, word_count:($word_count|tonumber)}'
else
  echo "$prompt"
fi

# Optional prompt-bank registration: stores composed prompt into a sibling
# prompt-bank skill. Set MCSLA_PROMPT_BANK_SH=/path/to/prompt-bank.sh to enable.
# Without that env var, --register-pattern is a no-op.
if [ "$REGISTER_PATTERN" -eq 1 ]; then
  PB_SH="${MCSLA_PROMPT_BANK_SH:-}"
  if [ -n "$PB_SH" ] && [ -x "$PB_SH" ]; then
    "$PB_SH" add --bucket mcsla --body "$prompt" --tags "$CAMERA,$MODEL" 2>/dev/null || \
      echo "[warn] prompt-bank registration failed (non-blocking)" >&2
  fi
fi

exit 0
