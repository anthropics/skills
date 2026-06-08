#!/usr/bin/env bash
# _veo-batch.sh — Direct Gemini Veo 3.1 Fast image-to-video for futrgroup-v5
# Free fallback when FAL Kling fails. Note: lower fidelity to start frame.
#
# Single-clip mode (called by 4-animate.sh as fallback):
#   VEO_FRAME=P01.png VEO_PROMPT="..." VEO_OUT=V01.mp4 _veo-batch.sh --single
#
# Batch mode:
#   _veo-batch.sh --batch <workdir>
#
# CLI flags (alternative to env vars):
#   _veo-batch.sh --start <png> --prompt "..." --duration 4 --aspect 9:16 --out <mp4>

set -uo pipefail

GEMINI_KEY="${GEMINI_API_KEY:-}"
[ -z "$GEMINI_KEY" ] && { echo "[veo] GEMINI_API_KEY not set in env" >&2; exit 1; }

# Generate one clip via Veo (call: gen_one start_png prompt duration out_mp4)
gen_one() {
  local start_png="$1"
  local prompt="$2"
  local dur="$3"
  local out_mp4="$4"

  local payload_file
  payload_file=$(mktemp)

  python3 - "$start_png" "$prompt" "$dur" > "$payload_file" <<'PYEOF'
import json, base64, sys
img_path, prompt, dur = sys.argv[1], sys.argv[2], int(sys.argv[3])
with open(img_path, "rb") as f:
    b64 = base64.b64encode(f.read()).decode()
print(json.dumps({
    "instances": [{"prompt": prompt, "image": {"bytesBase64Encoded": b64, "mimeType": "image/png"}}],
    "parameters": {"aspectRatio": "9:16", "durationSeconds": dur, "sampleCount": 1}
}))
PYEOF

  local response op
  response=$(curl -sS -X POST "https://generativelanguage.googleapis.com/v1beta/models/veo-3.1-fast-generate-preview:predictLongRunning?key=$GEMINI_KEY" \
    -H "Content-Type: application/json" --data-binary "@$payload_file" --max-time 60 2>&1)
  op=$(echo "$response" | jq -r '.name // empty')
  rm -f "$payload_file"

  if [ -z "$op" ]; then
    echo "[veo] submit failed: $(echo "$response" | head -c 200)" >&2
    return 1
  fi

  local i r done_ uri
  for i in $(seq 1 30); do
    r=$(curl -sS "https://generativelanguage.googleapis.com/v1beta/${op}?key=$GEMINI_KEY" 2>&1)
    done_=$(echo "$r" | jq -r '.done // false')
    if [ "$done_" = "true" ]; then
      uri=$(echo "$r" | jq -r '.response.generateVideoResponse.generatedSamples[0].video.uri // empty')
      if [ -n "$uri" ]; then
        curl -sSL -H "x-goog-api-key: $GEMINI_KEY" "$uri" -o "$out_mp4" 2>/dev/null
        local sz
        sz=$(wc -c < "$out_mp4" 2>/dev/null || echo 0)
        echo "[veo] OK $out_mp4 ($sz bytes)"
        return 0
      fi
      echo "[veo] DONE no URI" >&2
      return 1
    fi
    sleep 10
  done
  echo "[veo] TIMEOUT (5min)" >&2
  return 1
}

# ── Single-clip mode (env-var or CLI) ──
SINGLE=0
BATCH=""
START="" PROMPT="" DUR=4 OUT=""
while [ $# -gt 0 ]; do
  case "$1" in
    --single)   SINGLE=1; shift ;;
    --batch)    BATCH="$2"; shift 2 ;;
    --start)    START="$2"; shift 2 ;;
    --prompt)   PROMPT="$2"; shift 2 ;;
    --duration) DUR="$2"; shift 2 ;;
    --aspect)   shift 2 ;;   # accepted but Veo handles 9:16 by default
    --out)      OUT="$2"; shift 2 ;;
    *)          shift ;;
  esac
done

# Env-var single-clip path (used by 4-animate.sh fallback)
if [ "$SINGLE" -eq 1 ]; then
  START="${VEO_FRAME:-$START}"
  PROMPT="${VEO_PROMPT:-$PROMPT}"
  OUT="${VEO_OUT:-$OUT}"
  DUR="${VEO_DUR:-$DUR}"
  [ -z "$START" ] || [ -z "$OUT" ] && { echo "[veo --single] need VEO_FRAME + VEO_OUT (or --start + --out)" >&2; exit 1; }
  mkdir -p "$(dirname "$OUT")"
  gen_one "$START" "$PROMPT" "$DUR" "$OUT"
  exit $?
fi

# CLI single-clip path
if [ -n "$START" ] && [ -n "$OUT" ]; then
  mkdir -p "$(dirname "$OUT")"
  gen_one "$START" "$PROMPT" "$DUR" "$OUT"
  exit $?
fi

# Batch mode
if [ -n "$BATCH" ]; then
  FRAMES="$BATCH/3-frames"
  CLIPS="$BATCH/4-clips"
  mkdir -p "$CLIPS"

  FRAMES_LIST=()
  while IFS= read -r line; do FRAMES_LIST+=("$line"); done < <(ls "$FRAMES"/P*.png 2>/dev/null | sort)
  N=${#FRAMES_LIST[@]}
  [ "$N" -lt 2 ] && { echo "[veo] need ≥2 P frames" >&2; exit 1; }

  echo "[veo] batching $((N-1)) clips..."
  for i in $(seq 0 $((N-2))); do
    start="${FRAMES_LIST[$i]}"
    vid_id=$(printf "V%02d" $((i+1)))
    out_mp4="$CLIPS/${vid_id}.mp4"
    [ -s "$out_mp4" ] && { echo "[veo] $vid_id cached"; continue; }
    prompt="seamless cinematic transition with subtle motion. No talking. Soft ambient audio."
    gen_one "$start" "$prompt" "$DUR" "$out_mp4" || echo "[veo] $vid_id failed" >&2
  done
  ls "$CLIPS"/V*.mp4 2>/dev/null | wc -l | xargs -I{} echo "[veo] done: {}/$((N-1)) clips"
  exit 0
fi

echo "Usage:"
echo "  $(basename "$0") --single (uses VEO_FRAME, VEO_PROMPT, VEO_OUT env vars)"
echo "  $(basename "$0") --start <png> --prompt \"...\" --out <mp4>"
echo "  $(basename "$0") --batch <workdir>"
exit 1
