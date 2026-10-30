#!/usr/bin/env bash
# _fal-kling.sh — Direct FAL Kling v3 Pro image-to-video for futrgroup-v5
# Replaces the broken video-gen.sh kling path. Uses fal_client Python SDK for
# CDN upload + queue API for the actual gen.
#
# Usage:
#   _fal-kling.sh --start <png> --prompt "..." --duration 5 --aspect 9:16 --out V01.mp4
#   _fal-kling.sh --batch <workdir> --concept-json <path>   (run all 17)

set -uo pipefail
SD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

START="" PROMPT="" DUR=5 ASPECT="9:16" OUT="" MODEL="v3/pro" BATCH_DIR="" CONCEPT=""
while [ $# -gt 0 ]; do
  case "$1" in
    --start)         START="$2"; shift 2 ;;
    --prompt)        PROMPT="$2"; shift 2 ;;
    --duration)      DUR="$2"; shift 2 ;;
    --aspect)        ASPECT="$2"; shift 2 ;;
    --out)           OUT="$2"; shift 2 ;;
    --model)         MODEL="$2"; shift 2 ;;
    --batch)         BATCH_DIR="$2"; shift 2 ;;
    --concept-json)  CONCEPT="$2"; shift 2 ;;
    *)               shift ;;
  esac
done

# Load FAL key from env (FAL_API_KEY or FAL_KEY)
FAL_KEY="${FAL_API_KEY:-${FAL_KEY:-}}"
[ -z "$FAL_KEY" ] && { echo "[fal-kling] FAL_API_KEY not set in env" >&2; exit 1; }

# Upload helper — tries fal_client SDK first, falls back to catbox.moe (no auth required)
upload_to_fal() {
  local file="$1"
  local url=""

  # Try fal_client (FAL CDN — preferred when available)
  url=$(python3 -c "
import os, sys
os.environ['FAL_KEY']='$FAL_KEY'
import fal_client
try:
    print(fal_client.upload_file(sys.argv[1]))
except Exception:
    pass
" "$file" 2>/dev/null)

  if [ -n "$url" ] && [[ "$url" =~ ^https?:// ]]; then
    echo "$url"
    return 0
  fi

  # Fallback: catbox.moe (free, no auth, public)
  url=$(curl -sS --max-time 30 -F "reqtype=fileupload" -F "fileToUpload=@$file" \
    https://catbox.moe/user/api.php 2>/dev/null)
  if [ -n "$url" ] && [[ "$url" =~ ^https?:// ]]; then
    echo "$url"
    return 0
  fi

  # Fallback 2: uguu.se
  url=$(curl -sS --max-time 30 -F "files[]=@$file" https://uguu.se/upload 2>/dev/null | \
    python3 -c "import json,sys; d=json.load(sys.stdin); print(d['files'][0]['url'])" 2>/dev/null)
  if [ -n "$url" ] && [[ "$url" =~ ^https?:// ]]; then
    echo "$url"
    return 0
  fi

  return 1
}

# Single-clip gen (call: gen_one start_png prompt duration out_mp4)
gen_one() {
  local start_png="$1"
  local prompt="$2"
  local dur="$3"
  local out_mp4="$4"

  local img_url
  img_url=$(upload_to_fal "$start_png")
  if [ -z "$img_url" ]; then
    echo "[fal-kling] upload failed: $start_png" >&2
    return 1
  fi

  local payload resp req_id status_url response_url
  payload=$(jq -n --arg url "$img_url" --arg p "$prompt" --arg dur "$dur" --arg ar "$ASPECT" '{
    image_url: $url, prompt: $p, duration: $dur, aspect_ratio: $ar
  }')

  resp=$(curl -sS -X POST "https://queue.fal.run/fal-ai/kling-video/${MODEL}/image-to-video" \
    -H "Authorization: Key $FAL_KEY" -H "Content-Type: application/json" \
    --data "$payload" --max-time 30 2>&1)
  req_id=$(echo "$resp" | jq -r '.request_id // empty')
  status_url=$(echo "$resp" | jq -r '.status_url // empty')
  response_url=$(echo "$resp" | jq -r '.response_url // empty')

  if [ -z "$req_id" ] || [ -z "$status_url" ]; then
    echo "[fal-kling] submit failed: $resp" >&2
    return 1
  fi

  echo "[fal-kling] req=$req_id submitted, polling..."
  local s i
  for i in $(seq 1 60); do
    s=$(curl -sS -H "Authorization: Key $FAL_KEY" "$status_url" 2>&1 | jq -r '.status // "ERROR"')
    case "$s" in
      COMPLETED)
        local result url
        result=$(curl -sS -H "Authorization: Key $FAL_KEY" "$response_url" 2>&1)
        url=$(echo "$result" | jq -r '.video.url // empty')
        if [ -n "$url" ]; then
          curl -sSL -o "$out_mp4" "$url"
          echo "[fal-kling] OK $out_mp4 ($(wc -c < "$out_mp4") bytes)"
          return 0
        fi
        echo "[fal-kling] COMPLETED but no URL — body: $result" >&2
        return 1
        ;;
      FAILED|ERROR)
        echo "[fal-kling] $s" >&2
        return 1
        ;;
      IN_QUEUE|IN_PROGRESS)
        sleep 10
        ;;
      *)
        echo "[fal-kling] unknown status: $s" >&2
        sleep 10
        ;;
    esac
  done
  echo "[fal-kling] TIMEOUT (10min)" >&2
  return 1
}

# Single-clip mode
if [ -n "$START" ] && [ -n "$OUT" ]; then
  mkdir -p "$(dirname "$OUT")"
  gen_one "$START" "$PROMPT" "$DUR" "$OUT"
  exit $?
fi

# Batch mode (P01..P18 → V01..V17 linked chain)
if [ -n "$BATCH_DIR" ]; then
  FRAMES="$BATCH_DIR/3-frames"
  CLIPS="$BATCH_DIR/4-clips"
  mkdir -p "$CLIPS"

  CONCEPT="${CONCEPT:-$BATCH_DIR/2-concept/concept.json}"
  [ ! -f "$CONCEPT" ] && { echo "[fal-kling] missing concept.json: $CONCEPT" >&2; exit 1; }

  # Collect P frames in order
  FRAMES_LIST=()
  while IFS= read -r line; do FRAMES_LIST+=("$line"); done < <(ls "$FRAMES"/P*.png 2>/dev/null | sort)
  N=${#FRAMES_LIST[@]}
  [ "$N" -lt 2 ] && { echo "[fal-kling] need ≥2 P frames, got $N" >&2; exit 1; }

  echo "[fal-kling] batching $((N-1)) linked clips via Kling $MODEL..."
  fail_count=0
  for i in $(seq 0 $((N-2))); do
    start="${FRAMES_LIST[$i]}"
    vid_id=$(printf "V%02d" $((i+1)))
    out_mp4="$CLIPS/${vid_id}.mp4"

    if [ -s "$out_mp4" ]; then
      echo "[fal-kling] $vid_id: cached"
      continue
    fi

    # Pull motion prompt for this beat from concept.json (best-effort) or use generic
    motion_prompt=""
    if command -v jq >/dev/null 2>&1; then
      motion_prompt=$(jq -r ".image_prompts_p1_to_p18[$((i+1))].prompt // empty" "$CONCEPT" 2>/dev/null | head -c 400)
    fi
    [ -z "$motion_prompt" ] && motion_prompt="create a seamless cinematic transition with subtle motion. No talking, soft ambient audio."

    # Add Kling motion qualifier (motion-only, not redescribing the static frame per OSide MCSLA rule)
    final_prompt="seamless cinematic transition. ${motion_prompt:0:300}. No talking. Soft ambient audio."

    if ! gen_one "$start" "$final_prompt" "$DUR" "$out_mp4"; then
      fail_count=$((fail_count+1))
      echo "[fal-kling] $vid_id FAILED — continuing" >&2
    fi
    sleep 1
  done

  ok_count=$(ls "$CLIPS"/V*.mp4 2>/dev/null | wc -l | tr -d ' ')
  echo "[fal-kling] batch done: $ok_count/$((N-1)) clips, $fail_count failures"
  [ "$fail_count" -eq 0 ] && exit 0 || exit 1
fi

echo "Usage:"
echo "  $(basename "$0") --start <png> --prompt \"...\" --duration 5 --aspect 9:16 --out <mp4>"
echo "  $(basename "$0") --batch <workdir> [--concept-json <path>]"
exit 1
