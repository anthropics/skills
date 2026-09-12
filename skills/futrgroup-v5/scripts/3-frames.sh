#!/usr/bin/env bash
# 3-frames.sh — NanoBanana Pro renders 18 hero frames (P01..P18)
# Direct Gemini Image API call (gemini-3-pro-image-preview) — no skill dependency.
#
# Reads: workdir/2-concept/concept.json (image_prompts_p1_to_p18)
# Writes: workdir/3-frames/P01.png .. P18.png + prompts.csv
#
# Provider routing:
#   fal+gemini   → direct Gemini Image API ($0.039-0.134/img)
#   muapi        → muapi/scripts/img.sh --model nano-banana-pro
#   higgsfield-cli → only if --use-soul-id

set -uo pipefail
SD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$SD/_args.sh"
. "$SD/_siblings.sh"

[ -z "$WORKDIR" ] && { echo "missing --workdir" >&2; exit 1; }
OUT="$WORKDIR/3-frames"
mkdir -p "$OUT"

CONCEPT="$WORKDIR/2-concept/concept.json"
[ -f "$CONCEPT" ] || { echo "[3-frames] missing concept.json from stage 2" >&2; exit 1; }

# Pre-flight: ad_id required (lineage rule)
[ -f "$WORKDIR/ad-id.json" ] || { echo "[3-frames] missing ad-id.json (must mint before frame gen)" >&2; exit 3; }

PROMPTS_CSV="$OUT/prompts.csv"
echo "id,prompt,status" > "$PROMPTS_CSV"

# GEMINI_API_KEY expected from env
GEMINI_KEY="${GEMINI_API_KEY:-}"
if [ -z "$GEMINI_KEY" ] && [ "$PROVIDER" = "fal+gemini" -o "$PROVIDER" = "gemini" ]; then
  echo "[FUTRGROUP] WARNING: GEMINI_API_KEY not set — Gemini frame gen will fail (export it or use --provider muapi)" >&2
fi

# Sibling shortcuts (resolved by _siblings.sh)
MUAPI_IMG="${FUTRGROUP_MUAPI_IMG_SH:-}"
HFC_GEN="${FUTRGROUP_HIGGSFIELD_GEN_SH:-}"

# Gemini Image API direct generator
generate_via_gemini() {
  local id="$1" prompt="$2" out_png="$OUT/$1.png"
  local model="gemini-3-pro-image-preview"  # NanoBanana Pro
  local payload tmp_resp http_code

  payload=$(jq -n --arg p "$prompt" '{
    contents: [{
      parts: [{text: $p}]
    }],
    generationConfig: {
      responseModalities: ["IMAGE"]
    }
  }')

  tmp_resp="/tmp/nb-$id-$$.json"
  http_code=$(curl -sS -o "$tmp_resp" -w "%{http_code}" \
    -X POST "https://generativelanguage.googleapis.com/v1beta/models/${model}:generateContent" \
    -H "Content-Type: application/json" \
    -H "x-goog-api-key: $GEMINI_KEY" \
    --data "$payload" \
    --max-time 120 2>&1 || echo "000")

  if [ "$http_code" = "200" ]; then
    # Extract base64 image
    local b64
    b64=$(jq -r '.candidates[0].content.parts[] | select(.inlineData) | .inlineData.data' "$tmp_resp" 2>/dev/null | head -1)
    if [ -n "$b64" ]; then
      echo "$b64" | base64 -d > "$out_png" 2>/dev/null
      rm -f "$tmp_resp"
      [ -s "$out_png" ] && return 0
    fi
    echo "[3-frames] $id: 200 but no image in response" >&2
    cp "$tmp_resp" "$OUT/${id}.error.json"
    rm -f "$tmp_resp"
    return 1
  else
    echo "[3-frames] $id: HTTP $http_code" >&2
    cp "$tmp_resp" "$OUT/${id}.error.json"
    rm -f "$tmp_resp"
    return 1
  fi
}

generate_one() {
  local id="$1" prompt="$2" out_png="$OUT/$1.png"
  if [ -z "$prompt" ] || [ "$prompt" = "TODO" ]; then
    echo "[3-frames] $id: skip (prompt is TODO)" >&2
    echo "$id,$prompt,skip-todo" >> "$PROMPTS_CSV"
    return 0
  fi

  # Skip if already generated (resume support)
  if [ -s "$out_png" ]; then
    echo "[3-frames] $id: cached"
    echo "$id,$prompt,cached" >> "$PROMPTS_CSV"
    return 0
  fi

  case "$PROVIDER" in
    fal+gemini|gemini)
      if [ -n "$GEMINI_KEY" ]; then
        if generate_via_gemini "$id" "$prompt"; then
          echo "[3-frames] $id: ok ($(wc -c < "$out_png") bytes)"
          echo "$id,$prompt,ok-gemini" >> "$PROMPTS_CSV"
          return 0
        else
          echo "$id,$prompt,fail-gemini" >> "$PROMPTS_CSV"
          return 1
        fi
      else
        echo "[3-frames] $id: GEMINI_API_KEY missing" >&2
        echo "$id,$prompt,fail-no-gemini-key" >> "$PROMPTS_CSV"
        return 1
      fi
      ;;
    muapi)
      if [ -x "$MUAPI_IMG" ]; then
        "$MUAPI_IMG" --prompt "$prompt" --model nano-banana-pro --aspect "$ASPECT" --out "$out_png" 2>/dev/null && \
          echo "$id,$prompt,ok-muapi" >> "$PROMPTS_CSV" || \
          { echo "$id,$prompt,fail-muapi" >> "$PROMPTS_CSV"; return 1; }
      else
        echo "[3-frames] $id: muapi not installed" >&2
        echo "$id,$prompt,fail-no-muapi" >> "$PROMPTS_CSV"
        return 1
      fi
      ;;
    higgsfield-cli)
      if [ -x "$HFC_GEN" ]; then
        "$HFC_GEN" --prompt "$prompt" --aspect "$ASPECT" --out "$out_png" 2>/dev/null && \
          echo "$id,$prompt,ok-higgsfield" >> "$PROMPTS_CSV" || \
          { echo "$id,$prompt,fail-higgsfield" >> "$PROMPTS_CSV"; return 1; }
      else
        echo "$id,$prompt,fail-no-higgsfield" >> "$PROMPTS_CSV"
        return 1
      fi
      ;;
    *)
      echo "[3-frames] unknown provider: $PROVIDER" >&2
      return 1
      ;;
  esac
}

# Iterate concept.json prompts
if command -v jq >/dev/null 2>&1; then
  N=$(jq '.image_prompts_p1_to_p18 | length' "$CONCEPT" 2>/dev/null || echo 0)
  if [ "$N" -gt 0 ]; then
    for i in $(seq 0 $((N-1))); do
      id="$(jq -r ".image_prompts_p1_to_p18[$i].id" "$CONCEPT")"
      pr="$(jq -r ".image_prompts_p1_to_p18[$i].prompt" "$CONCEPT")"
      generate_one "$id" "$pr" || echo "[warn] $id failed (continuing)" >&2
      sleep 1   # gentle rate limit
    done
  else
    echo "[3-frames] concept.json has 0 prompts — stub mode" >&2
  fi
else
  echo "[3-frames] missing jq — skipping frame gen" >&2
  exit 1
fi

PNG_COUNT=$(ls "$OUT"/P*.png 2>/dev/null | wc -l | tr -d ' ')
echo "[3-frames] DONE → $OUT/"
echo "  prompts.csv ($(wc -l < "$PROMPTS_CSV" | tr -d ' ') rows)"
echo "  PNG count: $PNG_COUNT"
exit 0
