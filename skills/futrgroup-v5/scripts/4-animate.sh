#!/usr/bin/env bash
# 4-animate.sh — LINKED frame chain via Kling 3.0 (the Franky Shaw signature)
#
# For each adjacent pair (P_n.png, P_n+1.png) generate V_n.mp4 with:
#   start_frame = P_n.png
#   end_frame   = P_n+1.png
#   prompt      = MCSLA-built motion-only prompt (3-8 sec)
#
# This is the non-obvious technique most copy-cats miss — chains are LINKED,
# same PNG appears as end-of-V_n and start-of-V_n+1.
#
# Reads: workdir/3-frames/P*.png + concept.json motion hints
# Writes: workdir/4-clips/V01.mp4 .. V17.mp4 + prompts.csv
#
# Provider routing:
#   fal+gemini   → video-gen skill (FAL Kling 3.0, $0.05/clip)
#   muapi        → muapi/i2v.sh --model kling-pro
#   higgsfield-cli → higgsfield generate create kling3_0 --start-image --end-image

set -uo pipefail
SD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$SD/_args.sh"
. "$SD/_siblings.sh"

[ -z "$WORKDIR" ] && { echo "missing --workdir" >&2; exit 1; }
FRAMES="$WORKDIR/3-frames"
OUT="$WORKDIR/4-clips"
mkdir -p "$OUT"

# Collect P*.png in order (bash 3.2 compat — no mapfile)
FRAMES_LIST=()
while IFS= read -r line; do
  FRAMES_LIST+=("$line")
done < <(ls "$FRAMES"/P*.png 2>/dev/null | sort)
N=${#FRAMES_LIST[@]}
if [ "$N" -lt 2 ]; then
  echo "[4-animate] need ≥2 P frames, found $N — stage 3 must complete first" >&2
  exit 1
fi

PROMPTS_CSV="$OUT/prompts.csv"
echo "id,start_frame,end_frame,prompt,duration,status" > "$PROMPTS_CSV"

# Resolve generators (from _siblings.sh)
VG="${FUTRGROUP_VIDEO_GEN_SH:-}"          # video-gen.sh (FAL Kling)
MUAPI_I2V="${FUTRGROUP_MUAPI_I2V_SH:-}"
HFC_GEN="${FUTRGROUP_HIGGSFIELD_I2V_SH:-}"
MCSLA="${FUTRGROUP_MCSLA_SH:-}"

# Build motion prompt — Franky's transition prompt formula
build_motion_prompt() {
  local start="$1" end="$2"
  local style="${STYLE:-claymation}"
  if [ -n "$MCSLA" ] && [ -x "$MCSLA" ]; then
    "$MCSLA" --model kling-3.0 --camera "Dolly In" \
      --subject "subject from start frame" \
      --look "$style" \
      --action "create a seamless $style animated transition between the first shot and the second shot in a $style animation style with sound effects (no talking)" \
      --aspect "$ASPECT" --duration 4 2>/dev/null
  else
    echo "create a seamless $style animated transition between the first shot and the second shot in a $style animation style with sound effects (no talking)"
  fi
}

# Generate linked clips
for i in $(seq 0 $((N-2))); do
  start_png="${FRAMES_LIST[$i]}"
  end_png="${FRAMES_LIST[$((i+1))]}"
  vid_id="$(printf 'V%02d' $((i+1)))"
  out_mp4="$OUT/${vid_id}.mp4"
  motion_prompt="$(build_motion_prompt "$start_png" "$end_png")"

  # Resume support — skip if already generated
  if [ -s "$out_mp4" ]; then
    echo "[4-animate] $vid_id: cached"
    echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,cached" >> "$PROMPTS_CSV"
    continue
  fi

  case "$PROVIDER" in
    fal-kling|fal+kling|fal+gemini)
      # Primary: FAL Kling v3 Pro (the OG Franky Shaw path, $0.56/clip, identity-faithful)
      FK="$SD/_fal-kling.sh"
      if [ -x "$FK" ]; then
        if "$FK" --start "$start_png" --prompt "$motion_prompt" --duration 5 --aspect "$ASPECT" --out "$out_mp4"; then
          echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,5,ok-fal-kling-v3" >> "$PROMPTS_CSV"
        else
          # Fallback: Gemini Veo 3.1 Fast (free preview tier, may drift)
          echo "[4-animate] $vid_id: FAL Kling failed, trying Veo 3.1 fallback..." >&2
          VEO="$SD/_veo-batch.sh"
          if [ -x "$VEO" ]; then
            VEO_FRAME="$start_png" VEO_PROMPT="$motion_prompt" VEO_OUT="$out_mp4" "$VEO" --single 2>&1 | tail -3 || true
          fi
          if [ -s "$out_mp4" ]; then
            echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,ok-veo-fallback" >> "$PROMPTS_CSV"
          else
            echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,fail-fal-kling-and-veo" >> "$PROMPTS_CSV"
          fi
        fi
      else
        echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,fail-no-fal-kling-script" >> "$PROMPTS_CSV"
      fi
      ;;
    veo|gemini-veo)
      # Veo 3.1 Fast preview (free path)
      VEO="$SD/_veo-batch.sh"
      if [ -x "$VEO" ]; then
        VEO_FRAME="$start_png" VEO_PROMPT="$motion_prompt" VEO_OUT="$out_mp4" "$VEO" --single 2>&1 | tail -3
        [ -s "$out_mp4" ] && echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,ok-veo" >> "$PROMPTS_CSV" \
                          || echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,fail-veo" >> "$PROMPTS_CSV"
      fi
      ;;
    muapi)
      if [ -n "$MUAPI_I2V" ] && [ -x "$MUAPI_I2V" ]; then
        "$MUAPI_I2V" --start "$start_png" --end "$end_png" --prompt "$motion_prompt" --model kling-pro --duration 4 --aspect "$ASPECT" --out "$out_mp4" 2>/dev/null && \
          echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,ok-muapi" >> "$PROMPTS_CSV" || \
          echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,fail-muapi" >> "$PROMPTS_CSV"
      else
        echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,fail-no-muapi" >> "$PROMPTS_CSV"
      fi
      ;;
    higgsfield-cli)
      if [ -n "$HFC_GEN" ] && [ -x "$HFC_GEN" ]; then
        "$HFC_GEN" --start "$start_png" --end "$end_png" --prompt "$motion_prompt" --model kling3_0 --duration 4 --aspect "$ASPECT" --out "$out_mp4" 2>/dev/null && \
          echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,ok-higgsfield" >> "$PROMPTS_CSV" || \
          echo "$vid_id,$(basename "$start_png"),$(basename "$end_png"),$motion_prompt,4,fail-higgsfield" >> "$PROMPTS_CSV"
      fi
      ;;
  esac

  # Card-flip detector (optional sibling)
  CF="${FUTRGROUP_CARDFLIP_SH:-}"
  if [ -f "$out_mp4" ] && [ -n "$CF" ] && [ -x "$CF" ]; then
    if ! "$CF" --video "$out_mp4" 2>/dev/null; then
      echo "[4-animate] $vid_id: CARD-FLIP detected — quarantining + retry needed" >&2
      mv "$out_mp4" "$out_mp4.cardflip-rejected"
    fi
  fi
done

echo "[4-animate] DONE → $OUT/"
echo "  V*.mp4 count: $(ls "$OUT"/V*.mp4 2>/dev/null | wc -l | tr -d ' ')"
exit 0
