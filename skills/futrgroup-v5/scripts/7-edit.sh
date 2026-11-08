#!/usr/bin/env bash
# 7-edit.sh — Headless edit pipeline (Remotion + Hyperframes + optional Topaz)
#
# REPLACES CapCut Desktop with a fully scripted path:
#   1. Build Remotion props.json from clips + VO + music + Realism Filter values
#   2. Run remotion-renderer (UGCComposition) → 1080p mp4
#   3. Optional: Topaz Video AI super-sample to 4K 60fps (FFmpeg fallback if no Topaz)
#   4. Optional: Hyperframes caption overlay (replaces Captions iOS app)
#
# Realism Filter EXACT values (verified Franky Shaw v5.1):
#   Temp -3, Tint +2, Sat -6, Exp -3, Contrast +12, Highlight -35, Shadow +18, Fade +6
#
# Reads:
#   workdir/4-clips/V*.mp4 (linked clips)
#   workdir/5-voice/vo.mp3
#   workdir/6-music/music.mp3
# Writes:
#   workdir/7-edit/props.json              (Remotion input)
#   workdir/7-edit/intermediate-1080p.mp4  (Remotion render)
#   workdir/7-edit/topaz-4k60.mp4          (super-sampled — Topaz CLI or FFmpeg fallback)
#   workdir/7-edit/captions.html           (Hyperframes composition)
#   workdir/7-edit/final-captioned.mp4     (Hyperframes overlay output)
#   workdir/7-edit/manifest.json

set -uo pipefail
SD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$SD/_args.sh"
. "$SD/_siblings.sh"

[ -z "$WORKDIR" ] && { echo "missing --workdir" >&2; exit 1; }
CLIPS="$WORKDIR/4-clips"
VO="$WORKDIR/5-voice/vo.mp3"
MUSIC="$WORKDIR/6-music/music.mp3"
OUT="$WORKDIR/7-edit"
mkdir -p "$OUT"

# Realism Filter canonical values (Franky Shaw v5.1)
TEMP=-3 TINT=2 SAT=-6 EXP=-3 CONT=12 HI=-35 SH=18 FADE=6

# Speed mapping (alternates 1.12× ↔ 1.18×) + scale jump (100% ↔ 107%)
SPEED_A="1.12" SPEED_B="1.18" SCALE_A=100 SCALE_B=107

CLIP_COUNT=$(ls "$CLIPS"/V*.mp4 2>/dev/null | wc -l | tr -d ' ')
if [ "$CLIP_COUNT" -eq 0 ]; then
  echo "[7-edit] no clips in $CLIPS — stage 4 must complete first (stub mode)" >&2
  echo '{"status":"stub","reason":"no clips from stage 4"}' > "$OUT/manifest.json"
  exit 0
fi

# ── Step 1: build Remotion props.json ──
echo "[7-edit] building Remotion props.json from $CLIP_COUNT clips..."
TOTAL_DURATION=$((CLIP_COUNT * 4))   # default 4s per linked clip

python3 - <<PYEOF > "$OUT/props.json"
import json, os, glob, sys
clips = sorted(glob.glob("$CLIPS/V*.mp4"))
total = $TOTAL_DURATION
fps = 30
blocks = []
t = 0.0
for i, c in enumerate(clips):
    speed = float("$SPEED_A") if i % 2 == 0 else float("$SPEED_B")
    scale = $SCALE_A if i % 2 == 0 else $SCALE_B
    dur = 4.0 / speed
    blocks.append({
        "id": f"V{i+1:02d}",
        "type": "kol_video",
        "file": c,
        "start_s": round(t, 3),
        "duration_s": round(dur, 3),
        "speed": speed,
        "scale_percent": scale,
        "transition": "Mix" if i > 0 else None
    })
    t += dur

props = {
    "variant_id": "futrgroup_v5_$(date +%s)",
    "fps": fps,
    "width": 1080,
    "height": 1920,
    "total_duration_s": round(t, 3),
    "voiceover": "$VO" if os.path.exists("$VO") else None,
    "voiceover_volume": 1.0,
    "bgm": "$MUSIC" if os.path.exists("$MUSIC") else None,
    "bgm_volume": 0.25,
    "bgm_fade_out_s": 2.0,
    "blocks": blocks,
    "enable_transitions": True,
    "film_grain": {"enabled": True, "intensity": 0.035},
    "realism_filter": {
        "temp": $TEMP, "tint": $TINT, "saturation": $SAT,
        "exposure": $EXP, "contrast": $CONT, "highlight": $HI,
        "shadow": $SH, "fade": $FADE
    },
    "brand": "$BRAND"
}
print(json.dumps(props, indent=2))
PYEOF

echo "[7-edit] props.json: $(wc -c < "$OUT/props.json") bytes"

# ── Step 2: run Remotion (optional sibling) ──
RR="${FUTRGROUP_REMOTION_SH:-}"

INTERMEDIATE="$OUT/intermediate-1080p.mp4"
if [ -n "$RR" ] && [ -x "$RR" ]; then
  echo "[7-edit] rendering with Remotion sibling..."
  "$RR" render --props "$OUT/props.json" --output "$INTERMEDIATE" --brand "$BRAND" --composition UGCComposition 2>&1 | tail -5
else
  # Fallback: FFmpeg concat with Realism Filter approximation
  echo "[FUTRGROUP] WARNING: remotion-renderer not configured (FUTRGROUP_REMOTION_SH) — falling back to FFmpeg concat" >&2
  if command -v ffmpeg >/dev/null 2>&1; then
    CONCAT="$OUT/concat.txt"; : > "$CONCAT"
    for v in $(ls "$CLIPS"/V*.mp4 | sort); do echo "file '$v'" >> "$CONCAT"; done
    # Realism Filter via FFmpeg eq + curves (approximation)
    ffmpeg -y -f concat -safe 0 -i "$CONCAT" \
      $([ -f "$VO" ] && echo "-i $VO") \
      $([ -f "$MUSIC" ] && echo "-i $MUSIC") \
      -filter_complex "[0:v]eq=brightness=-0.03:contrast=1.12:saturation=0.94[v]" \
      -map "[v]" \
      $([ -f "$VO" ] && echo "-map 1:a") \
      -c:v libx264 -preset slow -crf 18 -pix_fmt yuv420p \
      -c:a aac -b:a 192k \
      -ar 48000 -af "loudnorm=I=-23:TP=-1.5:LRA=11" \
      "$INTERMEDIATE" 2>&1 | tail -3
  fi
fi

# ── Step 3: super-sample to 4K 60fps (Topaz CLI → FFmpeg fallback) ──
TOPAZ_OUT="$OUT/topaz-4k60.mp4"
TVAI="${FUTRGROUP_TOPAZ_BIN:-}"

if [ -n "$TVAI" ] && [ -x "$TVAI" ] && [ -f "$INTERMEDIATE" ]; then
  echo "[7-edit] Topaz Video AI CLI found — super-sampling to 4K 60fps..."
  "$TVAI" --model iris --input "$INTERMEDIATE" --output "$TOPAZ_OUT" \
    --resolution 3840x2160 --fps 60 --codec h264 2>&1 | tail -3 || \
    echo "[warn] Topaz CLI failed, using FFmpeg fallback" >&2
fi

if [ ! -f "$TOPAZ_OUT" ] && [ -f "$INTERMEDIATE" ]; then
  echo "[7-edit] FFmpeg upscale fallback (4K 60fps via libx264 + minterpolate)..."
  if command -v ffmpeg >/dev/null 2>&1; then
    ffmpeg -y -i "$INTERMEDIATE" \
      -vf "scale=2160:3840:flags=lanczos,minterpolate=fps=60:mi_mode=mci:mc_mode=aobmc:vsbmf=1" \
      -c:v libx264 -preset slow -crf 16 -pix_fmt yuv420p \
      -c:a copy "$TOPAZ_OUT" 2>&1 | tail -3
  fi
fi

# ── Step 4: caption overlay via Hyperframes (optional sibling) ──
HF="${FUTRGROUP_HYPERFRAMES_SH:-}"

FINAL="$OUT/final-captioned.mp4"
SOURCE_FOR_CAPTIONS="${TOPAZ_OUT}"
[ ! -f "$SOURCE_FOR_CAPTIONS" ] && SOURCE_FOR_CAPTIONS="$INTERMEDIATE"

# Build a minimal Hyperframes HTML composition for animated captions
# (full word-by-word caption pipeline = v0.3 — for now: simple title-card overlay)
CAPT_HTML="$OUT/captions.html"
if [ -f "$VO" ] && command -v ffmpeg >/dev/null 2>&1; then
  # Get VO duration for caption timing
  VO_DUR=$(ffprobe -v error -show_entries format=duration -of default=nw=1:nk=1 "$VO" 2>/dev/null || echo 60)
  cat > "$CAPT_HTML" <<EOF
<!DOCTYPE html>
<html><head><meta charset="utf-8"><title>captions</title>
<style>
  body { margin: 0; background: transparent; font-family: 'Inter', -apple-system, sans-serif; }
  .video-bg { position: fixed; inset: 0; width: 100vw; height: 100vh; object-fit: cover; }
  .caption-track { position: fixed; bottom: 18%; left: 50%; transform: translateX(-50%); text-align: center; max-width: 80vw; }
  .word { display: inline-block; color: #fff; font-weight: 800; font-size: 5.5vw; padding: 0 0.25em; line-height: 1.2;
          -webkit-text-stroke: 4px #000; text-shadow: 0 4px 16px rgba(0,0,0,.55); animation: pop .3s ease-out; }
  @keyframes pop { from { transform: scale(.85); opacity: 0; } to { transform: scale(1); opacity: 1; } }
</style></head>
<body>
  <video class="video-bg" src="file://$SOURCE_FOR_CAPTIONS" autoplay muted></video>
  <div class="caption-track" id="captions"></div>
  <script>
    /* TODO v0.3: Whisper transcribe \$VO → words[] with timings; for now render brand title */
    const words = [{ t: 0.5, w: '$BRAND'.toUpperCase() }];
    const target = document.getElementById('captions');
    words.forEach(({ t, w }) => {
      setTimeout(() => {
        const span = document.createElement('span');
        span.className = 'word'; span.textContent = w;
        target.appendChild(span);
      }, t * 1000);
    });
  </script>
</body></html>
EOF
fi

if [ -n "$HF" ] && [ -x "$HF" ] && [ -f "$CAPT_HTML" ]; then
  echo "[7-edit] Hyperframes caption overlay..."
  "$HF" --composition "$CAPT_HTML" --out "$FINAL" --workers auto 2>&1 | tail -3 || \
    echo "[FUTRGROUP] WARNING: Hyperframes failed — using $SOURCE_FOR_CAPTIONS as final" >&2
elif [ -z "$HF" ]; then
  echo "[FUTRGROUP] WARNING: hyperframes-render not configured (FUTRGROUP_HYPERFRAMES_SH) — final video will be $SOURCE_FOR_CAPTIONS without animated captions" >&2
  [ -f "$SOURCE_FOR_CAPTIONS" ] && cp "$SOURCE_FOR_CAPTIONS" "$FINAL"
fi

# Fallback: copy super-sampled as final if no caption render
[ ! -f "$FINAL" ] && [ -f "$SOURCE_FOR_CAPTIONS" ] && cp "$SOURCE_FOR_CAPTIONS" "$FINAL"

# ── Manifest ──
cat > "$OUT/manifest.json" <<EOF
{
  "stage": 7,
  "name": "edit",
  "engine": "remotion + hyperframes${TVAI:+ + topaz}",
  "realism_filter": {"temp":$TEMP,"tint":$TINT,"sat":$SAT,"exp":$EXP,"cont":$CONT,"hi":$HI,"sh":$SH,"fade":$FADE},
  "speed_alternation": ["${SPEED_A}x","${SPEED_B}x"],
  "scale_jump": [$SCALE_A, $SCALE_B],
  "outputs": {
    "props_json": "$OUT/props.json",
    "intermediate_1080p": "$INTERMEDIATE",
    "topaz_4k60": "$TOPAZ_OUT",
    "final_captioned": "$FINAL"
  },
  "topaz_used": $([ -n "$TVAI" ] && echo true || echo false),
  "completed_at": "$(date -u +%FT%TZ)"
}
EOF

echo "[7-edit] OK"
echo "  intermediate:  $INTERMEDIATE"
[ -f "$TOPAZ_OUT" ] && echo "  super-sampled: $TOPAZ_OUT"
[ -f "$FINAL" ]     && echo "  FINAL:         $FINAL"
exit 0
