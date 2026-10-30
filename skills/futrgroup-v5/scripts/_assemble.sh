#!/usr/bin/env bash
# _assemble.sh — Universal final-assembly: concat V*.mp4 + Realism Filter + VO mux + loudnorm
#
# Usage:
#   _assemble.sh --workdir <dir> [--style claymation|realistic]
#
# Reads:
#   workdir/4-clips/V*.mp4     (linked clips)
#   workdir/5-voice/vo.mp3     (voiceover)
# Writes:
#   workdir/7-edit/concat-only.mp4    (raw concat with Realism Filter)
#   workdir/7-edit/final.mp4          (final with VO mux + loudnorm)
#   workdir/7-edit/manifest.json

set -uo pipefail

WORKDIR=""
STYLE="claymation"
while [ $# -gt 0 ]; do
  case "$1" in
    --workdir) WORKDIR="$2"; shift 2 ;;
    --style)   STYLE="$2"; shift 2 ;;
    *)         shift ;;
  esac
done
[ -z "$WORKDIR" ] && { echo "missing --workdir" >&2; exit 1; }

CLIPS="$WORKDIR/4-clips"
VO="$WORKDIR/5-voice/vo.mp3"
OUT="$WORKDIR/7-edit"
mkdir -p "$OUT"

CLIP_COUNT=$(ls "$CLIPS"/V*.mp4 2>/dev/null | wc -l | tr -d ' ')
[ "$CLIP_COUNT" -eq 0 ] && { echo "[assemble] no clips in $CLIPS" >&2; exit 1; }
echo "[assemble] $CLIP_COUNT clips, style=$STYLE"

# Normalize all clips to 1080x1920@30fps H.264 first.
# Mixed sources (Kling Pro 1076×1924@24fps, Veo 720×1280@24fps, Ken Burns 1080×1920@30fps)
# can't be concat'd via the concat protocol — need matching codec params.
NORM_DIR="$WORKDIR/4-clips-normalized"
mkdir -p "$NORM_DIR"
NEED_NORM=0
for v in $(ls "$CLIPS"/V*.mp4 | sort); do
  out="$NORM_DIR/$(basename "$v")"
  if [ ! -s "$out" ] || [ "$v" -nt "$out" ]; then
    NEED_NORM=1
  fi
done

if [ "$NEED_NORM" -eq 1 ]; then
  echo "[assemble] normalizing $CLIP_COUNT clips to 1080x1920@30fps..."
  for v in $(ls "$CLIPS"/V*.mp4 | sort); do
    out="$NORM_DIR/$(basename "$v")"
    [ -s "$out" ] && [ "$out" -nt "$v" ] && continue
    ffmpeg -y -i "$v" \
      -vf "scale=1080:1920:force_original_aspect_ratio=increase,crop=1080:1920,fps=30,setsar=1" \
      -c:v libx264 -preset fast -crf 20 -pix_fmt yuv420p -r 30 -an "$out" 2>/dev/null
  done
fi
CLIPS="$NORM_DIR"

# Realism Filter values per style
# claymation = Franky v5 canonical
# realistic = Franky v5.1 canonical (slightly different — pulled from CHEAT-SHEET intel)
case "$STYLE" in
  claymation)
    EQ="brightness=-0.03:contrast=1.12:saturation=0.94:gamma=0.96"
    ;;
  realistic)
    # v5.1 documentary realism — lifted shadows, subtle warmth, soft contrast
    EQ="brightness=-0.02:contrast=1.10:saturation=0.92:gamma=1.02"
    ;;
  *)
    EQ="brightness=-0.03:contrast=1.12:saturation=0.94:gamma=0.96"
    ;;
esac

# Concat list
CONCAT="$OUT/concat.txt"
: > "$CONCAT"
for v in $(ls "$CLIPS"/V*.mp4 | sort); do echo "file '$v'" >> "$CONCAT"; done
echo "[assemble] concat list: $(wc -l < "$CONCAT") clips"

# Stage 1: concat + scale + Realism Filter
echo "[assemble] ffmpeg concat..."
ffmpeg -y -f concat -safe 0 -i "$CONCAT" \
  -vf "scale=1080:1920:force_original_aspect_ratio=increase,crop=1080:1920,eq=$EQ" \
  -c:v libx264 -preset fast -crf 20 -pix_fmt yuv420p -an "$OUT/concat-only.mp4" 2>&1 | tail -2

VID_DUR=$(ffprobe -v error -show_entries format=duration -of default=nw=1:nk=1 "$OUT/concat-only.mp4" 2>/dev/null)
echo "[assemble] concat duration: ${VID_DUR}s"

# Stage 2: VO mux at video length (apad if VO shorter)
if [ -f "$VO" ]; then
  VO_DUR=$(ffprobe -v error -show_entries format=duration -of default=nw=1:nk=1 "$VO" 2>/dev/null)
  echo "[assemble] VO duration: ${VO_DUR}s"
  ffmpeg -y -i "$OUT/concat-only.mp4" -i "$VO" \
    -filter_complex "[1:a]apad,atrim=0:${VID_DUR},loudnorm=I=-23:TP=-1.5:LRA=11[a]" \
    -c:v copy -c:a aac -b:a 192k -ar 48000 \
    -map 0:v -map "[a]" \
    "$OUT/final.mp4" 2>&1 | tail -2
else
  echo "[assemble] no VO, copying as final"
  cp "$OUT/concat-only.mp4" "$OUT/final.mp4"
fi

# Manifest
cat > "$OUT/manifest.json" <<EOF
{
  "stage": 7,
  "engine": "ffmpeg-direct",
  "style": "$STYLE",
  "realism_filter_eq": "$EQ",
  "clip_count": $CLIP_COUNT,
  "video_duration_s": ${VID_DUR:-0},
  "vo_present": $([ -f "$VO" ] && echo true || echo false),
  "loudnorm_target_lufs": -23,
  "outputs": {
    "concat_only": "$OUT/concat-only.mp4",
    "final": "$OUT/final.mp4"
  },
  "completed_at": "$(date -u +%FT%TZ)"
}
EOF

ls -lh "$OUT/final.mp4"
ffprobe -v error -show_entries format=duration,size -of default=nw=0 "$OUT/final.mp4" 2>&1 | head -3
echo "[assemble] DONE → $OUT/final.mp4"
exit 0
