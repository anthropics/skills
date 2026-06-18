#!/usr/bin/env bash
# 5-voice.sh — ElevenLabs voiceover with custom voice-direction prompt
# Reads: workdir/2-concept/voice-direction.txt + script (TODO: extracted from concept.json)
# Writes: workdir/5-voice/vo.mp3

set -uo pipefail
SD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$SD/_args.sh"
. "$SD/_siblings.sh"

[ -z "$WORKDIR" ] && { echo "missing --workdir" >&2; exit 1; }
OUT="$WORKDIR/5-voice"
mkdir -p "$OUT"

VO_TEXT="$WORKDIR/2-concept/voice-direction.txt"
[ -f "$VO_TEXT" ] || { echo "[5-voice] missing voice-direction.txt from stage 2" >&2; exit 1; }

# Resolve voiceover sibling
VS="${FUTRGROUP_VOICEOVER_SH:-}"

if [ -n "$VS" ] && [ -x "$VS" ]; then
  echo "[5-voice] using ai-voiceover sibling"
  "$VS" --text-file "$VO_TEXT" --voice-direction-prepend --out "$OUT/vo.mp3" --duration "$DURATION" 2>&1 | tail -3
else
  echo "[FUTRGROUP] WARNING: ai-voiceover not configured (FUTRGROUP_VOICEOVER_SH) — emitting stub vo.txt instead of vo.mp3" >&2
  cat > "$OUT/vo.txt" <<EOF
TODO — ai-voiceover sibling not configured.
Voice direction file: $VO_TEXT
Set FUTRGROUP_VOICEOVER_SH to a script that accepts --text-file --out --duration to produce vo.mp3.
EOF
fi

echo "[5-voice] OK → $OUT"
exit 0
