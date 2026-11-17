#!/usr/bin/env bash
# 6-music.sh — Suno custom song
# Reads: workdir/2-concept/suno-prompt.txt
# Writes: workdir/6-music/music.mp3

set -uo pipefail
SD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
. "$SD/_args.sh"
. "$SD/_siblings.sh"

[ -z "$WORKDIR" ] && { echo "missing --workdir" >&2; exit 1; }
OUT="$WORKDIR/6-music"
mkdir -p "$OUT"

PROMPT_FILE="$WORKDIR/2-concept/suno-prompt.txt"
[ -f "$PROMPT_FILE" ] || { echo "[6-music] missing suno-prompt.txt" >&2; exit 1; }

# Resolve music sibling (default: muapi create-music wrapper for Suno V5)
MUAPI_MUSIC="${FUTRGROUP_MUAPI_MUSIC_SH:-}"

if [ -n "$MUAPI_MUSIC" ] && [ -x "$MUAPI_MUSIC" ]; then
  echo "[6-music] using muapi create-music"
  "$MUAPI_MUSIC" --prompt-file "$PROMPT_FILE" --duration "$DURATION" --out "$OUT/music.mp3" 2>&1 | tail -3
else
  echo "[FUTRGROUP] WARNING: muapi create-music not configured (FUTRGROUP_MUAPI_MUSIC_SH) — emitting stub music.txt" >&2
  cat > "$OUT/music.txt" <<EOF
TODO — music sibling not configured.
Prompt file: $PROMPT_FILE
Set FUTRGROUP_MUAPI_MUSIC_SH to a script that accepts --prompt-file --duration --out and produces music.mp3.
EOF
fi

echo "[6-music] OK → $OUT"
exit 0
