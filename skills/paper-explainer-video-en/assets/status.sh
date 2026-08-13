#!/bin/bash
# Show render/mux progress. Run from the project (or /tmp workspace) dir: bash status.sh   (add -w to auto-refresh)
cd "$(dirname "$0")" || exit 1
PY="$HOME/llm_mc_venv/bin/python"

show() {
  Q=$($PY -c "import pipeline_config as c;print(c.QUALITY)" 2>/dev/null || echo 1080p60)
  BASE=$($PY -c "import pipeline_config as c;print(c.OUTPUT_BASENAME)" 2>/dev/null || echo output)
  SCENES=$($PY -c "import pipeline_config as c;print(' '.join(c.SCENES))" 2>/dev/null)
  DIR="media/videos/scenes/$Q"
  echo "════════ Progress ($(date +%H:%M:%S)) ════════"
  echo "▌Scenes ($Q):"
  done=0; n=0
  for s in $SCENES; do
    n=$((n+1))
    if [ -f "$DIR/$s.mp4" ]; then
      d=$(ffprobe -v error -show_entries format=duration -of csv=p=0 "$DIR/$s.mp4" 2>/dev/null)
      printf "   ✅ %-18s %5.1fs\n" "$s" "$d"; done=$((done+1))
    elif ps aux | grep -v grep | grep -q "scenes.py.*\b$s\b"; then
      printf "   ⏳ %-18s rendering…\n" "$s"
    else
      printf "   ⬜ %-18s pending\n" "$s"
    fi
  done
  echo "   $done/$n"
  echo "▌Voiceover:"; ls media/vo/scene*.mp3 >/dev/null 2>&1 && echo "   ✅ $(ls media/vo/scene*.mp3|wc -l|tr -d ' ') clips" || echo "   ⬜ not generated"
  echo "▌Base video base_video.mp4:"; [ -f base_video.mp4 ] && echo "   ✅" || echo "   ⬜"
  echo "▌Final:"
  for f in "${BASE}_1080p60.mp4" "${BASE}_live2d.mp4"; do
    [ -f "$f" ] && echo "   ✅ $f ($(du -h "$f"|cut -f1))" || echo "   ⬜ $f"
  done
  echo "▌Processes:"; ps aux|grep -v grep|grep -oE "scenes.py [A-Za-z]+|render_avatar.py|build_video.py"|sort -u|sed 's/^/   ▶ /' || echo "   (idle)"
  echo "▌Disk:"; df -h /tmp | tail -1 | awk '{print "   /tmp free "$4}'
  echo "═══════════════════════════════════"
}

if [ "$1" = "-w" ]; then while true; do clear; show; sleep 5; done; else show; fi
