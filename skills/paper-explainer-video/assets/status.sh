#!/bin/bash
# 查看渲染/合成进度。在项目(或 /tmp 工作区)目录跑: bash status.sh   (加 -w 滚动刷新)
cd "$(dirname "$0")" || exit 1
PY="$HOME/llm_mc_venv/bin/python"

show() {
  Q=$($PY -c "import pipeline_config as c;print(c.QUALITY)" 2>/dev/null || echo 1080p60)
  BASE=$($PY -c "import pipeline_config as c;print(c.OUTPUT_BASENAME)" 2>/dev/null || echo output)
  SCENES=$($PY -c "import pipeline_config as c;print(' '.join(c.SCENES))" 2>/dev/null)
  DIR="media/videos/scenes/$Q"
  echo "════════ 进度 ($(date +%H:%M:%S)) ════════"
  echo "▌分场景 ($Q):"
  done=0; n=0
  for s in $SCENES; do
    n=$((n+1))
    if [ -f "$DIR/$s.mp4" ]; then
      d=$(ffprobe -v error -show_entries format=duration -of csv=p=0 "$DIR/$s.mp4" 2>/dev/null)
      printf "   ✅ %-18s %5.1fs\n" "$s" "$d"; done=$((done+1))
    elif ps aux | grep -v grep | grep -q "scenes.py.*\b$s\b"; then
      printf "   ⏳ %-18s 渲染中…\n" "$s"
    else
      printf "   ⬜ %-18s 待渲染\n" "$s"
    fi
  done
  echo "   $done/$n"
  echo "▌配音:"; ls media/vo/scene*.mp3 >/dev/null 2>&1 && echo "   ✅ $(ls media/vo/scene*.mp3|wc -l|tr -d ' ') 段" || echo "   ⬜ 未生成"
  echo "▌底片 base_video.mp4:"; [ -f base_video.mp4 ] && echo "   ✅" || echo "   ⬜"
  echo "▌成片:"
  for f in "${BASE}_1080p60.mp4" "${BASE}_live2d.mp4"; do
    [ -f "$f" ] && echo "   ✅ $f ($(du -h "$f"|cut -f1))" || echo "   ⬜ $f"
  done
  echo "▌进程:"; ps aux|grep -v grep|grep -oE "scenes.py [A-Za-z]+|render_avatar.py|build_video.py"|sort -u|sed 's/^/   ▶ /' || echo "   (空闲)"
  echo "▌磁盘:"; df -h /tmp | tail -1 | awk '{print "   /tmp 可用 "$4}'
  echo "═══════════════════════════════════"
}

if [ "$1" = "-w" ]; then while true; do clear; show; sleep 5; done; else show; fi
