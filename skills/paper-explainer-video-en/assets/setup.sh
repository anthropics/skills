#!/bin/bash
# One-time setup: build a local venv in a non-iCloud dir + install deps + fetch Live2D sample models.
set -e
VENV="$HOME/llm_mc_venv"

echo "== 1. Build local venv (non-iCloud, avoids render hangs): $VENV =="
[ -d "$VENV" ] || /opt/homebrew/bin/python3 -m venv "$VENV"
"$VENV/bin/python" -m pip install --quiet --upgrade pip

echo "== 2. Install deps (manim / edge-tts / live2d-py / GL / scientific) =="
"$VENV/bin/python" -m pip install --quiet \
  manim edge-tts live2d-py glfw PyOpenGL pillow numpy scipy

echo "== 3. Fetch free Live2D sample models into /tmp/live2dpy =="
if [ ! -d /tmp/live2dpy ]; then
  git clone --depth 1 https://github.com/Arkueid/live2d-py /tmp/live2dpy
fi
echo "Available models:"; find /tmp/live2dpy -name "*.model3.json" | sed 's/^/  /'

echo "== 4. Self-check =="
"$VENV/bin/python" -c "import manim,edge_tts,numpy,scipy,glfw,OpenGL; import live2d.v3; print('deps OK')"
command -v ffmpeg >/dev/null && echo "ffmpeg OK" || echo "⚠️ ffmpeg missing: brew install ffmpeg"
# English on-screen text uses Helvetica Neue (always on macOS). PingFang SC is kept for any CJK.
ls "/System/Library/Fonts/Helvetica.ttc" >/dev/null 2>&1 || ls "/System/Library/Fonts/HelveticaNeue.ttc" >/dev/null 2>&1 && echo "Latin font OK"
ls /System/Library/Fonts/PingFang.ttc >/dev/null 2>&1 && echo "PingFang CJK font OK (for any CJK glyphs)"
# ★ MathTex scenes need latex. Non-interactive shells often lack TeX on PATH — export before rendering.
if [ -x /Library/TeX/texbin/latex ]; then
  echo "latex OK (MacTeX) — before rendering, run: export PATH=\"/Library/TeX/texbin:\$PATH\""
elif command -v latex >/dev/null; then
  echo "latex OK ($(command -v latex))"
else
  echo "⚠️ latex not found! MathTex scenes will fail silently. Install MacTeX/BasicTeX: brew install --cask basictex"
fi
echo "Done. Use $VENV/bin/python for all rendering; remember to export the TeX PATH."
