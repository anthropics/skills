#!/bin/bash
# 一次性环境准备: 在非 iCloud 目录建本地 venv + 装依赖 + 拉 Live2D 样例模型。
set -e
VENV="$HOME/llm_mc_venv"

echo "== 1. 建本地 venv (非 iCloud, 避免渲染卡死): $VENV =="
[ -d "$VENV" ] || /opt/homebrew/bin/python3 -m venv "$VENV"
"$VENV/bin/python" -m pip install --quiet --upgrade pip

echo "== 2. 装依赖 (manim / edge-tts / live2d-py / GL / 科学计算) =="
"$VENV/bin/python" -m pip install --quiet \
  manim edge-tts live2d-py glfw PyOpenGL pillow numpy scipy

echo "== 3. 拉 Live2D 免费样例模型到 /tmp/live2dpy =="
if [ ! -d /tmp/live2dpy ]; then
  git clone --depth 1 https://github.com/Arkueid/live2d-py /tmp/live2dpy
fi
echo "可用模型:"; find /tmp/live2dpy -name "*.model3.json" | sed 's/^/  /'

echo "== 4. 自检 =="
"$VENV/bin/python" -c "import manim,edge_tts,numpy,scipy,glfw,OpenGL; import live2d.v3; print('依赖 OK')"
command -v ffmpeg >/dev/null && echo "ffmpeg OK" || echo "⚠️ 未装 ffmpeg: brew install ffmpeg"
ls /System/Library/Fonts/PingFang.ttc >/dev/null 2>&1 && echo "PingFang 中文字体 OK"
# ★ MathTex 场景需要 latex。非交互 shell 常不带 TeX 的 PATH, 渲染前务必 export。
if [ -x /Library/TeX/texbin/latex ]; then
  echo "latex OK (MacTeX) —— 渲染前请 export PATH=\"/Library/TeX/texbin:\$PATH\""
elif command -v latex >/dev/null; then
  echo "latex OK ($(command -v latex))"
else
  echo "⚠️ 没找到 latex! 用 MathTex 的场景会静默失败。装 MacTeX/BasicTeX: brew install --cask basictex"
fi
echo "完成。用 $VENV/bin/python 跑所有渲染; 记得 export TeX 的 PATH。"
