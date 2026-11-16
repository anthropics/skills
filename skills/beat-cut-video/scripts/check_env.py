# -*- coding: utf-8 -*-
"""AdFlow skill 环境体检 — 零依赖，什么都没装也能跑。

检查：Python 版本 / 引擎文件 / ffmpeg / Python 依赖 / 配音配置 / 素材库
输出大白话清单，退出码 0=全好，1=有问题（按提示修完再跑一次）。

用法：python check_env.py
"""
import os
import sys

sys.stdout.reconfigure(errors="replace")

SKILL_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENGINE = os.path.join(SKILL_ROOT, "engine")

problems = []


def ok(msg):
    print("[OK] " + msg)


def bad(msg, fix):
    print("[X]  " + msg)
    print("     怎么修: " + fix)
    problems.append(msg)


# ── 1. Python 版本 ──
print("=" * 46)
print("AdFlow 环境体检")
print("=" * 46)
v = sys.version_info
if v >= (3, 10):
    ok("Python %d.%d.%d" % (v.major, v.minor, v.micro))
else:
    bad("Python 版本太低（%d.%d），要 3.10 以上" % (v.major, v.minor),
        "到 python.org 下载 Python 3.10~3.12 安装，安装时勾选 Add to PATH，"
        "详见 references/beginner-guide.md")

# ── 2. 引擎文件 ──
if os.path.isfile(os.path.join(ENGINE, "adflow", "agents", "pipeline.py")) \
        and os.path.isfile(os.path.join(ENGINE, "config.yaml")):
    ok("引擎文件齐全: " + ENGINE)
else:
    bad("找不到引擎文件（engine 文件夹不完整）",
        "确认 skill 包已完整解压，engine 文件夹和 scripts 文件夹在同一层")


# ── 3. ffmpeg ──
def _find_ffmpeg():
    """PATH → engine/ffmpeg/*/bin，返回可执行文件路径或空串"""
    from shutil import which
    found = which("ffmpeg")
    if found:
        return found
    ff_root = os.path.join(ENGINE, "ffmpeg")
    if os.path.isdir(ff_root):
        for sub in os.listdir(ff_root):
            bin_dir = os.path.join(ff_root, sub, "bin")
            exe = os.path.join(bin_dir, "ffmpeg.exe")
            if os.path.isfile(exe):
                return exe
            exe = os.path.join(bin_dir, "ffmpeg")
            if os.path.isfile(exe):
                return exe
    return ""


ffmpeg_path = _find_ffmpeg()
if ffmpeg_path:
    ok("ffmpeg 已就绪: " + ffmpeg_path)
else:
    bad("没找到 ffmpeg（剪辑必需）",
        "运行 python setup_env.py --ffmpeg 自动下载安装，"
        "或看 references/beginner-guide.md 手动装")

# ── 4. Python 依赖 ──
NEED = [
    ("yaml", "PyYAML"), ("ruamel.yaml", "ruamel.yaml"),
    ("moviepy", "moviepy"), ("librosa", "librosa"),
    ("openai", "openai"), ("dashscope", "dashscope"),
    ("edge_tts", "edge-tts"), ("dotenv", "python-dotenv"),
    ("numpy", "numpy"), ("cv2", "opencv-python"),
    ("PIL", "pillow"), ("requests", "requests"),
    ("PyQt6", "PyQt6(图形界面用，可不装)"),
]
missing = []
for mod, pkg in NEED:
    optional = "(" in pkg
    try:
        __import__(mod)
    except ImportError:
        if optional:
            print("[-]  可选依赖未装: " + pkg + "（不影响 Claude 出片，想开图形界面再装）")
        else:
            missing.append(pkg)
if not missing:
    ok("Python 依赖全部就绪")
elif missing:
    bad("缺少依赖: " + ", ".join(missing),
        "运行 python setup_env.py --deps 一键安装")

# ── 5. 配音配置 ──
try:
    with open(os.path.join(ENGINE, "config.yaml"), encoding="utf-8") as f:
        cfg_text = f.read()
except OSError:
    cfg_text = ""
backend = ""
for line in cfg_text.splitlines():
    s = line.strip()
    if s.startswith("backend:") and not backend:
        backend = s.split(":", 1)[1].strip()
        break

if backend == "edge":
    ok("配音方案: Edge-TTS（微软免费，无需任何 key）")
elif backend in ("volcano", "minimax"):
    # 检查 .env 里有没有配 key
    env_text = ""
    env_path = os.path.join(ENGINE, ".env")
    if os.path.isfile(env_path):
        with open(env_path, encoding="utf-8") as f:
            env_text = f.read()
    if backend == "volcano" and "VOLCANO_TTS_APP_ID" in env_text \
            and "VOLCANO_TTS_TOKEN" in env_text:
        ok("配音方案: 火山引擎（key 已配置）")
    elif backend == "minimax" and "MINIMAX_API_KEY" in env_text:
        ok("配音方案: MiniMax（key 已配置）")
    else:
        bad("配音方案是 %s 但还没配 key，出片会卡在配音" % backend,
            "按 references/tts-setup.md 配置 key，"
            "或把 engine/config.yaml 里 tts.backend 改回 edge（免费）")
else:
    bad("config.yaml 里没读到 tts.backend",
        "重新解压 skill 包，或把 tts.backend 设为 edge")

# ── 6. 素材库状态（只读提示，不算错）──
print("-" * 46)
try:
    import sqlite3
    db = os.path.join(ENGINE, "data", "adflow.db")
    if os.path.isfile(db):
        conn = sqlite3.connect(db)
        total = conn.execute("SELECT COUNT(*) FROM materials").fetchone()[0]
        tagged = conn.execute(
            "SELECT COUNT(*) FROM materials WHERE scene != ''").fetchone()[0]
        conn.close()
        print("素材库: 共 %d 条，已打标签 %d 条" % (total, tagged))
        if total == 0:
            print("      （还没素材 — 让 Claude 帮你导入视频素材后就能出片）")
        elif tagged < total:
            print("      （有 %d 条还没打标签，让 Claude 看图补上）" % (total - tagged))
    else:
        print("素材库: 还没建（首次导入素材时自动创建）")
except Exception as e:
    print("素材库: 状态读取失败（%s）— 不影响其他检查" % e)

n_bgm = 0
bgm_dir = os.path.join(ENGINE, "bgm_library")
if os.path.isdir(bgm_dir):
    n_bgm = len([f for f in os.listdir(bgm_dir)
                 if f.lower().endswith((".mp3", ".wav", ".m4a", ".flac"))])
print("背景音乐: %d 首（0 首也能出片，只是没有配乐）" % n_bgm)

print("-" * 46)
if problems:
    print("结论: 有 %d 个问题要修（看上面 [X] 行）" % len(problems))
    sys.exit(1)
print("结论: 环境全好，可以让 Claude 直接出片了")
sys.exit(0)
