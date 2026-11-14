# -*- coding: utf-8 -*-
"""把视频素材导入 AdFlow 素材库，并抽关键帧给 Claude 看图打标签。

用法:
    python import_materials.py --dir "D:\\我的素材"   导入指定文件夹
    python import_materials.py                        导入 engine/materials 里还没入库的
    python import_materials.py --retag                重抽所有素材的关键帧（补打标签用）

导入后会:
1. 视频拷进 engine/materials/（已在里面就不拷），MD5 去重
2. 用 ffprobe 探测时长/分辨率，写入素材数据库
3. 每条素材均匀抽 4 张关键帧到 engine/data/keyframes/<素材ID>/
4. 生成 engine/data/keyframes/manifest.json —— 把它给 Claude，
   Claude 看图写好 data/keyframes/tags.json 后跑 apply_tags.py
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys

sys.stdout.reconfigure(errors="replace")

SKILL_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENGINE = os.path.join(SKILL_ROOT, "engine")
sys.path.insert(0, ENGINE)

VIDEO_EXT = (".mp4", ".mov", ".avi", ".mkv", ".webm", ".m4v", ".flv")
N_FRAMES = 4
FRAME_WIDTH = 640


def compute_md5(path):
    h = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def probe(ffprobe, path):
    """ffprobe 探测时长/宽高/帧率，失败返回 None"""
    cmd = [ffprobe, "-v", "error", "-print_format", "json",
           "-show_streams", "-show_format", path]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True,
                             encoding="utf-8", errors="replace",
                             timeout=60)
        info = json.loads(out.stdout)
    except Exception:
        return None
    v = None
    for s in info.get("streams", []):
        if s.get("codec_type") == "video":
            v = s
            break
    if not v:
        return None
    try:
        duration = float(info.get("format", {}).get("duration", 0) or 0)
    except ValueError:
        duration = 0
    return {
        "duration_ms": int(duration * 1000),
        "width": int(v.get("width", 0) or 0),
        "height": int(v.get("height", 0) or 0),
        "fps": _parse_fps(v.get("avg_frame_rate", "30/1")),
    }


def _parse_fps(rate):
    try:
        num, _, den = rate.partition("/")
        den = float(den or 1)
        return float(num) / den if den else 30.0
    except (ValueError, ZeroDivisionError):
        return 30.0


def extract_frames(ffmpeg, video, mid, duration_ms):
    """均匀抽 N_FRAMES 帧到 data/keyframes/<mid>/，返回帧文件列表"""
    out_dir = os.path.join(ENGINE, "data", "keyframes", mid)
    os.makedirs(out_dir, exist_ok=True)
    frames = []
    dur = max(duration_ms, 1) / 1000.0
    for i in range(1, N_FRAMES + 1):
        t = dur * i / (N_FRAMES + 1)
        out = os.path.join(out_dir, "f%d.jpg" % i)
        cmd = [ffmpeg, "-ss", "%.2f" % t, "-i", video,
               "-frames:v", "1", "-vf", "scale=%d:-2" % FRAME_WIDTH,
               "-q:v", "3", "-y", out]
        try:
            subprocess.run(cmd, capture_output=True, timeout=60)
        except subprocess.TimeoutExpired:
            pass
        if os.path.isfile(out):
            frames.append(os.path.abspath(out))
    return frames


def main():
    ap = argparse.ArgumentParser(description="导入视频素材并抽关键帧")
    ap.add_argument("--dir", default="", help="素材所在文件夹（默认扫 engine/materials）")
    ap.add_argument("--retag", action="store_true",
                    help="重抽所有素材关键帧（补打标签用）")
    args = ap.parse_args()

    # 引擎依赖在动作阶段才导入，报错能落到大白话
    try:
        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd, get_ffprobe_cmd
        from adflow.db.material_repo import MaterialRepo
        from adflow.models import MaterialRecord
        from adflow.config_loader import config
    except Exception as e:
        print("[X] 引擎依赖没装好（%s）" % e)
        print("先跑: python setup_env.py --deps ，再跑 python check_env.py 复查")
        sys.exit(1)

    ffmpeg = get_ffmpeg_cmd()
    ffprobe = get_ffprobe_cmd()
    if not shutil.which(ffmpeg) and not os.path.isfile(ffmpeg):
        print("[X] 没找到 ffmpeg，先跑: python setup_env.py --ffmpeg")
        sys.exit(1)

    repo = MaterialRepo()
    materials_dir = config.materials_dir
    os.makedirs(materials_dir, exist_ok=True)
    keyframes_root = os.path.join(ENGINE, "data", "keyframes")
    os.makedirs(keyframes_root, exist_ok=True)

    # ── 收集要处理的视频 ──
    if args.retag:
        rows = repo.get_all(limit=0)
        todo = [(m.material_id, m.file_path, m.duration_ms, True) for m in rows]
        if not todo:
            print("素材库是空的，先正常导入一次: python import_materials.py --dir 素材文件夹")
            sys.exit(0)
    else:
        src_dir = args.dir or materials_dir
        if not os.path.isdir(src_dir):
            print("[X] 文件夹不存在: %s" % src_dir)
            sys.exit(1)
        files = []
        for root, dirs, names in os.walk(src_dir):
            dirs[:] = [d for d in dirs if d not in ("_frames", "keyframes")]
            for n in sorted(names):
                if n.lower().endswith(VIDEO_EXT) and not n.startswith("."):
                    files.append(os.path.join(root, n))
        if not files:
            print("文件夹里没有视频文件（支持 %s）" % "/".join(VIDEO_EXT))
            sys.exit(0)

        todo = []
        skipped = 0
        for f in files:
            print("处理: " + os.path.basename(f))
            md5 = compute_md5(f)
            if repo.get_by_md5(md5):
                skipped += 1
                continue
            # 拷进素材库（本来就在 materials/ 里就不拷）
            dest = os.path.join(materials_dir, os.path.basename(f))
            if os.path.abspath(f) != os.path.abspath(dest):
                base, ext = os.path.splitext(dest)
                i = 1
                while os.path.exists(dest):
                    dest = "%s_%d%s" % (base, i, ext)
                    i += 1
                shutil.copy2(f, dest)
            else:
                dest = f
            meta = probe(ffprobe, dest)
            if not meta:
                print("  [跳过] 读不出视频信息（文件可能损坏）")
                continue
            rec = MaterialRecord(
                file_path=os.path.abspath(dest),
                original_filename=os.path.basename(f),
                duration_ms=meta["duration_ms"],
                fps=meta["fps"],
                width=meta["width"],
                height=meta["height"],
                file_size_bytes=os.path.getsize(dest),
                md5_hash=md5,
                # 宽高推方向：与引擎匹配逻辑同口径（h>=w = 竖屏）
                orientation="vertical" if meta["height"] >= meta["width"]
                else "landscape",
            )
            mid = repo.insert(rec)
            todo.append((mid, rec.file_path, meta["duration_ms"], False))
        if skipped:
            print("（%d 个重复视频自动跳过）" % skipped)

    # ── 抽关键帧 ──
    print("\n抽关键帧（每条 %d 张）..." % N_FRAMES)
    manifest = []
    for mid, path, dur_ms, _ in todo:
        frames = extract_frames(ffmpeg, path, mid, dur_ms)
        if not frames:
            print("  [注意] %s 没抽出帧，跳过打标" % os.path.basename(path))
            continue
        manifest.append({
            "material_id": mid,
            "file": os.path.basename(path),
            "duration_ms": dur_ms,
            "keyframes": frames,
        })
        print("  %s -> %d 帧" % (os.path.basename(path), len(frames)))

    out_path = os.path.join(keyframes_root, "manifest.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, ensure_ascii=False, indent=2)

    print("\n[OK] 完成。清单已写入:\n  " + out_path)
    print("下一步: 让 Claude 看 keyframes 里的图打标签，"
          "写好 tags.json 后跑 python apply_tags.py")


if __name__ == "__main__":
    main()
