#!/usr/bin/env python3
"""
通用合成脚本: 把分场景拼成底片(交叉转场 + 配音 + BGM)。只用标准库, 可用系统 python3 跑。
读 pipeline_config 的 SCENES / XFADE / OUTPUT_BASENAME。

流程: 1) manim 渲染分场景  2) narrate.py 配音  3) build_video.py 合成
用法:
    python3 build_video.py 1080p60                 # 配音 + 占位音乐
    python3 build_video.py 1080p60 bgm.wav         # 配音 + 自己的 BGM
    python3 build_video.py 1080p60 --no-music      # 只配音
"""
import os
import subprocess
import sys
from pathlib import Path

import pipeline_config as cfg

ROOT = Path(__file__).parent
VO_DIR = ROOT / "media" / "vo"
SCENES = cfg.SCENES
XFADE = cfg.XFADE
ENC = cfg.ENCODE_PREVIEW if os.environ.get("MC_FAST") else cfg.ENCODE_FINAL  # 预览快档/成片高质量


def probe(path):
    return float(subprocess.check_output(
        ["ffprobe", "-v", "error", "-show_entries", "format=duration",
         "-of", "csv=p=0", str(path)]).strip())


def make_music_bed(duration, out_path):
    """占位环境音(没传 BGM 时用)。"""
    freqs = [110.0, 164.81, 220.0, 277.18]
    inputs = []
    for f in freqs:
        inputs += ["-f", "lavfi", "-i", f"sine=frequency={f}:sample_rate=44100"]
    fo = max(0.1, duration - 3.0)
    af = ("[0][1][2][3]amix=inputs=4:normalize=1,tremolo=f=0.1:d=0.6,"
          "lowpass=f=700,aecho=0.8:0.6:120:0.35,"
          f"volume=-20dB,afade=t=in:d=3,afade=t=out:st={fo:.2f}:d=3")
    subprocess.run(["ffmpeg", "-y", "-loglevel", "error", *inputs,
                    "-filter_complex", af, "-t", f"{duration:.2f}", str(out_path)], check=True)


def build(quality, music_arg):
    clip_dir = ROOT / "media" / "videos" / "scenes" / quality
    clips = [clip_dir / f"{s}.mp4" for s in SCENES]
    missing = [c.name for c in clips if not c.exists()]
    if missing:
        sys.exit(f"缺少片段(先 manim 渲染): {missing}\n目录: {clip_dir}")

    durs = [probe(c) for c in clips]
    starts, acc = [], 0.0
    for d in durs:
        starts.append(acc); acc += d - XFADE
    final_dur = sum(durs) - XFADE * (len(clips) - 1)
    print(f"[{quality}] 片段: " + ", ".join(f"{d:.1f}" for d in durs))
    print(f"转场后总时长 {final_dur:.1f}s ({final_dur/60:.2f} 分钟)")

    inputs = []
    for c in clips:
        inputs += ["-i", str(c)]

    # 视频 xfade 链
    filters, prev, offset = [], "[0:v]", 0.0
    for i in range(1, len(clips)):
        offset += durs[i - 1] - XFADE
        out = f"[v{i}]" if i < len(clips) - 1 else "[vout]"
        filters.append(f"{prev}[{i}:v]xfade=transition=fade:duration={XFADE}:"
                       f"offset={offset:.3f}{out}")
        prev = out

    # 配音轨: 各段放到场景起点
    vo_labels, idx = [], len(clips)
    for i in range(len(clips)):
        f = VO_DIR / f"scene{i}.mp3"
        if not f.exists():
            continue
        inputs += ["-i", str(f)]
        filters.append(f"[{idx}:a]adelay={int(starts[i]*1000)}:all=1[vo{i}]")
        vo_labels.append(f"[vo{i}]"); idx += 1
    n_vo = len(vo_labels)
    print(f"配音: {n_vo}/{len(clips)} 段" if n_vo else "⚠️ 无配音(先跑 narrate.py)")

    # BGM
    tmp_bed = ROOT / "_music_bed.wav"
    music_path = None
    if music_arg == "--no-music":
        pass
    elif music_arg:
        music_path = Path(music_arg)
        if not music_path.exists():
            sys.exit(f"找不到音乐: {music_path}")
    else:
        print("未提供 BGM → 合成占位环境音"); make_music_bed(final_dur, tmp_bed); music_path = tmp_bed

    music_label = None
    if music_path:
        inputs += ["-stream_loop", "-1", "-i", str(music_path)]
        vol = "-26dB" if n_vo else "-18dB"
        filters.append(f"[{idx}:a]volume={vol},afade=t=in:d=2,"
                       f"afade=t=out:st={final_dur-3:.2f}:d=3,atrim=0:{final_dur:.3f}[mus]")
        music_label = "[mus]"; idx += 1

    audio = vo_labels + ([music_label] if music_label else [])
    if audio:
        if len(audio) == 1:
            filters.append(f"{audio[0]}alimiter=limit=0.95,atrim=0:{final_dur:.3f}[aout]")
        else:
            filters.append("".join(audio) +
                           f"amix=inputs={len(audio)}:normalize=0:dropout_transition=0,"
                           f"alimiter=limit=0.95,atrim=0:{final_dur:.3f}[aout]")

    suffix = "1080p60" if quality.startswith("1080") else quality
    out_path = ROOT / f"{cfg.OUTPUT_BASENAME}_{suffix}.mp4"
    cmd = ["ffmpeg", "-y", "-loglevel", "error", *inputs,
           "-filter_complex", ";".join(filters), "-map", "[vout]"]
    if audio:
        cmd += ["-map", "[aout]", "-c:a", "aac", "-b:a", "192k"]
    cmd += [*ENC, str(out_path)]

    print("合成中(ffmpeg)…")
    subprocess.run(cmd, check=True)
    if tmp_bed.exists():
        tmp_bed.unlink()
    print(f"✅ 成片: {out_path}  ({probe(out_path):.1f}s)")


if __name__ == "__main__":
    quality = sys.argv[1] if len(sys.argv) > 1 else cfg.QUALITY
    music_arg = sys.argv[2] if len(sys.argv) > 2 else None
    build(quality, music_arg)
