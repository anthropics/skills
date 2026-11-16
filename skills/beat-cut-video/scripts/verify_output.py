# -*- coding: utf-8 -*-
"""卡点成片硬门禁 — 出片后必跑，全部通过才算完成。

用法:
    python verify_output.py 成片1.mp4 成片2.mp4
    python verify_output.py --dir engine/output
    python verify_output.py --dir engine/output --aspect landscape --latest 3

输出（stdout 标记块，直接解析，别从散文里猜）:
    ===VERIFY_START===
    FILE=<成片绝对路径>
    SIZE_MB=12.3
    DURATION_S=28.4
    RESOLUTION=1080x1920
    ORIENTATION=portrait
    AUDIO_DB=-18.2
    FRAME_YAVG=112.5
    PASS=0|1
    FAIL_REASONS=原因1;原因2   (PASS=1 时无此行)
    ===VERIFY_END===
    VERIFY_PASS=通过数/总数

体检项（全过才 PASS）:
    文件存在且非空 | 时长 >= 5 秒 | 方向符合竖屏/横屏且短边 >= 600 |
    有音轨且响度 > -45dB（防无声片）| 抽帧亮度 YAVG >= 20（防黑片：纯黑在 yuv420p 下 YAVG=16）

退出码:
    0    全部通过
    1    有成片没过（按 FAIL_REASONS 改，不能说完成）
    2    用法/环境错误（没给文件、找不到 ffmpeg）
"""
import argparse
import glob
import os
import re
import subprocess
import sys

sys.stdout.reconfigure(errors="replace")

SKILL_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENGINE = os.path.join(SKILL_ROOT, "engine")
sys.path.insert(0, ENGINE)


def _run(cmd, timeout=60):
    """跑 ffmpeg/ffprobe，返回 (returncode, stdout+stderr 合并文本)。"""
    try:
        r = subprocess.run(
            cmd, capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=timeout)
        return r.returncode, (r.stdout or "") + (r.stderr or "")
    except subprocess.TimeoutExpired:
        return 124, "命令超时"
    except Exception as e:
        return 125, str(e)


def verify_one(path, expect_orientation="portrait",
               min_duration=5.0, min_short_side=600):
    """体检单个成片，返回结果 dict（含 PASS 与 FAIL_REASONS）。"""
    info = {
        "FILE": os.path.abspath(path),
        "PASS": 0,
        "FAIL_REASONS": [],
    }
    fails = info["FAIL_REASONS"]

    if not os.path.isfile(path):
        fails.append("文件不存在")
        return info
    size_mb = os.path.getsize(path) / (1024 * 1024)
    info["SIZE_MB"] = round(size_mb, 1)
    if size_mb <= 0:
        fails.append("文件是空的")
        return info

    from adflow.utils.ffmpeg_finder import find_ffmpeg, find_ffprobe
    ffprobe = find_ffprobe()
    ffmpeg = find_ffmpeg()
    if not ffprobe or not ffmpeg:
        fails.append("环境缺 ffmpeg/ffprobe（先跑 setup_env.py --ffmpeg）")
        return info

    # ── 探测: 时长 / 分辨率 / 音轨 ──
    code, out = _run([ffprobe, "-v", "error", "-print_format", "json",
                      "-show_format", "-show_streams", path])
    if code != 0:
        reason = "ffprobe 探测失败"
        if out.strip():
            reason += ": " + out.strip().splitlines()[0][:80]
        fails.append(reason)
        return info
    import json
    try:
        probe = json.loads(out)
    except ValueError:
        fails.append("ffprobe 输出不是合法 JSON")
        return info

    duration = float(probe.get("format", {}).get("duration", 0) or 0)
    info["DURATION_S"] = round(duration, 1)
    if duration < min_duration:
        fails.append(f"时长{duration:.1f}s 不足{min_duration:.0f}s")

    v_w = v_h = 0
    has_audio = False
    for st in probe.get("streams", []):
        if st.get("codec_type") == "video" and not v_w:
            v_w = int(st.get("width", 0) or 0)
            v_h = int(st.get("height", 0) or 0)
        elif st.get("codec_type") == "audio":
            has_audio = True
    if not v_w or not v_h:
        fails.append("没有视频轨")
        return info
    info["RESOLUTION"] = f"{v_w}x{v_h}"
    orientation = "portrait" if v_h > v_w else ("landscape" if v_w > v_h else "square")
    info["ORIENTATION"] = orientation
    if expect_orientation != "any":
        if orientation != expect_orientation:
            fails.append(f"方向是{orientation}，期望{expect_orientation}")
    if min(v_w, v_h) < min_short_side:
        fails.append(f"短边{min(v_w, v_h)}低于{min_short_side}（渲染出了低清片）")

    # ── 响度: 防 BGM 丢失出无声片 ──
    if has_audio:
        code, out = _run([ffmpeg, "-i", path, "-vn", "-af",
                          "volumedetect", "-f", "null", "-"], timeout=120)
        m = re.findall(r"mean_volume:\s*(-?[\d.]+)\s*dB", out)
        if code != 0 or not m:
            fails.append("音频探测失败（音轨可能损坏）")
        else:
            db = float(m[-1])
            info["AUDIO_DB"] = db
            if db <= -45:
                fails.append(f"音频是哑的({db}dB，疑似 BGM 丢失)")
    else:
        fails.append("没有音轨（音轨丢了）")

    # ── 画面: 抽 1 秒处一帧防全黑 ──
    probe_at = min(1.0, max(0.0, duration / 2))
    code, out = _run([ffmpeg, "-ss", f"{probe_at:.2f}", "-i", path,
                      "-frames:v", "1", "-vf", "signalstats,metadata=print",
                      "-f", "null", "-"], timeout=60)
    m = re.findall(r"YAVG=([\d.]+)", out)
    if code != 0 or not m:
        fails.append("抽帧失败（画面流可能损坏）")
    else:
        yavg = float(m[-1])
        info["FRAME_YAVG"] = yavg
        if yavg < 20:
            fails.append(f"抽帧是黑的(YAVG={yavg}，疑似黑屏片)")

    info["PASS"] = 0 if fails else 1
    return info


def verify_and_report(paths, expect_orientation="portrait",
                      min_duration=5.0, min_short_side=600):
    """体检一批成片并打印标记块，返回 (是否全过, 结果列表)。"""
    results = [verify_one(p, expect_orientation, min_duration, min_short_side)
               for p in paths]
    print("===VERIFY_START===")
    for r in results:
        for key, val in r.items():
            if key == "FAIL_REASONS":
                continue
            if key == "PASS" or val != "":
                print(f"{key}={val}")
        if not r["PASS"]:
            print("FAIL_REASONS=" + ";".join(r["FAIL_REASONS"]))
    print("===VERIFY_END===")
    n_pass = sum(1 for r in results if r["PASS"])
    print(f"VERIFY_PASS={n_pass}/{len(results)}")
    return n_pass == len(results) and len(results) > 0, results


def main():
    ap = argparse.ArgumentParser(description="AdFlow 成片硬门禁")
    ap.add_argument("files", nargs="*", help="成片文件路径")
    ap.add_argument("--dir", default="", help="扫这个目录下的 .mp4")
    ap.add_argument("--latest", type=int, default=0,
                    help="配合 --dir 只体检最新的 N 条（0=全部）")
    ap.add_argument("--aspect", default="portrait",
                    choices=["portrait", "landscape", "any"],
                    help="期望方向（默认竖屏）")
    ap.add_argument("--min-duration", type=float, default=5.0)
    ap.add_argument("--min-short-side", type=int, default=600)
    args = ap.parse_args()

    paths = list(args.files)
    if args.dir:
        if not os.path.isdir(args.dir):
            print("[X] 目录不存在: %s" % args.dir)
            sys.exit(2)
        found = glob.glob(os.path.join(args.dir, "*.mp4"))
        found.sort(key=os.path.getmtime, reverse=True)
        if args.latest > 0:
            found = found[:args.latest]
        paths.extend(found)
    paths = [p for p in paths if p]
    if not paths:
        print("[X] 没给文件：传成片路径，或用 --dir engine/output")
        sys.exit(2)

    ok, _ = verify_and_report(
        paths, expect_orientation=args.aspect,
        min_duration=args.min_duration,
        min_short_side=args.min_short_side)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
