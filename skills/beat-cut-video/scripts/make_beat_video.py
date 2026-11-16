# -*- coding: utf-8 -*-
"""BGM 卡点/快闪无头出片 — BGM 进，踩点成片出（不经图形界面，不调任何大模型 API）。

和文案出片（make_videos.py）相反：这里 BGM 是主时钟，
切点全部落在 librosa 检出的真实鼓点上，配音没有、纯节奏。

用法示例:
    python make_beat_video.py --bgm "C:\\music\\卡点.mp3"
    python make_beat_video.py --bgm bgm.mp3 --style standard --duration 15
    python make_beat_video.py --bgm bgm.mp3 --style flash --words "夏天 旅行 自由"

常用参数:
    --bgm         BGM 文件（必填，必须是本人有授权的音乐）
    --style       flash 快闪每拍一刀 / standard 卡点两拍一刀 / build 前缓后炸（默认 flash）
    --duration    成片秒数（0=整首，自动截到 60 秒封顶）
    --words       大字快闪词，空格/逗号分隔（不给就不加字）
    --count       出几条（默认 1，素材顺序和窗口不同）
    --aspect      portrait 竖屏（默认）/ landscape 横屏
    --prefix      文件名前缀
    --bgm-volume  BGM 音量 0~1（默认 0.9，BGM 是主角）
    --reverse     倒放镜头占比 0~1（默认 0.15，0=不倒放）
    --seed        随机种子（默认 0，同种子同素材库 = 可复现）
    --force       已出的成品也全部重出（默认同参数重跑会跳过已出的条目只补缺）

断点续跑:
    同参数重跑（同 BGM/风格/词/种子…）时，已出且切点表签名一致的条目直接跳过，
    只补缺的和失败的；改了参数（或 config 里的效果预设）想全部重出加 --force。
    素材预处理（归一化到目标分辨率）缓存在 engine/cache/normalize/，跨次出片复用，
    删掉整个目录会自动重建。

退出码:
    0    出片 + 成片体检全过
    1    全部失败 / 环境错误（看日志排查）
    2    出了但有条目失败或没过体检（看 FAILED_STAGE / FAIL_REASONS，不能算完成）
    130  手动停止
"""
import argparse
import glob
import json
import os
import random
import re
import subprocess
import sys
import time
import traceback

sys.stdout.reconfigure(errors="replace")

SKILL_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENGINE = os.path.join(SKILL_ROOT, "engine")
sys.path.insert(0, ENGINE)

# 效果预设兜底值（正式调参面在 engine/config.yaml 的 beat_cut.style_presets）
_DEFAULT_PRESET = {"punch": 0.15, "flash": "white", "mirror_every": 3, "calm_zoom": 0.0}
_FLASH_COLORS = {"white": (255, 255, 255), "black": (0, 0, 0)}


def parse_words(raw: str) -> list:
    words = [w for w in re.split(r"[\s,，、/]+", raw or "") if w]
    return words


def main():
    ap = argparse.ArgumentParser(description="BGM 卡点/快闪无头出片")
    ap.add_argument("--bgm", default="", help="BGM 文件路径（必填）")
    ap.add_argument("--style", default="flash",
                    choices=["flash", "standard", "build"])
    ap.add_argument("--duration", type=float, default=0.0,
                    help="成片秒数，0=整首（60 秒封顶）")
    ap.add_argument("--words", default="", help="大字快闪词，空格/逗号分隔")
    ap.add_argument("--count", type=int, default=1)
    ap.add_argument("--aspect", default="portrait",
                    choices=["portrait", "landscape"])
    ap.add_argument("--prefix", default="")
    ap.add_argument("--bgm-volume", type=float, default=0.0,
                    help="BGM 音量 0~1，0=用 config 默认")
    ap.add_argument("--reverse", type=float, default=-1.0,
                    help="倒放镜头占比 0~1，负数=用 config 默认")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--force", action="store_true",
                    help="已出的成品也全部重出（默认跳过参数一致的已出条目）")
    args = ap.parse_args()

    if not args.bgm or not os.path.isfile(args.bgm):
        print("[X] 没给 BGM 或文件不存在: %r — 卡点出片必须有 BGM" % args.bgm)
        sys.exit(1)

    try:
        from adflow.config_loader import config
        from adflow.db.material_repo import MaterialRepo
        from adflow.engine.beat_cutter import extract_beat_map, plan_cuts
        from adflow.engine.shot_picker import WINDOW_SEC, build_motion_index, pick_window
        from adflow.engine import beat_effects as fx
        from adflow.engine.editor import VideoEditor
        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
        from adflow.utils.font_resolver import resolve_subtitle_font
    except Exception as e:
        print("[X] 引擎依赖没装好（%s）" % e)
        print("先跑: python setup_env.py --all ，再 python check_env.py 复查")
        sys.exit(1)

    words = parse_words(args.words)
    if words and len(words) > 24:
        print("[X] 快闪词最多 24 个（现在 %d 个），挑重点" % len(words))
        sys.exit(1)

    # ── 1. BGM 节拍（主时钟）──
    print("提取节拍: %s" % os.path.basename(args.bgm))
    try:
        beat_map = extract_beat_map(args.bgm)
    except Exception as e:
        print("[X] 节拍提取失败: %s" % e)
        sys.exit(1)

    max_duration = float(config.get("beat_cut.max_duration", 60))
    target = args.duration if args.duration > 0 else beat_map.duration
    if target > max_duration:
        print("成片时长 %.0fs 截到 %.0fs 封顶" % (target, max_duration))
        target = max_duration

    plan = plan_cuts(beat_map, args.style, target)
    print("BPM %.0f | %s 风格 | %.1f 秒 | %d 个镜头%s" % (
        plan.bpm, plan.style, plan.duration, plan.shot_count,
        (" | 高潮段 %.1fs 起" % plan.high_energy_start)
        if plan.high_energy_start else ""))
    if plan.shot_count > len(words or []) * 8 and words:
        print("提示: 词只有 %d 个，要循环 %d 轮，多给几个词效果更好" % (
            len(words), plan.shot_count // max(len(words), 1)))

    # ── 2. 素材库 ──
    records = [r for r in MaterialRepo().get_all(limit=500)
               if r.file_path and os.path.exists(r.file_path)
               and r.duration_ms >= 1500]
    if not records:
        print("[X] 素材库是空的（或都短于 1.5 秒），没法剪片")
        print("先跑: python import_materials.py --dir \"你的视频素材文件夹\"")
        sys.exit(1)
    if len(records) < 3:
        print("提醒: 素材只有 %d 条，快闪循环快，重复感会强" % len(records))

    # ── 3. 出片 ──
    preset = dict(_DEFAULT_PRESET)
    preset.update(config.get("beat_cut.style_presets.%s" % args.style, {}) or {})
    bgm_volume = args.bgm_volume if args.bgm_volume > 0 else float(
        config.get("beat_cut.bgm_volume", 0.9))
    word_cfg = config.get("beat_cut.word", {}) or {}
    motion_pick = bool(config.get("beat_cut.motion_pick", True))
    reverse_ratio = (args.reverse if args.reverse >= 0
                     else float(config.get("beat_cut.reverse_ratio", 0.15)))
    shake_every = int(config.get("beat_cut.shake_every", 4))
    font_path = resolve_subtitle_font(config.get("editing.subtitle.font", ""))
    width, height = (1920, 1080) if args.aspect == "landscape" else (1080, 1920)

    from moviepy import AudioFileClip, VideoFileClip, CompositeVideoClip, concatenate_videoclips

    tmp_dir = os.path.join(config.output_dir, "_temp")
    os.makedirs(tmp_dir, exist_ok=True)
    # 归一化缓存持久化：跨次出片复用，不再每次重编码同批素材。
    # 键含分辨率，横竖屏不会串包；原子转正保证不留半截文件
    norm_cache_dir = os.path.join(ENGINE, "cache", "normalize")
    os.makedirs(norm_cache_dir, exist_ok=True)
    _now = time.time()
    for _f in glob.glob(os.path.join(norm_cache_dir, "*.part.mp4")):
        try:
            if _now - os.path.getmtime(_f) > 600:  # 10 分钟前的 .part 肯定是死进程留的
                os.remove(_f)
        except OSError:
            pass
    open_clips = []          # 退出前关
    outputs = []
    skipped = []
    failures = []            # [(第几条, 挂在哪阶段, 错误)]

    def normalize_source(path: str) -> str:
        """统一缩放裁剪到目标分辨率（结果进持久缓存，多镜头多条成片复用；ffmpeg 自动回正旋转）。
        -g 30 加密关键帧：倒放镜头要逐帧往回跳着解码，关键帧太稀（默认 250）倒放会慢得离谱"""
        import zlib
        # 键含大小+mtime：同路径换了文件（重新导过素材）不会吃到旧缓存
        ident = "%s|%d|%d" % (os.path.abspath(path),
                              os.path.getsize(path),
                              int(os.path.getmtime(path)))
        tag = zlib.crc32(ident.encode("utf-8")) % 10**8
        out = os.path.join(norm_cache_dir, "norm_%d_%dx%d.mp4" % (
            tag, width, height))
        if os.path.exists(out) and os.path.getsize(out) > 0:
            return out
        part = out + ".part.mp4"
        vf = ("scale=%d:%d:force_original_aspect_ratio=increase,crop=%d:%d"
              % (width, height, width, height))
        result = subprocess.run(
            [get_ffmpeg_cmd(), "-y", "-i", path, "-vf", vf, "-an",
             "-c:v", "libx264", "-preset", "veryfast", "-crf", "18",
             "-pix_fmt", "yuv420p", "-g", "30", part],
            capture_output=True, timeout=300)
        if result.returncode != 0 or not os.path.exists(part):
            raise RuntimeError("素材预处理失败 %s: %s" % (
                os.path.basename(path), result.stderr.decode(errors="replace")[-200:]))
        os.replace(part, out)  # 原子落名：中断的半截文件不会被下轮误用
        return out

    def run_signature(n: int) -> str:
        """第 n 条成片的参数指纹（写进 cuts.json 的 sig）：重跑同命令时识别「这条已出过」。
        只含 CLI 参数 + BGM 身份；改了 config 里的效果预设想要全部重出，用 --force"""
        import hashlib
        bgm_id = "%s|%d|%d" % (os.path.abspath(args.bgm),
                               os.path.getsize(args.bgm),
                               int(os.path.getmtime(args.bgm)))
        raw = "|".join(["v1", bgm_id, plan.style, "%.2f" % plan.duration,
                        args.aspect, " ".join(words),
                        "%.2f" % reverse_ratio, "%.2f" % bgm_volume,
                        str(args.seed + n)])
        return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:16]

    def _cuts_sig(cuts_path: str):
        """读旧切点表里的签名；没有/读不了返回 None（老版表没有 sig，视为不匹配重出）"""
        try:
            with open(cuts_path, encoding="utf-8") as f:
                return json.load(f).get("sig")
        except (OSError, ValueError):
            return None

    try:
        norm_cache: dict = {}
        src_clips: dict = {}  # material_id -> VideoFileClip，整场只开一次
        # 出片素材池：只预处理实际会用到的条数（全库几百条都过一遍 ffmpeg 对
        # 15 秒快闪纯属浪费），最少保 12 条画面多样性
        pool = records[:max(plan.shot_count, 12)]
        loaded = []
        for mat in pool:
            key = mat.material_id
            try:
                if key not in norm_cache:
                    norm_cache[key] = normalize_source(mat.file_path)
                if key not in src_clips:
                    src_clips[key] = VideoFileClip(norm_cache[key])
                    open_clips.append(src_clips[key])
                loaded.append(mat)
            except Exception as e:
                # 单条素材坏（被挪走/损坏）不该废掉整场，跳过并继续
                print("[!] 素材加载失败，跳过 %s: %s" % (
                    os.path.basename(mat.file_path), str(e)[:100]))
        pool = loaded
        if not pool:
            raise RuntimeError("素材全部加载失败")
        motion_index = build_motion_index(src_clips) if motion_pick else {}
        if motion_pick:
            print("镜头优选: %d/%d 条素材完成运动打分%s" % (
                len(motion_index), len(src_clips),
                "" if len(motion_index) == len(src_clips) else "（其余退回顺序选）"))
        for n in range(max(1, args.count)):
            sig = run_signature(n)
            name = "beat_%s_%s%02d.mp4" % (
                plan.style, (args.prefix + "_") if args.prefix else "", n + 1)
            out_path = os.path.join(config.output_dir, name)
            cuts_path = os.path.splitext(out_path)[0] + ".cuts.json"
            # 断点续跑：同参数已出且成品还在 → 跳过这条只补缺的（结尾体检统一覆盖）
            if (not args.force and os.path.isfile(out_path)
                    and os.path.getsize(out_path) > 0
                    and _cuts_sig(cuts_path) == sig):
                print("跳过 %d/%d: %s 已出过且参数一致（全部重出加 --force）"
                      % (n + 1, args.count, name))
                outputs.append(out_path)
                skipped.append(out_path)
                continue

            rng = random.Random(args.seed + n)
            order = list(pool)
            rng.shuffle(order)
            cursor = {}   # 打分失败素材的顺序游标（"用到了第几秒"）
            used = set()  # 打分路线已用过的窗口，防同窗反复用
            accent_seen = 0  # 第几个重音刀（每 N 个换一次抖动）
            reverse_flags, shake_flags, shot_srcs = [], [], []
            shots = []
            stage = "拼镜头"
            try:
                for i in range(plan.shot_count):
                    shot_len = plan.cut_times[i + 1] - plan.cut_times[i]
                    mat = order[i % len(order)]
                    key = mat.material_id
                    src = src_clips[key]
                    src_dur = src.duration
                    # 选镜头：运动打分优选（重音刀配动得最狠的窗口，平稳刀配安静段），
                    # 这条素材打不了分就退回顺序游标
                    start = pick_window(motion_index, key, bool(plan.accent_flags[i]),
                                        rng, used)
                    if start is None:
                        if key not in cursor:
                            # 起点随机散开（不同条之间画面组合不同）
                            cursor[key] = rng.uniform(
                                0, max(mat.duration_ms / 1000.0 - 1.0, 0))
                        start = cursor[key]
                    else:
                        # 窗口内随机起，别每刀都从窗口头起
                        start += rng.uniform(0, max(WINDOW_SEC - shot_len, 0.0))
                    if start + shot_len > src_dur - 0.001:
                        start = 0.0
                    shot = src.subclipped(start, min(start + shot_len, src_dur))
                    # 倒放混切（回手镜头）；倒放先做，再算慢放补齐的速度
                    is_reversed = rng.random() < reverse_ratio
                    if is_reversed:
                        shot = fx.reverse_play(shot)
                    shot = fx.slow_to_fill(shot, shot_len)  # 素材短于镜头 → 慢放补齐

                    # 效果：重音刀 punch+闪（每 N 个换冲击抖动），普通刀缓推；隔几刀镜像换换味
                    if preset["mirror_every"] and i > 0 and i % int(preset["mirror_every"]) == 0:
                        shot = fx.mirror_flip(shot)
                    shook = False
                    if plan.accent_flags[i]:
                        accent_seen += 1
                        if shake_every and accent_seen % shake_every == 0:
                            shot = fx.shake(shot)
                            shook = True
                        else:
                            shot = fx.punch_zoom(shot, float(preset["punch"]))
                    elif float(preset["calm_zoom"]) > 0:
                        shot = fx.calm_zoom(shot, float(preset["calm_zoom"]))
                    reverse_flags.append(is_reversed)
                    shake_flags.append(shook)
                    shot_srcs.append(os.path.basename(mat.file_path))

                    layers = []
                    if plan.accent_flags[i] and preset["flash"] in _FLASH_COLORS:
                        layers.append(fx.flash_layer(
                            width, height, shot.duration,
                            color=_FLASH_COLORS[preset["flash"]]))
                    if words:
                        w = fx.word_pop(
                            words[i % len(words)], shot.duration, font_path,
                            font_size=int(word_cfg.get("font_size", 100)),
                            color=word_cfg.get("color", "white"),
                            stroke_color=word_cfg.get("stroke_color", "black"),
                            stroke_width=int(word_cfg.get("stroke_width", 5)))
                        if w is not None:
                            layers.append(w)
                    if layers:
                        shot = CompositeVideoClip([shot] + layers, size=(width, height))
                    shots.append(shot)
                    cursor[key] = start + shot_len + rng.uniform(0.1, 0.6)

                if not shots:
                    raise RuntimeError("一个镜头都没拼出来，素材全部加载失败")

                stage = "渲染"
                final = (shots[0] if len(shots) == 1
                         else concatenate_videoclips(shots, method="compose"))

                bgm = AudioFileClip(args.bgm).subclipped(0, plan.duration)
                final = final.with_audio(bgm.with_volume_scaled(bgm_volume))

                print("渲染 %d/%d: %s（%d 个镜头）..." % (
                    n + 1, args.count, name, plan.shot_count))

                # 导出参数与 editor.py 同源（bt709/faststart/48k），改那边同步这边
                final.write_videofile(
                    out_path,
                    fps=30, codec="libx264", audio_codec="aac",
                    preset="medium", bitrate=None, threads=4, logger=None,
                    ffmpeg_params=[
                        "-crf", "23", "-pix_fmt", "yuv420p",
                        "-movflags", "+faststart", "-g", "60",
                        "-profile:v", "high", "-level", "4.1",
                        "-colorspace", "bt709", "-color_primaries", "bt709",
                        "-color_trc", "bt709", "-ar", "48000",
                    ],
                )
                stage = "响度归一"
                VideoEditor._normalize_loudness(out_path)  # 响度归一到 -14 LUFS

                stage = "写切点表"
                with open(cuts_path, "w", encoding="utf-8") as f:
                    json.dump({
                        "style": plan.style, "bpm": plan.bpm,
                        "duration": plan.duration, "output": out_path,
                        "cut_times": plan.cut_times, "accent_flags": plan.accent_flags,
                        "reverse_flags": reverse_flags, "shake_flags": shake_flags,
                        "shot_srcs": shot_srcs,
                        "high_energy_start": plan.high_energy_start,
                        "words": words, "seed": args.seed + n,
                        "sig": sig, "aspect": args.aspect,
                    }, f, ensure_ascii=False, indent=2)

                # 子镜头/成片共享素材 reader，中途关会把下一条出片的源带塌，统一 finally 里关
                open_clips.append(final)
                open_clips.extend(shots)
                outputs.append(out_path)
                print("  已出: %s（倒放 %d 镜 / 抖动 %d 镜）" % (
                    out_path, sum(reverse_flags), sum(shake_flags)))
            except Exception as e:
                # 单条失败不废整批：记挂在哪阶段，清半截成品，继续下一条
                failures.append((n + 1, stage, str(e)[:160]))
                print("\n[X] 第 %d/%d 条失败（挂在: %s）: %s\n继续出下一条\n"
                      % (n + 1, args.count, stage, str(e)[:160]))
                traceback.print_exc()
                for dead in (out_path, cuts_path):
                    try:
                        os.remove(dead)
                    except OSError:
                        pass
                continue
    except KeyboardInterrupt:
        print("\n已手动停止")
        sys.exit(130)
    except Exception:
        print("\n[X] 出片失败，完整报错如下:\n")
        traceback.print_exc()
        print("\n常见原因:")
        print("  * 没找到 ffmpeg   -> python setup_env.py --ffmpeg")
        print("  * No module named xx -> python setup_env.py --deps")
        sys.exit(1)
    finally:
        for c in open_clips:
            try:
                c.close()
            except Exception:
                pass

    print("\n" + "=" * 46)
    print("卡点出片完成")
    print("=" * 46)
    # 成片清单标记块（机器可读）：OK 本次新出 / SKIP 断点续跑沿用 / FAIL 失败
    ok_set = {os.path.abspath(p) for p in outputs}
    skip_set = {os.path.abspath(p) for p in skipped}
    fail_by_idx = {idx: stage for idx, stage, _ in failures}
    print("===VIDEOS_START===")
    for n in range(max(1, args.count)):
        name = "beat_%s_%s%02d.mp4" % (
            plan.style, (args.prefix + "_") if args.prefix else "", n + 1)
        p = os.path.abspath(os.path.join(config.output_dir, name))
        if p in skip_set:
            print("FILE=%s" % p)
            print("STATUS=SKIP")
        elif p in ok_set:
            print("FILE=%s" % p)
            print("STATUS=OK")
        elif (n + 1) in fail_by_idx:
            print("FILE=%s" % p)
            print("STATUS=FAIL")
            print("FAILED_STAGE=%s" % fail_by_idx[n + 1])
    print("===VIDEOS_END===")
    print("成片文件夹: " + config.output_dir)
    if not outputs:
        print("[X] 一条都没出来 — 把上面的日志发给 Claude 排查")
        sys.exit(1)

    # ── 成片体检（硬门禁）：全过才算完成 ──
    import verify_output
    print("\n" + "=" * 46)
    print("成片体检（时长/画面/声音硬门禁）")
    print("=" * 46)
    all_ok, _ = verify_output.verify_and_report(
        outputs, expect_orientation=args.aspect)
    if failures or not all_ok:
        print("\n[X] 有条目失败或没过体检，这批不能算完成"
              + ("；跳过的旧条目没过的话，加 --force 重出" if skipped else ""))
        sys.exit(2)


if __name__ == "__main__":
    main()
