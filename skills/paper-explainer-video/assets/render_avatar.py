#!/usr/bin/env python3
"""
通用 Live2D 虚拟主播渲染 + 合成。读 pipeline_config 的 SCENES / AVATAR / L2D_MODEL。

- 口型: 由配音音量包络驱动 (ParamMouthOpenY) —— 真同步, 静音闭嘴
- 待机: 缓慢摇头/呼吸/眨眼 (确定性正弦, 不依赖动作计时器)
- 透明: 把角色原始 RGBA 帧**直接管道进 ffmpeg overlay**, 与 base_video.mp4 合成出成片
        (完美透明, 不落大中间文件, 省磁盘 —— 不要用 VP9(掉alpha)/qtrle(爆盘))

前置: 已有 base_video.mp4 (build_video 产出) 和 media/vo/sceneN.mp3。
用法: ~/llm_mc_venv/bin/python render_avatar.py
"""
import os
import subprocess
from pathlib import Path
import numpy as np

import pipeline_config as cfg

ENC = cfg.ENCODE_PREVIEW if os.environ.get("MC_FAST") else cfg.ENCODE_FINAL

ROOT = Path(__file__).parent
SCENES = cfg.SCENES
XFADE = cfg.XFADE
A = cfg.AVATAR
FPS = A["fps"]
W, H = A["W"], A["H"]
ENV_SR = 16000


def probe(path):
    return float(subprocess.check_output(
        ["ffprobe", "-v", "error", "-show_entries", "format=duration",
         "-of", "csv=p=0", str(path)]).strip())


def decode_mono(path, sr=ENV_SR):
    raw = subprocess.check_output(
        ["ffmpeg", "-v", "error", "-i", str(path), "-ac", "1",
         "-ar", str(sr), "-f", "f32le", "-"])
    return np.frombuffer(raw, dtype=np.float32)


def build_envelope(scenes_dir, vo_dir, total_dur, n_frames):
    durs = [probe(Path(scenes_dir) / f"{s}.mp4") for s in SCENES]
    starts, acc = [], 0.0
    for d in durs:
        starts.append(acc); acc += d - XFADE
    timeline = np.zeros(int(total_dur * ENV_SR) + ENV_SR, dtype=np.float32)
    for i in range(len(SCENES)):
        vo = Path(vo_dir) / f"scene{i}.mp3"
        if not vo.exists():
            continue
        sig = np.abs(decode_mono(vo))
        s = int(starts[i] * ENV_SR)
        timeline[s:s + len(sig)] = np.maximum(timeline[s:s + len(sig)], sig)
    hop = ENV_SR / FPS
    env = np.zeros(n_frames)
    win = int(ENV_SR * 0.045)
    for f in range(n_frames):
        c = int(f * hop)
        seg = timeline[max(0, c - win):c + win]
        env[f] = np.sqrt(np.mean(seg ** 2)) if len(seg) else 0.0
    p = np.percentile(env, 96) + 1e-6
    env = np.clip(env / p, 0, 1) ** 0.7
    out = np.zeros_like(env); prev = 0.0
    for f in range(n_frames):
        target = env[f]
        a = 0.6 if target > prev else 0.25
        prev = prev + a * (target - prev)
        out[f] = prev
    return np.clip(out * 0.95, 0, 1)


def main():
    if not getattr(cfg, "USE_AVATAR", True):
        print("USE_AVATAR=False → 跳过虚拟主播, 成片即 base_video.mp4")
        return
    import glfw
    from OpenGL.GL import (glReadPixels, glReadBuffer, glPixelStorei,
                           GL_RGBA, GL_UNSIGNED_BYTE, GL_BACK, GL_PACK_ALIGNMENT)
    import live2d.v3 as live2d

    scenes_dir = ROOT / "media" / "videos" / "scenes" / "1080p60"
    vo_dir = ROOT / "media" / "vo"
    total = probe(ROOT / "base_video.mp4")
    n_frames = int(total * FPS)
    print(f"总时长 {total:.1f}s  帧 {n_frames} @ {FPS}fps")
    mouth = build_envelope(scenes_dir, vo_dir, total, n_frames)
    print(f"口型包络 均值 {mouth.mean():.2f} 峰值 {mouth.max():.2f}")

    glfw.init(); glfw.window_hint(glfw.VISIBLE, glfw.FALSE)
    win = glfw.create_window(W, H, "avatar", None, None)
    glfw.make_context_current(win)
    live2d.init(); live2d.glInit()
    model = live2d.LAppModel(); model.LoadModelJson(cfg.L2D_MODEL); model.Resize(W, H)
    model.SetScale(A["scale"]); model.SetOffset(A["offset_x"], A["offset_y"])

    out_final = str(ROOT / f"{cfg.OUTPUT_BASENAME}_live2d.mp4")
    # crop_left: 裁掉画框左侧百分比。免费样例模型(llny)在脸的**左侧**有材质水印,
    # 纵向 crop 裁不掉, 必须横向裁。overlay 右对齐 → 裁左侧不改变脸的位置和大小。
    cl = A.get("crop_left", 0.0)
    dw = int(A["disp_w"] * (1 - cl))
    overlay = (f"[1:v]crop=iw*{1 - cl:.4f}:ih*{A['crop']}:iw*{cl:.4f}:0,scale={dw}:-1[a];"
               f"[0:v][a]overlay=W-w-{A['margin_x']}:H-h-{A['margin_y']}:format=auto[v]")
    ff = subprocess.Popen(
        ["ffmpeg", "-y", "-loglevel", "error",
         "-i", str(ROOT / "base_video.mp4"),
         "-f", "rawvideo", "-pix_fmt", "rgba", "-s", f"{W}x{H}", "-r", str(FPS), "-i", "-",
         "-filter_complex", overlay, "-map", "[v]", "-map", "0:a",
         *ENC, "-c:a", "copy", out_final], stdin=subprocess.PIPE)

    def P(pid, v, w=1.0):
        model.SetParameterValue(pid, float(v), w)

    sway = A["sway"]
    for f in range(n_frames):
        t = f / FPS
        P("ParamAngleX", sway * np.sin(2 * np.pi * 0.07 * t))
        P("ParamAngleY", sway * 0.75 * np.sin(2 * np.pi * 0.05 * t + 1.0))
        P("ParamAngleZ", sway * 0.75 * np.sin(2 * np.pi * 0.045 * t + 2.0))
        P("ParamBodyAngleX", sway * 0.75 * np.sin(2 * np.pi * 0.045 * t))
        P("ParamBodyAngleZ", sway * 0.5 * np.sin(2 * np.pi * 0.035 * t))
        P("ParamBreath", 0.5 + 0.5 * np.sin(2 * np.pi * 0.25 * t))
        P("ParamEyeBallX", 0.25 * np.sin(2 * np.pi * 0.03 * t))
        P("ParamEyeBallY", 0.15 * np.sin(2 * np.pi * 0.04 * t + 0.5))
        ph = t % 3.6
        e = 1.0 - np.sin(ph / 0.12 * np.pi) if ph < 0.12 else 1.0
        P("ParamEyeLOpen", e); P("ParamEyeROpen", e)
        P("ParamMouthOpenY", mouth[f])
        P("ParamMouthForm", 0.4 + 0.3 * mouth[f])

        model.Update()
        live2d.clearBuffer(0.0, 0.0, 0.0, 0.0)
        model.Draw()
        # 不需要 glFinish(): glReadPixels 本身就会同步等待渲染完成, 再加一次是冗余。
        glPixelStorei(GL_PACK_ALIGNMENT, 1); glReadBuffer(GL_BACK)
        data = glReadPixels(0, 0, W, H, GL_RGBA, GL_UNSIGNED_BYTE)
        arr = np.frombuffer(data, np.uint8).reshape(H, W, 4)[::-1]
        ff.stdin.write(arr.tobytes())
        if f % 600 == 0:
            print(f"  渲染 {f}/{n_frames}")

    ff.stdin.close(); ff.wait()
    print(f"✅ 成片(含主播): {out_final}  ({probe(out_final):.1f}s)")


if __name__ == "__main__":
    main()
