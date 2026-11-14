# -*- coding: utf-8 -*-
"""
踩点效果包 — 只提供原子效果，按预设组装在 make_beat_video.py 里做

约定：传入的 shot 都是 subclipped 之后的镜头，t=0 即踩点瞬间，
      所以「踩点触发」的效果全部用 t 的衰减函数实现，不另设计时器。
"""

import math

import numpy as np
from moviepy import ColorClip, CompositeVideoClip, TextClip, VideoClip
from moviepy.video.fx import MirrorX, MultiplySpeed, TimeMirror

# 白闪衰减时长（秒）：3 帧内暗下去，长了就成"糊"不成"闪"
_FLASH_DECAY = 0.09


def punch_zoom(shot, strength: float = 0.15, tau: float = 0.14):
    """踩点瞬间放大后指数回弹（重音刀的核心效果）"""
    return shot.resized(lambda t: 1.0 + strength * math.exp(-t / tau))


def calm_zoom(shot, amount: float = 0.08):
    """整个镜头匀速缓推（平稳段铺垫用，和 punch 的爆发形成反差）"""
    dur = max(shot.duration, 0.01)
    return shot.resized(lambda t: 1.0 + amount * (t / dur))


def mirror_flip(shot):
    """水平镜像翻转（快闪里隔几刀翻一次，画面不单调）"""
    return shot.with_effects([MirrorX()])


def reverse_play(shot):
    """倒放（和正放混切的"回手"镜头，借鉴 MusicVideoCutter 的方向混切）"""
    return shot.with_effects([TimeMirror()])


def slow_to_fill(shot, target_dur: float):
    """素材比镜头短时整体慢放填满（不黑帧不跳切）"""
    factor = shot.duration / target_dur
    if factor >= 0.95:  # 差 5% 以内直接用原速，尾部对齐交给拼接
        return shot
    return shot.with_effects([MultiplySpeed(factor)]).with_duration(target_dur)


def flash_layer(width: int, height: int, duration: float,
                color: tuple = (255, 255, 255), decay: float = _FLASH_DECAY):
    """起音瞬间的全屏白闪/闪黑层（用动态 mask 衰减，不用 with_opacity 兼容性差）"""
    def mask_frame(t):
        v = max(0.0, 1.0 - t / decay)
        return np.full((height, width), v, dtype=float)

    mask = VideoClip(frame_function=mask_frame, duration=duration, is_mask=True)
    layer = ColorClip(size=(width, height), color=color, duration=duration)
    return layer.with_mask(mask)


def shake(shot, strength_px: int = 12, tau: float = 0.18, freq_hz: int = 11):
    """踩点冲击抖动：先放大留边，再衰减正弦偏移，全程不露黑边"""
    w, h = shot.size
    margin = strength_px * 2
    big = shot.resized((w + 2 * margin, h + 2 * margin))

    def pos(t):
        decay = math.exp(-t / tau)
        dx = strength_px * decay * math.sin(2 * math.pi * freq_hz * t)
        dy = strength_px * decay * math.cos(2 * math.pi * freq_hz * 0.9 * t)
        return (-margin + dx, -margin + dy)

    return CompositeVideoClip([big.with_position(pos)], size=(w, h))


def word_pop(word: str, duration: float, font_path: str,
             font_size: int = 100, color: str = "white",
             stroke_color: str = "black", stroke_width: int = 5):
    """大字快闪：整词踩点弹出，0.1s 从 1.3 倍缩稳，之后轻微呼吸"""
    if not word:
        return None
    txt = TextClip(
        font=font_path, text=word, font_size=font_size, color=color,
        stroke_color=stroke_color, stroke_width=stroke_width, method="label",
    )

    def scale(t):
        if t < 0.1:
            return 1.3 - 0.3 * (t / 0.1)
        return 1.0 + 0.02 * math.sin(2 * math.pi * 1.5 * t)

    return (txt.resized(scale)
              .with_duration(duration)
              .with_position(("center", "center")))
