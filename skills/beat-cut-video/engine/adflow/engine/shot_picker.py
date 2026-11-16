# -*- coding: utf-8 -*-
"""
运动打分选镜头 — 重音刀配画面动得最狠的段落，平稳刀配安静段落

借鉴 BeatSync Engine「精彩时刻库」思路的零模型版：不开 AI 不调 API，
对每条素材按固定窗口采样帧差（画面变化越大分越高）建窗口池；
重音刀从高分档挑，平稳刀从中位数档挑。打分失败的素材不进池，
调用方自动退回原来的顺序游标选法（不吞错，打 warning）。
"""

import logging
import random

import numpy as np

logger = logging.getLogger("adflow.shot_picker")

# 打分窗口（秒）：和典型卡点镜头同量级，窗口里动得狠 ≈ 这段有戏
WINDOW_SEC = 1.2
_STRIDE = WINDOW_SEC / 2     # 半重叠：可挑的起点密度翻倍
_FRAMES_PER_WIN = 3          # 每窗采样帧数（头/中/尾，帧差=运动强度）
_MAX_FRAMES = 48             # 每条素材解码帧数封顶（防长素材拖慢出片）
_SKIP_PX = 12                # 帧降采样步长（12x12 像素取 1，够看清动静）


def build_motion_index(src_clips: dict) -> dict:
    """给素材建 {素材id: [(窗口起点, 运动分), ...]}，分数降序。

    打不出分的素材不进返回值，调用方对其走旧选法。
    """
    index = {}
    for key, clip in src_clips.items():
        try:
            wins = _score_one(clip)
        except Exception as e:   # 单条读帧失败不该废掉整场出片，但要留痕
            logger.warning("[ShotPicker] %s 运动打分失败，这条退回顺序选: %s", key, e)
            continue
        if wins:
            index[key] = wins
    return index


def _gray(clip, t: float) -> np.ndarray:
    a = np.asarray(clip.get_frame(t), dtype=np.float32)[::_SKIP_PX, ::_SKIP_PX, :3]
    return a.mean(axis=2)


def _score_one(clip) -> list:
    dur = float(clip.duration)
    if dur < 0.2:
        return []
    starts = np.arange(0.0, max(dur - WINDOW_SEC, 0.0) + 1e-6, _STRIDE)
    if len(starts) == 0:
        starts = np.asarray([0.0])
    # 解码预算：窗口数 x 每窗帧数超了就隔一个砍一个
    while len(starts) * _FRAMES_PER_WIN > _MAX_FRAMES and len(starts) > 1:
        starts = starts[::2]
    wins = []
    for s in starts:
        end = min(float(s) + WINDOW_SEC, dur)
        if end - float(s) < 0.2:
            break
        grays = [_gray(clip, t) for t in (float(s), (float(s) + end) / 2, end - 0.03)]
        motion = float(np.mean([np.abs(grays[i + 1] - grays[i]).mean()
                                for i in range(len(grays) - 1)]))
        wins.append((float(s), motion))
    wins.sort(key=lambda w: -w[1])
    return wins


def pick_window(index: dict, key, want_accent: bool,
                rng: random.Random, used: set):
    """挑一个窗口起点，返回 float；没池子返回 None 由调用方兜底。

    重音刀取前 25% 高分档，平稳刀取中间档；先洗牌再取（同分窗口不总拿同一个），
    用过的窗口尽量不重复（档位池子用尽则放开重用）。
    """
    wins = index.get(key)
    if not wins:
        return None
    n = len(wins)
    if want_accent:
        lo, hi = 0, max(1, n // 4)
    else:
        lo, hi = n // 4, max(n // 4 + 1, (3 * n) // 4)
    pool = [w for w in wins[lo:hi] if (key, round(w[0], 2)) not in used]
    if not pool:
        pool = list(wins[lo:hi])
    rng.shuffle(pool)
    start = pool[0][0]
    used.add((key, round(start, 2)))
    return start
