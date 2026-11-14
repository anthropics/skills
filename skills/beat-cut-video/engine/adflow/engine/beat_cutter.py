# -*- coding: utf-8 -*-
"""
BGM 卡点切点规划 — 鼓点提取 + 段落感知的切点密度

和老流程（配音当主时钟，2-3 秒一镜头）相反，这里 BGM 是主时钟：
切点全部落在 librosa 检出的真实鼓点上，不做等间隔假设（变奏/渐快都跟得住）。

段落感知 = 按「小节」（4 拍）平均响度把歌分成平稳段/高潮段：
  - flash    快闪：全程每拍一刀（最密）
  - standard 卡点：平稳段两拍一刀，高潮段加密到每拍一刀
  - build    递进：平稳段四拍一刀，从能量跳变最大处（drop）起每拍一刀
"""

import logging
import os
from dataclasses import dataclass, field

import numpy as np

logger = logging.getLogger("adflow.beat_cutter")

# 小节拍数（流行/电子惯例，段落判断按小节算）
_BEATS_PER_BAR = 4

# 风格 → (平稳段每 N 拍一刀, 高潮段每 N 拍一刀)
STYLE_DENSITY = {
    "flash": (1, 1),
    "standard": (2, 1),
    "build": (4, 1),
}

# 最短镜头（秒）：再短肉眼跟不上，宁可合并到下一刀
MIN_SHOT_SEC = 0.32


@dataclass
class BeatMap:
    """一首 BGM 的节拍地图"""
    bpm: float
    beat_times: list           # 每一拍的时间点（秒）
    beat_accents: list         # 每拍起音强度 0~1（哪一刀加特效）
    beat_energy: list          # 每拍区间响度 0~1（分段用）
    duration: float            # 音频全长（秒）


@dataclass
class CutPlan:
    """一次出片的切点方案"""
    style: str
    bpm: float
    cut_times: list            # 镜头起点（含 0.0），末尾追加成片结束点
    accent_flags: list         # 每个镜头是否重音刀（触发 punch/闪白）
    high_energy_start: float | None  # 高潮段起点（秒），整首都平则 None
    duration: float            # 成片时长

    @property
    def shot_count(self) -> int:
        return max(0, len(self.cut_times) - 1)


def extract_beat_map(bgm_path: str) -> BeatMap:
    """librosa 提取节拍地图。

    BGM 缺失/读不出/测不出节拍 → 直接抛错：卡点没有节拍就没意义，不带病往下走。
    """
    if not bgm_path or not os.path.exists(bgm_path):
        raise FileNotFoundError("找不到 BGM 文件: %r — 卡点出片必须有 BGM" % bgm_path)

    import librosa

    y, sr = librosa.load(bgm_path, sr=22050, mono=True)
    if len(y) < sr:
        raise ValueError("BGM 太短（不足 1 秒），提不出节拍")
    duration = len(y) / sr

    # trim=False：默认 True 会把起音弱的拍整段剪掉（安静前奏直接没拍，
    # 开头就成 10 秒不切的长镜头），卡点必须全程跟拍
    tempo, beat_frames = librosa.beat.beat_track(y=y, sr=sr, trim=False)
    bpm = float(np.atleast_1d(tempo)[0])
    beat_frames = np.atleast_1d(beat_frames)
    beat_times_raw = librosa.frames_to_time(beat_frames, sr=sr)
    # 去掉贴在一起的两拍（时间四舍五入到 0.1ms 再 unique），
    # 拍点和帧下标必须同步过滤，否则起音/响度数组会和拍点错位
    _times, keep = np.unique(np.round(beat_times_raw, 4), return_index=True)
    beat_times = _times
    beat_frames = beat_frames[keep]
    if len(beat_times) < 4:
        raise ValueError("BGM 里只检出 %d 个节拍点 — 换一首节奏清晰的音乐" % len(beat_times))

    # 每拍起音强度 / 区间响度：帧级序列按拍区间取均值，再整体归一到 0~1
    onset_env = librosa.onset.onset_strength(y=y, sr=sr)
    if float(np.std(onset_env)) < 1e-4:
        # 纯静音/白噪音：librosa 会硬凑节拍网格，测了不如不测
        raise ValueError("BGM 没有节奏起伏（近乎无声），测不出节拍")
    rms = librosa.feature.rms(y=y)[0]

    def _per_beat_mean(frame_series: np.ndarray) -> np.ndarray:
        vals = []
        n = len(frame_series)
        for i, f in enumerate(beat_frames):
            f_end = beat_frames[i + 1] if i + 1 < len(beat_frames) else n
            f0, f1 = int(f), min(int(f_end), n)
            vals.append(float(frame_series[f0:f1].mean()) if f1 > f0 else 0.0)
        return np.asarray(vals)

    def _normalize(vals: np.ndarray) -> np.ndarray:
        rng = float(vals.max() - vals.min())
        if rng < 1e-9:
            return np.zeros_like(vals)
        return (vals - vals.min()) / rng

    beat_accents = _normalize(_per_beat_mean(onset_env))
    beat_energy = _normalize(_per_beat_mean(rms))

    logger.info("[BeatCutter] BPM=%.1f 拍数=%d 时长=%.1fs", bpm, len(beat_times), duration)
    return BeatMap(
        bpm=bpm,
        beat_times=beat_times.tolist(),
        beat_accents=beat_accents.tolist(),
        beat_energy=beat_energy.tolist(),
        duration=duration,
    )


def _bar_sections(beat_energy: list) -> tuple[list[bool], int]:
    """按小节（4 拍）分平稳/高潮。

    返回 (每拍是否在高潮段, 高潮起始拍下标)。高潮起始 = 能量一次跳变最大的小节边界，
    且跳变后小节能量须高于中位数（防止把开头的淡入当 drop）。
    """
    energies = np.asarray(beat_energy, dtype=float)
    n_beats = len(energies)
    n_bars = n_beats // _BEATS_PER_BAR
    if n_bars < 2:
        return [False] * n_beats, n_beats  # 太短分不了段 → 全程平稳

    bar_energy = energies[:n_bars * _BEATS_PER_BAR].reshape(
        n_bars, _BEATS_PER_BAR).mean(axis=1)

    # 平稳/高潮标记：小节能量 >= 65 分位算高潮
    threshold = float(np.quantile(bar_energy, 0.65))
    bar_high = bar_energy >= threshold

    # drop 候选：相邻小节能量正跳变最大处
    jumps = bar_energy[1:] - bar_energy[:-1]
    drop_bar = int(np.argmax(jumps)) + 1
    if not (bar_high[drop_bar] and jumps[drop_bar - 1] > 0.1):
        drop_bar = int(np.argmax(bar_high)) if bar_high.any() else n_bars

    high_flags: list[bool] = []
    for b in range(n_bars):
        high_flags.extend([bool(bar_high[b])] * _BEATS_PER_BAR)
    high_flags.extend([False] * (n_beats - len(high_flags)))  # 尾部不满一小节的拍
    return high_flags, drop_bar * _BEATS_PER_BAR


def plan_cuts(beat_map: BeatMap, style: str, target_duration: float = 0.0,
              fps: float = 30.0) -> CutPlan:
    """把节拍地图变成切点方案。

    target_duration 0 = 整首 BGM 全长。超过 BGM 长度按 BGM 长度算（BGM 是主时钟）。
    fps 把切点锁到输出帧网格（刀口正好落在帧上，最多挪半帧），0=不量化。
    """
    if style not in STYLE_DENSITY:
        raise ValueError("未知风格 %r，可选: %s" % (style, "/".join(STYLE_DENSITY)))
    density_low, density_high = STYLE_DENSITY[style]

    duration = beat_map.duration if target_duration <= 0 else min(
        target_duration, beat_map.duration)

    beats = np.asarray(beat_map.beat_times, dtype=float)
    accents = np.asarray(beat_map.beat_accents, dtype=float)
    energies = np.asarray(beat_map.beat_energy, dtype=float)

    # 只留 [0, duration) 内的拍
    in_range = np.where(beats < duration - 1e-6)[0]
    if len(in_range) < 4:
        raise ValueError("成片时长内只有 %d 拍，太短剪不出卡点 — 加长 --duration 或换长音乐" % len(in_range))

    high_flags, drop_beat_idx = _bar_sections(energies.tolist())

    # 逐拍决定这一刀切不切：小节内按步长取，切点一定落在拍上
    accent_threshold = float(np.quantile(accents[in_range], 0.6))  # 起音前 40% 算重音刀
    cut_idx: list[int] = []
    # 第一刀从 0.0 起（即使第一拍在 0.3s，0~第一拍这段也归第一个镜头）
    for bi in in_range:
        stride = density_high if high_flags[bi] else density_low
        # 是小节内第 stride-1 拍（即小节头/第 stride 拍…）才切
        pos_in_song = bi - in_range[0]
        if stride <= 1 or pos_in_song % stride == 0:
            cut_idx.append(bi)

    cut_times = [0.0] + [float(beats[bi]) for bi in cut_idx if beats[bi] > MIN_SHOT_SEC]
    # 切点锁到输出帧网格：不量化刀口常落在两帧之间，渲染出来是"软刀"。
    # 量化最多挪半帧（30fps 下 17ms），仍在拍点容差内；成片结束边界在后面另补
    if fps and fps > 0:
        cut_times = [cut_times[0]] + [round(t * fps) / fps for t in cut_times[1:]]
    # 合并过短的镜头间隔（连续重拍歌/量化挤压会触发；宁并勿快）
    merged: list[float] = [cut_times[0]]
    for t in cut_times[1:]:
        if t - merged[-1] >= MIN_SHOT_SEC:
            merged.append(t)
    cut_times = merged
    # 尾镜头太短就并入前一个（切点回退到倒数第二个，末尾边界照常补齐）
    if len(cut_times) > 1 and duration - cut_times[-1] < MIN_SHOT_SEC:
        cut_times.pop()
    cut_times.append(float(duration))  # 末尾边界 = 成片结束

    # 每镜头的重音标记（镜头起点对应那拍的起音强度，最后一项是结束边界占位）
    def _is_accent(bi: int) -> bool:
        return bool(accents[bi] >= max(accent_threshold, 0.35))

    accent_flags = []
    for k in range(len(cut_times) - 1):
        t = cut_times[k]
        near = int(np.argmin(np.abs(beats - t)))
        accent_flags.append(_is_accent(near))

    drop_time = float(beats[drop_beat_idx]) if drop_beat_idx < len(beats) else None
    high_start = drop_time if any(high_flags[b] for b in in_range) else None

    plan = CutPlan(
        style=style,
        bpm=beat_map.bpm,
        cut_times=cut_times,
        accent_flags=accent_flags,
        high_energy_start=high_start,
        duration=duration,
    )
    logger.info("[BeatCutter] %s 风格: %d 个镜头, 平均 %.2fs/镜头, 重音刀 %d 个",
                style, plan.shot_count, duration / max(plan.shot_count, 1),
                sum(accent_flags))
    return plan
