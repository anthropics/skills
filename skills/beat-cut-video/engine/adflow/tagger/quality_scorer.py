"""
素材自动质量评分
- 基于客观指标（分辨率/时长/稳定性）打分
- 不依赖 AI，纯规则评估
- 满分 100 分
"""

from dataclasses import dataclass


@dataclass
class QualityReport:
    """质量评分报告"""
    total_score: float = 0.0         # 0-100
    resolution_score: float = 0.0    # 分辨率得分
    stability_score: float = 0.0     # 稳定性得分（需 FFprobe 分析）
    duration_score: float = 0.0      # 时长得分
    audio_score: float = 0.0         # 音频得分
    flags: list[str] = None          # 质量问题标记

    def __post_init__(self):
        if self.flags is None:
            self.flags = []


# 各维度满分
MAX_RESOLUTION = 25
MAX_STABILITY = 25
MAX_DURATION = 25
MAX_AUDIO = 25


def score_quality(
    width: int, height: int,
    duration_ms: int,
    has_audio: bool = False,
    quality_flags: str = "clean",
) -> QualityReport:
    """综合质量评分"""
    report = QualityReport()

    # 1. 分辨率评分 (0-25)
    total_pixels = width * height
    if total_pixels >= 1920 * 1080:
        report.resolution_score = MAX_RESOLUTION
    elif total_pixels >= 1280 * 720:
        report.resolution_score = 20
    elif total_pixels >= 720 * 720:
        report.resolution_score = 12
    elif total_pixels >= 640 * 360:
        report.resolution_score = 5
    else:
        report.resolution_score = 2

    # 2. 稳定性评分 (0-25) — 基于 quality_flags
    flags_lower = quality_flags.lower()
    report.stability_score = MAX_STABILITY
    problem_count = 0
    if "blurry" in flags_lower:
        report.stability_score -= 10
        problem_count += 1
    if "shaky" in flags_lower:
        report.stability_score -= 10
        problem_count += 1
    if "overexposed" in flags_lower or "underexposed" in flags_lower:
        report.stability_score -= 5
        problem_count += 1
    if "noisy" in flags_lower:
        report.stability_score -= 5
        problem_count += 1
    if "watermark" in flags_lower:
        report.stability_score -= 5
        problem_count += 1

    if problem_count == 0 and "clean" in flags_lower:
        report.stability_score = MAX_STABILITY

    report.stability_score = max(0, report.stability_score)

    # 3. 时长评分 (0-25)
    sec = duration_ms / 1000
    if sec >= 8:
        report.duration_score = MAX_DURATION      # ≥8秒满分，足够剪
    elif sec >= 5:
        report.duration_score = 20
    elif sec >= 3:
        report.duration_score = 12
    elif sec >= 1.5:
        report.duration_score = 5
    else:
        report.duration_score = 2                 # 太短，难用

    # 4. 音频评分 (0-25)
    report.audio_score = MAX_AUDIO if has_audio else 5  # 有音轨至少可以做参考音

    # 汇总
    report.total_score = (
        report.resolution_score +
        report.stability_score +
        report.duration_score +
        report.audio_score
    )

    # 质量标记
    report.flags = [f for f in flags_lower.split(",") if f.strip() and f.strip() != "clean"]
    if not report.flags and "clean" in flags_lower:
        report.flags = []

    return report
