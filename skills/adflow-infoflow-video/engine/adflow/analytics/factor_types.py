# -*- coding: utf-8 -*-
"""爆款因子数据结构 — 6大类30+因子，类比量化因子体系"""

from dataclasses import dataclass, field, asdict
from typing import Optional


# ═══════════════════════════════════════
# 因子维度定义
# ═══════════════════════════════════════

@dataclass
class RhythmFactors:
    """剪辑节奏因子（类比动量因子）"""
    avg_shot_duration: float = 0.0      # 平均镜头时长(秒)
    shot_count: int = 0                 # 镜头切换次数
    shot_duration_variance: float = 0.0 # 镜头时长方差
    cut_speed: float = 0.0             # 切换密度(次/秒)
    tempo_bpm: float = 0.0             # BGM节拍(BPM)

    def to_vector(self) -> list[float]:
        return [self.avg_shot_duration, float(self.shot_count),
                self.shot_duration_variance, self.cut_speed, self.tempo_bpm]


@dataclass
class EmotionFactors:
    """情绪曲线因子（类比贪婪/恐慌因子）"""
    emotion_sequence: list[str] = field(default_factory=list)
    peak_emotion_position: float = 0.0  # 情绪峰值位置(0-1)
    emotion_volatility: float = 0.0     # 情绪波动率
    hook_emotion: str = "中性"           # 钩子镜头情绪
    emotion_energy: float = 0.0         # 情绪能量均值(1-10)

    def to_vector(self) -> list[float]:
        return [self.peak_emotion_position, self.emotion_volatility,
                self.emotion_energy]


@dataclass
class VisualFactors:
    """视觉冲击因子（类比量价因子）"""
    brightness_mean: float = 0.0        # 平均亮度(0-255)
    brightness_variance: float = 0.0    # 亮度变化率
    color_saturation: float = 0.0       # 色彩饱和度(0-1)
    scene_change_rate: float = 0.0      # 场景切换率(次/秒)
    motion_intensity: float = 0.0       # 运镜强度(0-1)

    def to_vector(self) -> list[float]:
        return [self.brightness_mean / 255.0, self.brightness_variance / 255.0,
                self.color_saturation, self.scene_change_rate,
                self.motion_intensity]


@dataclass
class CopyFactors:
    """文案密度因子（类比基本面因子）"""
    words_per_second: float = 0.0       # 语速(字/秒)
    keyword_density: float = 0.0        # 行动词密度(0-1)
    cta_position_ratio: float = 0.0     # CTA位置(0-1, 越靠近1越晚)
    sentence_length_avg: float = 0.0    # 平均句长(字)
    question_ratio: float = 0.0         # 问句占比(0-1)
    power_word_count: int = 0           # 力度词数量

    def to_vector(self) -> list[float]:
        return [self.words_per_second, self.keyword_density,
                self.cta_position_ratio, self.sentence_length_avg,
                self.question_ratio, float(self.power_word_count)]


@dataclass
class VoiceFactors:
    """音色匹配因子（类比音色因子）"""
    voice_gender: str = ""              # "female" | "male"
    voice_speed: float = 1.0            # 配音语速(倍速)
    voice_emotion: str = "中性"          # 配音情绪
    bgm_energy: float = 0.0             # BGM能量(0-1)
    voice_bgm_match: float = 0.0        # 音画协调度(0-1)
    has_bgm: bool = False

    def to_vector(self) -> list[float]:
        return [
            1.0 if self.voice_gender == "female" else 0.0,
            self.voice_speed, self.bgm_energy,
            self.voice_bgm_match, 1.0 if self.has_bgm else 0.0,
        ]


@dataclass
class StructureFactors:
    """结构比例因子（类比结构因子）"""
    hook_ratio: float = 0.0             # 钩子占比(0-1)
    product_intro_time: float = 0.0     # 产品露出时机(0-1)
    cta_duration: float = 0.0           # CTA时长(秒)
    total_duration: float = 0.0         # 总时长(秒)
    shot_role_diversity: float = 0.0    # 镜头角色多样性(0-1)
    structure_pattern: str = ""         # 结构模式: "hook-first" | "story" | "direct-sell"

    def to_vector(self) -> list[float]:
        return [self.hook_ratio, self.product_intro_time,
                self.cta_duration, self.total_duration,
                self.shot_role_diversity]


# ═══════════════════════════════════════
# 完整因子快照
# ═══════════════════════════════════════

@dataclass
class VideoFactors:
    """完整因子快照 — 6大类所有因子"""
    rhythm: RhythmFactors = field(default_factory=RhythmFactors)
    emotion: EmotionFactors = field(default_factory=EmotionFactors)
    visual: VisualFactors = field(default_factory=VisualFactors)
    copy: CopyFactors = field(default_factory=CopyFactors)
    voice: VoiceFactors = field(default_factory=VoiceFactors)
    structure: StructureFactors = field(default_factory=StructureFactors)

    # 元数据
    source_type: str = ""               # "labeled" | "adflow_output"
    source_task_id: str = ""
    video_path: str = ""

    def to_vector(self, normalize: bool = True) -> list[float]:
        """转为28维特征向量（供XGBoost使用）。

        Returns: 28维 float list
        """
        vec = (
            self.rhythm.to_vector()      # 5
            + self.emotion.to_vector()    # 3
            + self.visual.to_vector()     # 5
            + self.copy.to_vector()       # 6
            + self.voice.to_vector()      # 5
            + self.structure.to_vector()  # 5
        )
        # 补到固定维数
        while len(vec) < 30:
            vec.append(0.0)
        return vec[:30]

    def to_dict(self) -> dict:
        """转为嵌套dict（供JSON存储和千问交互）"""
        return {
            "rhythm": asdict(self.rhythm),
            "emotion": asdict(self.emotion),
            "visual": asdict(self.visual),
            "copy": asdict(self.copy),
            "voice": asdict(self.voice),
            "structure": asdict(self.structure),
        }

    # ── 所有因子名（供特征重要性显示）──
    FACTOR_NAMES: list[str] = field(default_factory=lambda: [
        # rhythm (5)
        "avg_shot_duration", "shot_count", "shot_duration_variance",
        "cut_speed", "tempo_bpm",
        # emotion (3)
        "peak_emotion_position", "emotion_volatility", "emotion_energy",
        # visual (5)
        "brightness_mean", "brightness_variance", "color_saturation",
        "scene_change_rate", "motion_intensity",
        # copy (6)
        "words_per_second", "keyword_density", "cta_position_ratio",
        "sentence_length_avg", "question_ratio", "power_word_count",
        # voice (5)
        "voice_gender", "voice_speed", "bgm_energy",
        "voice_bgm_match", "has_bgm",
        # structure (5) → padding to 30
        "hook_ratio", "product_intro_time", "cta_duration",
        "total_duration", "shot_role_diversity", "padding_29",
    ], init=False, repr=False)


# ═══════════════════════════════════════
# 标注记录
# ═══════════════════════════════════════

@dataclass
class HitRecord:
    """爆款标注记录 — 类比量化 signal_records"""
    id: int = 0
    video_path: str = ""
    video_source: str = "local"
    source_task_id: str = ""

    # 文案
    copy_text: str = ""

    # 投放数据（用户提供）
    impressions: int = 0
    clicks: int = 0
    conversions: int = 0
    ctr: float = 0.0
    cvr: float = 0.0
    cost: float = 0.0
    play_3s_rate: float = 0.0
    play_full_rate: float = 0.0
    like_count: int = 0
    share_count: int = 0
    comment_count: int = 0

    # 标注
    label: str = ""                     # "爆款" | "一般" | "低效"
    label_source: str = "manual"
    label_notes: str = ""

    # 关联因子
    factors: Optional[VideoFactors] = None

    labeled_at: str = ""
    created_at: str = ""


# ═══════════════════════════════════════
# 爆款区间的参考值（模型训练后动态更新）
# ═══════════════════════════════════════

@dataclass
class FactorBenchmark:
    """单个因子的爆款参考区间"""
    name: str = ""
    hit_mean: float = 0.0
    hit_std: float = 0.0
    hit_min: float = 0.0
    hit_max: float = 0.0
    importance: float = 0.0             # XGBoost 特征重要性
    recommendation: str = ""            # 优化建议文本


@dataclass
class FactorReport:
    """完整因子分析报告"""
    sample_count: int = 0
    hit_count: int = 0
    benchmarks: list[FactorBenchmark] = field(default_factory=list)
    top_factors: list[str] = field(default_factory=list)
    model_accuracy: float = 0.0
    generated_at: str = ""
