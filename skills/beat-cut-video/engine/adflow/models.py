"""
AdFlow 数据模型 — 所有 dataclass 定义

按模块分组：
  - 枚举 (ShotType, Emotion 等)
  - 素材 (MaterialRecord, MaterialUsageLog)
  - 产品与任务 (ProductProfile, ProjectTask)
  - 策略与脚本 (CreativeStrategy, StoryboardScript, StoryboardShot)
  - 匹配与产出 (ShotMatchResult, EditTimeline, AdVariant)
"""

from dataclasses import dataclass, field
from enum import Enum


# ============================================================
# 枚举
# ============================================================

class ShotType(str, Enum):
    """景别"""
    EXTREME_CLOSEUP = "extreme_closeup"
    CLOSEUP = "closeup"
    MEDIUM_CLOSEUP = "medium_closeup"
    MEDIUM = "medium"
    MEDIUM_WIDE = "medium_wide"
    WIDE = "wide"
    EXTREME_WIDE = "extreme_wide"


class CameraMovement(str, Enum):
    """运镜"""
    STATIC = "static"
    PAN_LEFT = "pan_left"
    PAN_RIGHT = "pan_right"
    TILT_UP = "tilt_up"
    TILT_DOWN = "tilt_down"
    ZOOM_IN = "zoom_in"
    ZOOM_OUT = "zoom_out"
    TRACKING = "tracking"
    HANDHELD = "handheld"
    AERIAL = "aerial"


class Emotion(str, Enum):
    """情绪基调"""
    EXCITED = "excited"
    HAPPY = "happy"
    CALM = "calm"
    SERIOUS = "serious"
    URGENT = "urgent"
    CURIOUS = "curious"
    TRUST = "trust"
    SURPRISE = "surprise"
    ANXIOUS = "anxious"
    NEUTRAL = "neutral"


class ProductVisibility(str, Enum):
    """产品露出程度"""
    NONE = "none"
    PARTIAL = "partial"
    FULL = "full"
    PACKAGING = "packaging"
    USAGE = "usage"
    BEFORE_AFTER = "before_after"
    TEXT_LOGO = "text_logo"


class ScriptRole(str, Enum):
    """分镜角色定位"""
    HOOK = "hook"
    PROBLEM = "problem"
    SOLUTION = "solution"
    PRODUCT_DEMO = "product_demo"
    TESTIMONIAL = "testimonial"
    COMPARISON = "comparison"
    CTA = "cta"
    TRANSITION = "transition"
    B_ROLL = "b_roll"


class Platform(str, Enum):
    """投放平台"""
    DOUYIN = "douyin"
    KUAISHOU = "kuaishou"
    SHIPINHAO = "shipinhao"
    OCEAN_ENGINE = "ocean_engine"
    TIKTOK = "tiktok"
    YOUTUBE_SHORTS = "youtube_shorts"


class MaterialCategory(str, Enum):
    """素材功能分类"""
    PRODUCT_SHOOT = "product_shoot"
    SCENARIO_SHOOT = "scenario_shoot"
    UGC_STYLE = "ugc_style"
    STOCK_FOOTAGE = "stock_footage"
    SCREEN_RECORD = "screen_record"
    ANIMATION = "animation"
    TEXT_CARD = "text_card"


class TaskStatus(str, Enum):
    """任务状态"""
    PENDING = "pending"
    RUNNING = "running"
    DONE = "done"
    FAILED = "failed"


class VariantStatus(str, Enum):
    """变体状态"""
    PENDING_REVIEW = "pending_review"
    APPROVED = "approved"
    REJECTED = "rejected"
    DELIVERING = "delivering"
    DELIVERED = "delivered"
    ARCHIVED = "archived"


# ============================================================
# 素材模型
# ============================================================

@dataclass
class MaterialRecord:
    """素材库中的一条镜头"""
    material_id: str = ""
    file_path: str = ""
    original_filename: str = ""
    duration_ms: int = 0
    fps: float = 30.0
    width: int = 1080
    height: int = 1920
    file_size_bytes: int = 0
    md5_hash: str = ""
    phash: str = ""
    # 方向分类: vertical / landscape / phone_rotated(手机横拍竖看) / unknown
    orientation: str = "unknown"

    # 标签维度
    scene: str = ""
    shot_type: str = ""
    camera_movement: str = ""
    emotion: str = "neutral"
    product_visibility: str = "none"
    has_person: bool = False
    person_count: int = 0
    person_role: str = ""
    person_feature: str = ""
    has_dialogue: bool = False
    has_bgm: bool = False
    lighting: str = ""
    pace: str = "medium"
    quality_flags: str = "clean"
    material_category: str = ""
    tags: str = ""  # JSON array of free tags

    # 质量评估
    auto_quality_score: float = 0.0
    visual_impact_score: float = 0.0  # 视觉冲击力 0-1

    # 来源
    source_project: str = ""
    imported_at: str = ""
    notes: str = ""

    # Diversity 追踪
    use_count_total: int = 0
    use_count_30d: int = 0
    last_used_at: str = ""
    cooldown_hours: int = 48
    performance_score: float = 50.0
    ctr_avg: float = 0.0
    cvr_avg: float = 0.0
    retention_3s_avg: float = 0.0
    retention_5s_avg: float = 0.0

    def is_cooldown_active(self, role: str = "default", config: dict | None = None) -> bool:
        """检查素材是否在冷却期内"""
        if not self.last_used_at:
            return False
        cooldown_map = {"hook": 72, "cta": 36, "default": self.cooldown_hours}
        if config:
            cooldown_map = {
                "hook": config.get("cooldown_hours_hook", 72),
                "cta": config.get("cooldown_hours_cta", 36),
                "default": config.get("cooldown_hours_default", 48),
            }
        required = cooldown_map.get(role, cooldown_map["default"])
        from datetime import datetime, timedelta
        last = datetime.fromisoformat(self.last_used_at)
        return (datetime.now() - last) < timedelta(hours=required)

    def freshness_score(self, role: str = "default", config: dict | None = None) -> float:
        """计算新鲜度得分 (0.0-1.0)，1.0 表示完全新鲜"""
        if not self.last_used_at:
            return 1.0
        cooldown_map = {"hook": 72, "cta": 36, "default": self.cooldown_hours}
        if config:
            cooldown_map = {
                "hook": config.get("cooldown_hours_hook", 72),
                "cta": config.get("cooldown_hours_cta", 36),
                "default": config.get("cooldown_hours_default", 48),
            }
        required = cooldown_map.get(role, cooldown_map["default"])
        from datetime import datetime
        last = datetime.fromisoformat(self.last_used_at)
        hours_since = (datetime.now() - last).total_seconds() / 3600
        if hours_since >= required:
            return 1.0
        return hours_since / max(required, 1)


@dataclass
class MaterialUsageLog:
    """素材使用记录"""
    id: int = 0
    material_id: str = ""
    ad_variant_id: str = ""
    shot_position: int = 0
    used_at: str = ""
    account_id: str = ""


# ============================================================
# 产品与项目模型
# ============================================================
# 风格模型
# ============================================================

@dataclass
class StyleProfile:
    """风格定义 — 影响 AI 出片的视觉/听觉/节奏偏好，含参考案例"""
    name: str = ""
    # 字幕
    subtitle_font: str = ""
    subtitle_size: int = 0
    subtitle_color: str = ""
    subtitle_stroke_color: str = ""
    subtitle_stroke_width: int = 0
    # 调色
    brightness: float = 0.0
    contrast: float = 0.0
    saturation: float = 0.0
    temperature: float = 0.0
    # 节奏
    pace: str = ""
    transition: str = ""
    # 音频
    voice: str = ""
    speech_rate: float = 0.0
    # 动画
    animation_in: str = ""
    animation_out: str = ""
    # 规则文本（Markdown，自由填写）
    rules: str = ""
    # 参考案例列表 [{"task_id": "xxx", "notes": "...", "added": "..."}]
    cases: list = None
    # 元信息
    source: str = ""
    notes: str = ""
    created: str = ""
    updated: str = ""

    def __post_init__(self):
        if self.cases is None:
            self.cases = []

    def to_dict(self) -> dict:
        from dataclasses import asdict
        return asdict(self)

    @classmethod
    def from_dict(cls, data: dict) -> "StyleProfile":
        fields = set(cls.__dataclass_fields__.keys())
        return cls(**{k: v for k, v in data.items() if k in fields})

    @property
    def is_auto(self) -> bool:
        """所有值为默认值 = AI 全自动"""
        return all(
            v == "" or v == 0 or v == 0.0 or v is False
            for v in [self.subtitle_font, self.subtitle_size, self.subtitle_color,
                       self.subtitle_stroke_color, self.subtitle_stroke_width,
                       self.brightness, self.contrast, self.saturation, self.temperature,
                       self.pace, self.transition, self.voice,
                       self.speech_rate, self.animation_in, self.animation_out]
        ) and not self.rules and not self.cases

    @property
    def case_count(self) -> int:
        return len(self.cases) if self.cases else 0

    def add_case(self, task_id: str, notes: str = ""):
        from datetime import datetime
        if self.cases is None:
            self.cases = []
        self.cases.append({
            "task_id": task_id,
            "notes": notes,
            "added": datetime.now().isoformat(),
            "label": f"案例{len(self.cases) + 1}",
        })

    def build_prompt_context(self) -> str:
        """构建注入 AI prompt 的风格上下文"""
        parts = [f"## 风格参考: {self.name}"]

        if self.rules:
            parts.append(f"### 规则\n{self.rules}")

        # 参数约束
        params = []
        if self.pace:
            params.append(f"节奏={self.pace}")
        if self.transition:
            params.append(f"转场={self.transition}")
        if self.voice:
            params.append(f"音色={self.voice}")
        if self.animation_in:
            params.append(f"入场动画={self.animation_in}")
        if self.subtitle_size > 0:
            params.append(f"字号≈{self.subtitle_size}px")
        if self.subtitle_color:
            params.append(f"字幕色={self.subtitle_color}")
        if params:
            parts.append(f"### 参数偏好\n{', '.join(params)}")

        # 参考案例
        if self.cases:
            parts.append(f"### 参考案例 ({len(self.cases)}个)")
            for c in self.cases:
                parts.append(
                    f"- {c.get('label','案例')}: {c.get('notes','')} "
                    f"[task_id: {c.get('task_id','')[:8]}]"
                )
            parts.append("请参考以上案例的风格和节奏来创作。")

        return "\n".join(parts)


@dataclass
class ProductProfile:
    """产品信息档案"""
    product_id: str = ""
    name: str = ""
    category: str = ""
    key_selling_points: str = ""       # JSON array
    target_audience: str = ""
    pain_points: str = ""              # JSON array
    brand_tone: str = ""
    prohibited_words: str = ""         # JSON array
    avg_price_range: str = ""
    competitors: str = ""              # JSON array
    notes: str = ""
    created_at: str = ""
    updated_at: str = ""


@dataclass
class ProjectTask:
    """一次出片任务"""
    task_id: str = ""
    product_id: str = ""
    platform: str = "ocean_engine"
    account_id: str = ""
    target_duration_ms: int = 30000
    variant_count: int = 5
    status: str = "pending"
    strategy_id: str = ""
    created_at: str = ""
    completed_at: str = ""
    notes: str = ""


# ============================================================
# 策略与脚本模型
# ============================================================

@dataclass
class CreativeStrategy:
    """策略 Agent 输出"""
    strategy_id: str = ""
    task_id: str = ""
    narrative_type: str = ""
    hook_type: str = ""
    pace_style: str = ""
    tone: str = ""
    key_message: str = ""
    target_emotion: str = ""
    reasoning: str = ""
    specific_angle: str = ""           # 具体切入角度
    target_scenario: str = ""          # 核心使用场景
    opening_style: str = ""            # 开场风格
    emotion_arc: str = ""              # 情绪弧线
    differentiation_hints: str = ""    # JSON 数组: 不同变体切入角度提示
    source_signals: str = ""           # JSON: 触发此策略的数据信号
    created_at: str = ""


@dataclass
class StoryboardShot:
    """分镜脚本中的一镜"""
    id: int = 0
    script_id: str = ""
    shot_index: int = 0
    role: str = "b_roll"
    duration_ms: int = 3000
    description: str = ""
    camera_direction: str = ""
    narration_text: str = ""
    narration_segments: str = ""     # JSON数组: ["句1","句2",...] LLM直接分段
    required_product_visibility: str = ""
    required_scene: str = ""
    required_emotion: str = ""
    fallback_notes: str = ""


@dataclass
class StoryboardScript:
    """完整分镜脚本"""
    script_id: str = ""
    task_id: str = ""
    strategy_id: str = ""
    shots: list[StoryboardShot] = field(default_factory=list)
    cta_text: str = ""
    total_duration_ms: int = 0
    variant_index: int = 0
    created_at: str = ""


# ============================================================
# 匹配与产出模型
# ============================================================

@dataclass
class ShotMatchResult:
    """单镜匹配结果"""
    shot_index: int = 0
    material_id: str = ""
    material_file: str = ""
    start_ms: int = 0
    end_ms: int = 0
    match_score: float = 0.0
    # 子片段重组（防判重）：[(起ms, 止ms), ...] 素材内绝对时间，非空时渲染按此拼接
    sub_ranges: list = None


@dataclass
class EditTimeline:
    """剪辑时间线"""
    timeline_id: str = ""
    script_id: str = ""
    shots: list[ShotMatchResult] = field(default_factory=list)
    bgm_file: str = ""
    subtitle_tracks: str = ""          # JSON
    cta_overlay: str = ""              # JSON
    variant_metadata: str = ""         # JSON: {hook_type, bgm_name, cta_text, ...}


@dataclass
class AdVariant:
    """产出的一个广告变体"""
    variant_id: str = ""
    task_id: str = ""
    script_id: str = ""
    timeline_id: str = ""
    output_file: str = ""
    variant_metadata: str = ""         # JSON
    status: str = "pending_review"
    compliance_check_passed: bool = False
    created_at: str = ""
