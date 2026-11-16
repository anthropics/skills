# -*- coding: utf-8 -*-
"""
创意预评分器 — 出片前对每个变体预估表现

评分维度（冷启动用规则 + LLM，有数据后切 XGBoost）:
  1. 文案吸引力 (0.35): hook 强度 + 口语度 + CTA 清晰度
  2. 结构节奏 (0.30): 钩子占比 + 镜头时长分布 + 情绪曲线
  3. 视觉匹配 (0.20): 素材与文案匹配分 + 色彩一致性
  4. 平台适配 (0.15): 平台风格符合度 + 时长合规

输出:
  CreativeScore: total_score(0-10) + ctr_estimate + confidence + breakdown + suggestions
"""

from dataclasses import dataclass, field


@dataclass
class CreativeScore:
    """单个变体预评分结果"""
    variant_id: str = ""
    variant_index: int = 0
    total_score: float = 0.0       # 0-10
    ctr_estimate: float = 0.0      # 预估 CTR（0.005 = 0.5%）
    confidence: float = 0.0        # 置信度（0-1），冷启动阶段较低
    breakdown: dict = field(default_factory=dict)  # 各维度得分
    suggestions: list[str] = field(default_factory=list)


class CreativeScorer:
    """创意预评分器"""

    # 维度权重
    DIM_WEIGHTS = {
        "copy_appeal": 0.35,        # 文案吸引力
        "structure_rhythm": 0.30,   # 结构节奏
        "visual_match": 0.20,       # 视觉匹配
        "platform_fit": 0.15,       # 平台适配
    }

    def __init__(self, category: str = "", platform: str = "douyin"):
        self.category = category
        self.platform = platform
        self._model = None          # 将来加载 XGBoost 模型
        self._min_samples = 50      # 最少样本数才启用模型

    def score_script(self, script, copy_filter_result=None, script_index: int = 0) -> CreativeScore:
        """评估一个分镜脚本的预估表现

        Args:
            script: StoryboardScript
            copy_filter_result: CopyFilter 的 FilterResult（可复用其 sub_scores）
            script_index: 变体序号

        Returns:
            CreativeScore
        """
        # 1. 文案吸引力 — 复用 CopyFilter 评分
        copy_appeal = self._score_copy_appeal(script, copy_filter_result)

        # 2. 结构节奏
        structure_rhythm = self._score_structure_rhythm(script)

        # 3. 视觉匹配 — 脚本是否有足够的视觉描述
        visual_match = self._score_visual_match(script)

        # 4. 平台适配
        platform_fit = self._score_platform_fit(script)

        # 加权综合
        weighted = (
            copy_appeal * self.DIM_WEIGHTS["copy_appeal"]
            + structure_rhythm * self.DIM_WEIGHTS["structure_rhythm"]
            + visual_match * self.DIM_WEIGHTS["visual_match"]
            + platform_fit * self.DIM_WEIGHTS["platform_fit"]
        ) / sum(self.DIM_WEIGHTS.values())  # 标准化回 0-10

        # CTR 预估：粗略映射（冷启动用经验公式）
        # 10分 ≈ CTR 5%, 5分 ≈ CTR 1.5%, 0分 ≈ CTR 0.3%
        ctr_estimate = 0.003 + weighted / 10 * 0.047  # 0.3% ~ 5%

        # 置信度：冷启动阶段较低
        confidence = 0.4 + weighted / 10 * 0.3  # 0.4 ~ 0.7

        suggestions = self._generate_suggestions(
            copy_appeal, structure_rhythm, visual_match, platform_fit)

        return CreativeScore(
            variant_id=getattr(script, 'script_id', ''),
            variant_index=script_index,
            total_score=round(weighted, 1),
            ctr_estimate=round(ctr_estimate, 4),
            confidence=round(confidence, 2),
            breakdown={
                "copy_appeal": round(copy_appeal, 1),
                "structure_rhythm": round(structure_rhythm, 1),
                "visual_match": round(visual_match, 1),
                "platform_fit": round(platform_fit, 1),
            },
            suggestions=suggestions,
        )

    def score_batch(self, scripts: list, copy_filter_results: dict | None = None) -> list[CreativeScore]:
        """批量评估多个变体

        Args:
            scripts: StoryboardScript 列表
            copy_filter_results: {script_id: FilterResult} 映射

        Returns:
            按 total_score 降序排列的评分列表
        """
        scores = []
        for i, script in enumerate(scripts):
            cf_result = None
            if copy_filter_results:
                cf_result = copy_filter_results.get(getattr(script, 'script_id', ''))
            score = self.score_script(script, cf_result, i)
            scores.append(score)

        scores.sort(key=lambda s: s.total_score, reverse=True)
        return scores

    # ── 子维度评分 ──

    def _score_copy_appeal(self, script, cf_result=None) -> float:
        """文案吸引力 (0-10)"""
        if cf_result and hasattr(cf_result, 'sub_scores'):
            ss = cf_result.sub_scores
            hook = ss.get("hook_strength", 5)
            oral = ss.get("oral_quality", 5)
            cta = ss.get("cta_strength", 5)
            scene = ss.get("scene_coverage", 5)
            return (hook * 0.35 + oral * 0.20 + cta * 0.25 + scene * 0.20)
        # 回退：从脚本直接计算
        all_text = " ".join(s.narration_text or "" for s in script.shots)
        score = 5.0
        if len(all_text) >= 100:
            score += 1
        if "?" in all_text or "？" in all_text:
            score += 1
        if any(w in all_text for w in ["下单", "点击", "抢", "立即"]):
            score += 1
        return min(10, max(0, score))

    def _score_structure_rhythm(self, script) -> float:
        """结构节奏 (0-10)"""
        shots = script.shots if hasattr(script, 'shots') else []
        if not shots:
            return 5.0

        n = len(shots)
        durations = [s.duration_ms for s in shots if hasattr(s, 'duration_ms')]

        # 检查是否有 hook→problem→solution→demo→cta 五段
        roles = {getattr(s, 'role', '') for s in shots}
        required = {"hook", "cta"}
        has_structure = len(required & roles) / len(required)  # 0-1

        # 时长分布：检查是否有极短/极长的镜头
        if durations:
            avg = sum(durations) / len(durations)
            too_short = sum(1 for d in durations if d < 1000)
            too_long = sum(1 for d in durations if d > 12000)
            rhythm_score = max(0, 10 - too_short * 2 - too_long * 2)
        else:
            rhythm_score = 5

        return has_structure * 5 + rhythm_score * 0.5

    def _score_visual_match(self, script) -> float:
        """视觉匹配 (0-10) — 脚本中视觉描述的丰富度"""
        score = 5.0
        for shot in script.shots if hasattr(script, 'shots') else []:
            desc = getattr(shot, 'description', '') or ''
            scene = getattr(shot, 'required_scene', '') or ''
            if len(desc) > 10:
                score += 0.3
            if scene:
                score += 0.3
        return min(10, max(3, score))

    def _score_platform_fit(self, script) -> float:
        """平台适配 (0-10)"""
        score = 6.0
        try:
            from adflow.engine.platform_style import PlatformStyle
            style = PlatformStyle.get_style(self.platform)
            if style:
                max_dur = style.get("max_duration_sec", 60) * 1000
                actual_dur = getattr(script, 'total_duration_ms', 30000)
                if actual_dur <= max_dur:
                    score += 2
                else:
                    score -= 2
        except Exception:
            pass
        return min(10, max(0, score))

    @staticmethod
    def _generate_suggestions(copy_s: float, struct_s: float, visual_s: float, plat_s: float) -> list[str]:
        """根据各维度得分生成改进建议"""
        tips = []
        if copy_s < 5:
            tips.append("文案吸引力偏低：尝试更强的钩子或更自然的CTA")
        if struct_s < 5:
            tips.append("结构节奏不足：建议调整镜头时长分布，避免单镜过长")
        if visual_s < 5:
            tips.append("视觉描述偏弱：为每个镜头补充更详细的画面描述")
        if plat_s < 5:
            tips.append("平台适配性不足：检查时长和风格是否符合目标平台")
        return tips


def build_score_summary(scores: list[CreativeScore]) -> str:
    """构建评分摘要文本（用于日志/GUI展示）"""
    if not scores:
        return "无评分数据"

    lines = ["## 创意预评分（预估表现）", ""]
    for i, s in enumerate(scores, 1):
        ctr_pct = s.ctr_estimate * 100
        lines.append(
            f"**#{i} 变体{s.variant_index}** — 综合 {s.total_score:.1f}/10 "
            f"| 预估CTR {ctr_pct:.2f}% | 置信度 {s.confidence:.0%}")
        lines.append(f"  文案{s.breakdown.get('copy_appeal',0):.1f} "
                     f"结构{s.breakdown.get('structure_rhythm',0):.1f} "
                     f"视觉{s.breakdown.get('visual_match',0):.1f} "
                     f"平台{s.breakdown.get('platform_fit',0):.1f}")
        if s.suggestions:
            for tip in s.suggestions[:2]:
                lines.append(f"  💡 {tip}")
    lines.append("")
    lines.append("> 冷启动阶段，预评分仅供参考。积累投放数据后准确度会提升。")
    return "\n".join(lines)
