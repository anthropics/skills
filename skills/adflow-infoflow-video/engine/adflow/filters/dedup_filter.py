# -*- coding: utf-8 -*-
"""
去重过滤器 — 检测新变体与已生成变体的相似度，打回过高的

与 CopyFilter._score_diversity 互补:
  - CopyFilter 做整体8维度评分（差异度是维度之一，权重10%）
  - DedupFilter 做专项相似度检测（可独立REJECT打回）
"""
from adflow.filters.base_filter import BaseFilter, FilterResult, Verdict
from adflow.engine.anti_dedup import AntiDedupEngine


class DedupFilter(BaseFilter):
    """去重专项过滤器"""

    def __init__(self, existing_scripts: list = None):
        super().__init__(
            name="去重检测",
            pass_threshold=7.0,
            warning_threshold=5.0,
            max_retries=2,
        )
        self.existing_scripts = existing_scripts or []

    def _evaluate(self, script, context: dict) -> FilterResult:
        """评估新脚本与已生成变体的差异度"""
        my_text = " ".join(s.narration_text or "" for s in script.shots)
        max_sim = 0.0
        max_idx = -1

        for idx, other in enumerate(self.existing_scripts):
            other_text = " ".join(
                s.narration_text or "" for s in other.shots)
            text_sim = AntiDedupEngine.compute_text_similarity(
                my_text, other_text)
            edit_sim = AntiDedupEngine.compute_edit_similarity(script, other)
            combined = text_sim * 0.6 + edit_sim * 0.4
            if combined > max_sim:
                max_sim = combined
                max_idx = idx

        # 相似度→评分
        if max_sim < 0.30:
            score = 10.0
            label = "差异度足够"
        elif max_sim < 0.50:
            score = 7.0 + (0.50 - max_sim) / 0.20 * 3.0
            label = "差异度可接受"
        elif max_sim < 0.70:
            score = 4.0 + (0.70 - max_sim) / 0.20 * 3.0
            label = "差异度偏低"
        else:
            score = max(0, 4.0 - (max_sim - 0.70) / 0.30 * 4.0)
            label = "过于相似"

        issues = []
        suggestions = []
        if max_sim > 0.50:
            issues.append(f"与变体#{max_idx}相似度{max_sim:.0%}")
            suggestions.extend([
                "同义词替换关键短语",
                "调整句式（疑问→陈述→感叹）",
                "改变叙事顺序（正叙→倒叙）",
            ])

        # similarity > 70% → REJECT 真拦截
        verdict = Verdict.REJECT if max_sim > 0.70 else Verdict.PASS
        return FilterResult(
            verdict=verdict,
            score=score,
            sub_scores={
                "text_similarity": (1 - max_sim) * 10,
                "edit_pattern": (1 - max_sim * 0.5) * 10,
            },
            issues=issues,
            suggestions=suggestions,
        )
