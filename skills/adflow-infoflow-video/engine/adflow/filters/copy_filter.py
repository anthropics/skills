# -*- coding: utf-8 -*-
"""
文案质量过滤器 — 8维度评分 + 打回重试带反馈

维度:
  1. hook_strength      — 开头吸引力
  2. oral_quality       — 口语化程度
  3. info_density       — 信息密度
  4. cta_strength       — CTA力度
  5. subtitle_diff      — 字幕与旁白差异度
  6. segment_quality    — 分段质量
  7. structure          — 分镜结构完整性
  8. diversity          — 与其他变体的差异度
"""
import json as _json
import logging
from typing import Any

from adflow.filters.base_filter import BaseFilter, FilterResult, Verdict, weighted_total

logger = logging.getLogger("adflow.filters.copy")


class CopyFilter(BaseFilter):
    """文案质量过滤器"""

    def __init__(self):
        super().__init__(
            name="文案过滤",
            pass_threshold=6.5,
            warning_threshold=4.5,
            max_retries=2,
        )

    def _evaluate(self, script: Any, context: dict) -> FilterResult:
        """评估单个 StoryboardScript 的质量"""
        sub_scores = {}
        issues = []
        suggestions = []

        # 1. Hook 吸引力
        hook = script.shots[0] if script.shots else None
        hook_text = hook.narration_text if hook else ""
        sub_scores["hook_strength"] = self._score_hook(hook_text)
        if sub_scores["hook_strength"] < 5:
            issues.append(f"开头吸引力不足: '{hook_text[:20]}'")
            suggestions.append("尝试用疑问句/数据/反常识/场景代入开头")

        # 2. 口语化程度
        all_narration = " ".join(
            s.narration_text or "" for s in script.shots)
        sub_scores["oral_quality"] = self._score_oral(all_narration)
        if sub_scores["oral_quality"] < 5:
            issues.append("文案过于书面化")
            suggestions.append("加入'真的''特别''太''超'等口语词")

        # 3. 信息密度
        sub_scores["info_density"] = self._score_density(script)
        if sub_scores["info_density"] < 5:
            issues.append("信息密度低，存在套话废话")
            suggestions.append("删除'今天给大家推荐'等套话，加入具体数据和利益点")

        # 4. CTA 力度
        cta_shot = [s for s in script.shots if s.role == "cta"]
        if cta_shot:
            cta_text = cta_shot[0].narration_text or script.cta_text or ""
            sub_scores["cta_strength"] = self._score_cta(cta_text)
            if sub_scores["cta_strength"] < 5:
                issues.append("CTA力度不足")
                suggestions.append("加入行动动词(下单/抢/立即)+紧迫感(限时/手慢/仅剩)")
        else:
            sub_scores["cta_strength"] = 0
            issues.append("缺少CTA镜头")

        # 5. 分段质量
        sub_scores["segment_quality"] = self._score_segments(script)
        if sub_scores["segment_quality"] < 5:
            issues.append("narration_segments 分段不合理")
            suggestions.append("每段8-20字，在语义边界处断句")

        # 6. 结构完整性
        sub_scores["structure"] = self._score_structure(script)
        if sub_scores["structure"] < 5:
            issues.append("分镜结构不完整")
            suggestions.append("确保包含 hook→problem→solution→demo→cta 五段")

        # 7. 变体差异度
        other_scripts = context.get("other_scripts", [])
        if other_scripts:
            sub_scores["diversity"] = self._score_diversity(script, other_scripts)
            if sub_scores["diversity"] < 5:
                issues.append("与其他变体相似度过高")
                suggestions.append("使用不同的开头类型和叙事角度")
        else:
            sub_scores["diversity"] = 8.0

        # ── 去AI感检测（7大死亡气味）──
        from adflow.filters.ai_smell_detector import AISmellDetector
        ai_smell = AISmellDetector().detect(all_narration)
        if ai_smell.total_hits > 0:
            issues.append(f"AI感: {ai_smell.summary}")
            for s in ai_smell.suggestions[:3]:
                suggestions.append(s)
        if ai_smell.needs_rewrite:
            issues.append(f"AI感过重({ai_smell.total_hits}/7项命中)，建议重写")
            sub_scores["ai_smell_penalty"] = -2.0

        # ── 新增: 字数硬约束 ──
        sub_scores["length_check"] = self._score_length(script)
        if sub_scores["length_check"] < 3:
            issues.append(f"文案字数不足(仅{len(all_narration)}字)，需要120-150字")

        # ── 新增: 场景化程度 ──
        sub_scores["scene_coverage"] = self._score_scene_coverage(script)
        if sub_scores["scene_coverage"] < 4:
            issues.append("文案缺场景化描述，像说明书")
            suggestions.append("每个卖点加场景→使用→效果")

        # ── 新增: 情绪曲线 ──
        sub_scores["emotion_curve"] = self._score_emotion_curve(script)
        if sub_scores["emotion_curve"] < 4:
            issues.append("文案情绪平淡，从头到尾一个调")
            suggestions.append("情绪要有起伏：好奇→共鸣→紧迫")

        # 加权综合（钩子是生死线，情绪起伏是爆款特征，已归一化）
        weights = {
            "hook_strength": 0.27,      # 前3秒决定70%+完播率
            "oral_quality": 0.09,
            "info_density": 0.09,
            "cta_strength": 0.11,
            "segment_quality": 0.12,
            "structure": 0.05,
            "diversity": 0.05,
            "length_check": 0.05,
            "scene_coverage": 0.07,
            "emotion_curve": 0.10,      # 情绪起伏是爆款核心特征
        }
        total = weighted_total(sub_scores, weights)
        # AI感惩罚
        if "ai_smell_penalty" in sub_scores:
            total += sub_scores["ai_smell_penalty"]
            total = max(0, total)

        # < 5.5 → REJECT 真拦截
        verdict = Verdict.REJECT if total < 5.5 else Verdict.PASS
        return FilterResult(
            verdict=verdict,
            score=total,
            sub_scores=sub_scores,
            issues=issues,
            suggestions=suggestions,
        )

    # ── 评分函数 ──

    @staticmethod
    def _score_hook(text: str) -> float:
        """开头吸引力评分 (0-10)"""
        if not text:
            return 0
        score = 5.0
        if any(c in text for c in "？？?"):
            score += 2
        if any(c.isdigit() for c in text):
            score += 1
        if any(w in text for w in ["竟然", "居然", "没想到", "其实", "90%"]):
            score += 2
        # 套路扣分
        for w in ["今天给大家", "为大家推荐", "大家好", "这款产品"]:
            if w in text:
                score -= 3
                break
        # 长度
        if len(text) > 25:
            score -= 1
        elif len(text) <= 15:
            score += 1
        return max(0, min(10, score))

    @staticmethod
    def _score_oral(text: str) -> float:
        """口语化评分 (0-10)"""
        if not text:
            return 0
        score = 6.0
        written_marks = ["因此", "然而", "此外", "综上所述", "总而言之", "值得注意", "不可忽视"]
        for mark in written_marks:
            if mark in text:
                score -= 1
        oral_marks = ["真的", "特别", "太", "超", "绝了", "冲", "抢", "贼", "老"]
        for mark in oral_marks:
            if mark in text:
                score += 1
        return max(0, min(10, score))

    @staticmethod
    def _score_density(script) -> float:
        """信息密度评分 (0-10)"""
        score = 6.0
        all_text = " ".join(s.narration_text or "" for s in script.shots)
        waste_marks = [
            "今天给大家", "为大家推荐", "大家好",
            "这款产品真的很好用", "点击下方链接了解更多", "希望大家喜欢",
        ]
        for mark in waste_marks:
            if mark in all_text:
                score -= 2
        # 具体数字加分
        import re
        numbers = re.findall(r'\d+', all_text)
        if len(numbers) >= 2:
            score += 2
        return max(0, min(10, score))

    @staticmethod
    def _score_cta(text: str) -> float:
        """CTA力度评分 (0-10)"""
        if not text:
            return 0
        score = 3.0
        for w in ["下单", "点击", "抢", "立即", "马上", "赶紧"]:
            if w in text:
                score += 1
        for w in ["限时", "仅剩", "手慢", "今天", "现在", "立减", "买二送一"]:
            if w in text:
                score += 1
        return max(0, min(10, score))

    @staticmethod
    def _score_segments(script) -> float:
        """分段质量评分 (0-10)"""
        all_lens = []
        for shot in script.shots:
            segs_raw = shot.narration_segments or ""
            try:
                segs = _json.loads(segs_raw) if segs_raw else []
            except (_json.JSONDecodeError, TypeError):
                segs = []
            all_lens.extend(len(s) for s in segs if isinstance(s, str))

        if not all_lens:
            return 3

        in_range = sum(1 for l in all_lens if 8 <= l <= 20)
        ratio = in_range / len(all_lens)

        too_short = sum(1 for l in all_lens if l < 5)
        too_long = sum(1 for l in all_lens if l > 25)
        penalty = (too_short + too_long) * 0.5

        return max(0, min(10, ratio * 10 - penalty))

    @staticmethod
    def _score_structure(script) -> float:
        """结构完整性评分 (0-10)"""
        required = {"hook", "problem", "solution", "product_demo", "cta"}
        actual = {s.role for s in script.shots}
        coverage = len(required & actual) / len(required)
        return coverage * 10

    @staticmethod
    def _score_length(script) -> float:
        """字数评分: 120-150字=满分, <80字=0分, >200字=5分"""
        total = len("".join(s.narration_text or "" for s in script.shots))
        if 120 <= total <= 150:
            return 10
        if 100 <= total <= 160:
            return 8
        if 80 <= total <= 180:
            return 5
        if total < 80:
            return max(0, total / 20)  # 80字以下线性递减
        return 5

    @staticmethod
    def _score_scene_coverage(script) -> float:
        """场景化评分: 检测是否有场景+使用+效果描述"""
        score = 3.0
        for shot in script.shots:
            text = (shot.narration_text or "") + (shot.description or "")
            # 有场景词
            if any(w in text for w in ["的时候", "出门", "早上", "下班", "在家", "办公室"]):
                score += 1.5
            # 有使用方式
            if any(w in text for w in ["拿出来", "按两下", "吃两颗", "涂上去", "打开"]):
                score += 1.0
            # 有效果描述
            if any(w in text for w in ["就能", "就会", "之后", "感觉", "发现"]):
                score += 1.0
        return min(10, score)

    @staticmethod
    def _score_emotion_curve(script) -> float:
        """情绪曲线评分: 情绪有变化才得分"""
        emotions = [getattr(s, 'required_emotion', '') or '' for s in script.shots]
        unique = len(set(e for e in emotions if e))
        if unique >= 3:
            return 10
        if unique == 2:
            return 7
        if unique == 1:
            return 3
        return 0

    @staticmethod
    def _score_diversity(script, others: list) -> float:
        """与变体间的差异度 (0-10)"""
        if not others:
            return 10

        my_text = " ".join(s.narration_text or "" for s in script.shots)
        my_chars = set(my_text)

        overlaps = []
        for other in others:
            other_text = " ".join(
                s.narration_text or "" for s in other.shots)
            other_chars = set(other_text)
            union = my_chars | other_chars
            if union:
                overlaps.append(len(my_chars & other_chars) / len(union))

        if not overlaps:
            return 10
        return (1 - sum(overlaps) / len(overlaps)) * 10
