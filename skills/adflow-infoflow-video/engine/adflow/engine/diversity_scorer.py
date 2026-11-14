# -*- coding: utf-8 -*-
"""
文案多样性竞价算法 — 结构签名 + 竞价评分 + 定向重试

基线 0 分，6维结构签名独立评分，<60 分触发定向重试
跨批次持久化，按品类分库，换品自动切换
"""
import logging
from adflow.engine.signature_extractor import (
    extract_signature, Signature, signature_distance,
    DIMENSION_NAMES, DIMENSION_SUGGESTIONS,
)
from adflow.engine.signature_history import SignatureHistory

logger = logging.getLogger("adflow.bidding")

# 6维权重
DIM_WEIGHTS = {
    "sentence_pattern": 0.25,
    "emotion_curve": 0.20,
    "role_sequence": 0.15,
    "narrative_pov": 0.15,
    "transition_type": 0.15,
    "duration_bucket": 0.10,
}


class DiversityScorer:
    """文案多样性竞价评分器"""

    def __init__(self, category: str = "通用"):
        self.history = SignatureHistory(category)

    def score_batch(self, scripts: list, max_score: float = 100.0) -> dict:
        """对一批脚本竞价评分

        Returns: {score, passed, details, feedback}
        """
        if not scripts:
            return {"score": 0, "passed": False, "details": [], "feedback": "空脚本列表", "low_items": []}
        if len(scripts) < 2:
            return {"score": 100, "passed": True, "details": [], "feedback": "", "low_items": []}

        # 1. 提取签名
        sigs = [extract_signature(s) for s in scripts]

        # 2. 逐条评分
        details = []
        low_items = []
        for i, sig in enumerate(sigs):
            novelty = _score_novelty(sig, sigs, i)
            repeat = _penalty_repeat(sig, self.history)
            coverage = _score_coverage(sig, sigs, i)
            hist_diff = _score_history_diff(sig, self.history)
            total = novelty + coverage + hist_diff - repeat

            detail = {
                "variant_index": i,
                "novelty": round(novelty, 1),
                "repeat_penalty": round(repeat, 1),
                "coverage": round(coverage, 1),
                "history_diff": round(hist_diff, 1),
                "score": round(max(0, total), 1),
            }
            details.append(detail)

            if detail["score"] < 70:
                diagnosis = _diagnose(sig, sigs, self.history)
                detail["diagnosis"] = diagnosis
                low_items.append(detail)

        # 3. 总分 = 各条最低分（一票否决）
        batch_score = min(d["score"] for d in details) if details else 100
        passed = batch_score >= 70

        # 4. 构建反馈
        feedback = ""
        if not passed:
            feedback = _build_feedback(low_items)

        return {
            "score": batch_score,
            "passed": passed,
            "details": details,
            "feedback": feedback,
            "low_items": low_items,
        }

    def add_to_history(self, scripts: list):
        """通过的脚本写入历史库"""
        for s in scripts:
            try:
                sig = extract_signature(s)
                self.history.add(
                    sig,
                    script_id=getattr(s, 'script_id', ''),
                    product_name=getattr(s, 'product_name', ''),
                    score=80,
                )
            except Exception:
                pass
        self.history.decay_old()


# ── 评分函数 ──

def _score_novelty(sig: Signature, batch: list[Signature], idx: int) -> float:
    """原创性: 批内唯一 → 40分，碰撞 → -15/次"""
    dup = sum(1 for s in batch if s == sig) - 1
    return max(0, 40.0 - dup * 15.0)


def _penalty_repeat(sig: Signature, history: SignatureHistory) -> float:
    """历史碰撞惩罚: -15/次"""
    return history.count_collisions(sig) * 15.0


def _score_coverage(sig: Signature, batch: list[Signature], idx: int) -> float:
    """维度覆盖: 6个维度与其他文案的差异比例"""
    others = [s for i, s in enumerate(batch) if i != idx]
    if not others:
        return 40.0
    total = 0.0
    for dim, w in DIM_WEIGHTS.items():
        my_val = getattr(sig, dim)
        diff = sum(1 for o in others if getattr(o, dim) != my_val)
        total += (diff / len(others)) * w * 40
    return round(total, 1)


def _score_history_diff(sig: Signature, history: SignatureHistory) -> float:
    """历史差异: 与最近200条的最小距离 → 分数"""
    recent = history.get_recent(200)
    if not recent:
        return 20.0
    dists = [signature_distance(sig, h) for h in recent]
    min_d = min(dists)
    avg_d = sum(dists) / len(dists)
    return round((min_d * 0.7 + avg_d * 0.3) * 20, 1)


# ── 诊断 + 反馈 ──

def _diagnose(sig: Signature, batch: list[Signature],
              history: SignatureHistory) -> str:
    """诊断低分原因"""
    issues = []
    for dim in DIM_WEIGHTS:
        my_val = getattr(sig, dim)
        # 批内碰撞
        batch_dup = sum(1 for s in batch if getattr(s, dim) == my_val) - 1
        if batch_dup > 0:
            issues.append(
                f"{DIMENSION_NAMES[dim]}: 与批内{batch_dup}条相同"
                f" → {DIMENSION_SUGGESTIONS[dim]}")
    if not issues:
        return "整体结构需要调整，建议改变叙事节奏和情绪走向"
    return "\n".join(issues[:3])


def _build_feedback(low_items: list[dict]) -> str:
    """构建定向重试反馈"""
    lines = ["## ⚠️ 多样性不足，定向调整：", ""]
    for item in low_items[:3]:
        lines.append(f"变体{item['variant_index']}({item['score']:.0f}分):")
        lines.append(item.get("diagnosis", ""))
        lines.append("")
    return "\n".join(lines)
