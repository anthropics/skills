# -*- coding: utf-8 -*-
"""
过滤模型基类 — 所有环节质量验收器的统一框架

判定:
  ✅ PASS    — 质量分≥阈值，直接进入下一环节
  ⚠️ WARNING — 质量分在边缘区间，带标记通过
  ❌ REJECT  — 质量分<最低阈值，可重试（最多N次）
  💀 FATAL   — 重试耗尽仍不达标，标记为废品
"""
from dataclasses import dataclass, field
from enum import Enum
from typing import Any


class Verdict(Enum):
    """过滤判定结果"""
    PASS = "pass"           # ✅ 通过
    WARNING = "warning"     # ⚠️ 警告（带标记通过）
    REJECT = "reject"       # ❌ 打回重做
    FATAL = "fatal"         # 💀 拒绝（重试耗尽）


@dataclass
class FilterResult:
    """过滤模型输出"""
    verdict: Verdict
    score: float                        # 0-10 综合分
    sub_scores: dict[str, float] = field(default_factory=dict)  # 各维度得分
    issues: list[str] = field(default_factory=list)            # 发现的问题
    suggestions: list[str] = field(default_factory=list)       # 改进建议
    retry_count: int = 0                # 当前重试次数
    max_retries: int = 2                # 最大重试次数

    @property
    def should_retry(self) -> bool:
        """是否应该重试"""
        return self.verdict == Verdict.REJECT and self.retry_count < self.max_retries

    @property
    def is_terminal(self) -> bool:
        """是否终态（不可重试）"""
        return self.verdict in (Verdict.PASS, Verdict.WARNING, Verdict.FATAL)

    @property
    def is_ok(self) -> bool:
        """是否可继续（通过或警告）"""
        return self.verdict in (Verdict.PASS, Verdict.WARNING)

    @property
    def label(self) -> str:
        """判定标签"""
        labels = {
            Verdict.PASS: "✅ PASS",
            Verdict.WARNING: "⚠️ WARN",
            Verdict.REJECT: "❌ REJECT",
            Verdict.FATAL: "💀 FATAL",
        }
        return labels.get(self.verdict, "? UNKNOWN")

    def summary(self, name: str = "") -> str:
        """单行摘要"""
        dims = ", ".join(
            f"{k}={v:.1f}" for k, v in sorted(self.sub_scores.items()))
        header = f"[{name}] " if name else ""
        return f"{header}{self.label} {self.score:.1f}/10 ({dims})"


class BaseFilter:
    """过滤模型基类 — 所有环节的质量验收器继承此类

    子类需要实现:
      - _evaluate(data, context) → FilterResult: 核心评估逻辑
    """

    def __init__(self, name: str, pass_threshold: float = 7.0,
                 warning_threshold: float = 5.0, max_retries: int = 2):
        self.name = name
        self.pass_threshold = pass_threshold
        self.warning_threshold = warning_threshold
        self.max_retries = max_retries

    def evaluate(self, data: Any, context: dict | None = None) -> FilterResult:
        """评估入口 — 调用子类 _evaluate，以子类 verdict 为准

        子类在 _evaluate 内已根据自身业务阈值给出 verdict（如 copy 的 5.5、
        dedup 的 0.70），基类不得再按 score 覆盖，否则会：① 把子类的 REJECT
        软化成 WARNING 放行；② 把子类的 PASS 硬判成 REJECT。
        """
        ctx = context if isinstance(context, dict) else {}
        result = self._evaluate(data, ctx)
        result.retry_count = ctx.get("retry_count", 0)
        result.max_retries = self.max_retries
        return result

    def _evaluate(self, data: Any, context: dict) -> FilterResult:
        """子类实现：评估数据质量"""
        raise NotImplementedError(f"{self.name} 未实现 _evaluate()")

    def run_with_retry(self, generator, data: Any,
                       context: dict | None = None) -> tuple[Any, FilterResult]:
        """带重试的生成+过滤循环

        Args:
            generator: 可调用对象，接受 (data, context)，返回新的生成结果
            data: 初始输入数据
            context: 上下文（包含重试计数等）

        Returns:
            (最终生成结果, 最终过滤结果)
        """
        ctx = context or {}
        current_data = data

        for attempt in range(self.max_retries + 1):
            ctx["retry_count"] = attempt

            # 如果是重试，用 generator 重新生成
            if attempt > 0:
                try:
                    current_data = generator(data, ctx)
                except Exception as e:
                    result = FilterResult(
                        verdict=Verdict.FATAL,
                        score=0,
                        issues=[f"重试生成失败: {e}"],
                    )
                    return current_data, result

            # 评估
            result = self.evaluate(current_data, ctx)

            if result.is_terminal:
                return current_data, result

            # REJECT → 准备重试，把问题反馈给 generator
            ctx["previous_issues"] = result.issues
            ctx["previous_suggestions"] = result.suggestions

        # 重试耗尽
        result.verdict = Verdict.FATAL
        return current_data, result


def clamp_score(value: float, min_val: float = 0, max_val: float = 10) -> float:
    """夹紧分数在范围内"""
    return max(min_val, min(max_val, value))


def weighted_total(sub_scores: dict[str, float],
                   weights: dict[str, float]) -> float:
    """加权总分"""
    total = 0.0
    for k, w in weights.items():
        total += sub_scores.get(k, 5.0) * w
    return clamp_score(total)
