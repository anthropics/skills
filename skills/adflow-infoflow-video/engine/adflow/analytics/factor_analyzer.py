# -*- coding: utf-8 -*-
"""因子相关性分析 — 类比量化 ParameterAnalyzer

分析各因子与爆款的相关性，识别高估/低估因子，生成优化建议。
"""

from datetime import datetime
from typing import Optional

import numpy as np

from adflow.db.analytics_repo import AnalyticsRepo, LABEL_HIT
from adflow.analytics.factor_types import FactorBenchmark, FactorReport


class FactorAnalyzer:
    """因子分析器 — 无模型依赖，纯统计分析"""

    def __init__(self, repo: Optional[AnalyticsRepo] = None):
        self.repo = repo or AnalyticsRepo()

    def analyze(self, model=None) -> FactorReport:
        """主分析入口。

        Args:
            model: AestheticModel 实例（可选，提供特征重要性）

        Returns:
            FactorReport 含各因子的基准区间 + 建议
        """
        hits = self.repo.get_labels_with_factors(limit=500)
        if len(hits) < 10:
            return FactorReport(sample_count=len(hits))

        report = FactorReport(
            sample_count=len(hits),
            hit_count=sum(1 for h in hits if h.label == LABEL_HIT),
            generated_at=datetime.now().isoformat(),
        )

        # 提取所有因子向量
        factor_vectors = []
        labels = []
        for h in hits:
            if h.factors:
                factor_vectors.append(h.factors.to_vector())
                labels.append(1.0 if h.label == LABEL_HIT else 0.0)

        if not factor_vectors:
            return report

        X = np.array(factor_vectors)
        y = np.array(labels)

        # 特征重要性（从模型获取，或从相关性推断）
        importance = {}
        if model is not None and model.loaded:
            for name, imp in model.feature_importance():
                importance[name] = imp

        # 因子名
        names = self._get_factor_names()

        # 对每个因子计算统计量
        benchmarks = []
        for i, name in enumerate(names):
            if i >= X.shape[1]:
                break

            hit_vals = X[y == 1, i] if y.sum() > 0 else np.array([])
            normal_vals = X[y == 0, i]

            imp = importance.get(name, self._correlation_importance(X[:, i], y))

            bm = FactorBenchmark(
                name=name,
                hit_mean=round(float(np.mean(hit_vals)), 4) if len(hit_vals) > 0 else 0,
                hit_std=round(float(np.std(hit_vals)), 4) if len(hit_vals) > 1 else 0,
                hit_min=round(float(np.min(hit_vals)), 4) if len(hit_vals) > 0 else 0,
                hit_max=round(float(np.max(hit_vals)), 4) if len(hit_vals) > 0 else 0,
                importance=round(imp, 4),
                recommendation=self._make_recommendation(
                    name, hit_vals, normal_vals),
            )
            benchmarks.append(bm)

        benchmarks.sort(key=lambda b: b.importance, reverse=True)
        report.benchmarks = benchmarks
        report.top_factors = [b.name for b in benchmarks[:10]]

        # 模型准确率
        if model is not None and model.loaded:
            report.model_accuracy = 0.0  # 由外部设置

        return report

    # ── 内部 ──

    @staticmethod
    def _correlation_importance(factor_vals: np.ndarray,
                                labels: np.ndarray) -> float:
        """用相关系数估算因子重要性"""
        if len(factor_vals) < 3:
            return 0.0
        # Spearman rank correlation
        n = len(factor_vals)
        def _rank(v):
            order = np.argsort(v)
            ranks = np.zeros(n)
            for r, idx in enumerate(order):
                ranks[idx] = r
            return ranks

        rx = _rank(factor_vals)
        ry = _rank(labels)
        mean_rx, mean_ry = np.mean(rx), np.mean(ry)
        cov = np.sum((rx - mean_rx) * (ry - mean_ry))
        std_x = np.sqrt(np.sum((rx - mean_rx) ** 2))
        std_y = np.sqrt(np.sum((ry - mean_ry) ** 2))
        if std_x == 0 or std_y == 0:
            return 0.0
        r = cov / (std_x * std_y)
        return abs(float(r))

    @staticmethod
    def _make_recommendation(name: str, hit_vals: np.ndarray,
                             normal_vals: np.ndarray) -> str:
        """根据爆款vs普通视频的因子差异生成优化建议"""
        if len(hit_vals) < 3 or len(normal_vals) < 3:
            return "样本不足，暂无法给出建议"

        hit_m = np.mean(hit_vals)
        normal_m = np.mean(normal_vals)
        diff_pct = (hit_m - normal_m) / max(abs(normal_m), 1e-6) * 100

        if abs(diff_pct) < 10:
            return f"差异不显著({diff_pct:+.0f}%)，非关键因子"

        direction = "更高" if diff_pct > 0 else "更低"
        return f"爆款{name}比普通{direction}{abs(diff_pct):.0f}%"

    @staticmethod
    def _get_factor_names() -> list[str]:
        return [
            "avg_shot_duration", "shot_count", "shot_duration_variance",
            "cut_speed", "tempo_bpm",
            "peak_emotion_position", "emotion_volatility", "emotion_energy",
            "brightness_mean", "brightness_variance", "color_saturation",
            "scene_change_rate", "motion_intensity",
            "words_per_second", "keyword_density", "cta_position_ratio",
            "sentence_length_avg", "question_ratio", "power_word_count",
            "voice_gender", "voice_speed", "bgm_energy",
            "voice_bgm_match", "has_bgm",
            "hook_ratio", "product_intro_time", "cta_duration",
            "total_duration", "shot_role_diversity", "padding",
        ]
