# -*- coding: utf-8 -*-
"""XGBoost 审美模型 — 预测视频爆款概率（类比量化 signal_optimizer）

训练: 因子向量 → hit/not-hit 二分类
预测: 新脚本因子 → 0-1 爆款概率
特征重要性: 哪些因子最影响爆款
"""

import json
import logging
import os
import time
from dataclasses import dataclass, field

import numpy as np

from adflow.db.analytics_repo import AnalyticsRepo

_log = logging.getLogger("adflow.aesthetic")

MIN_SAMPLES = 20          # 最少标注数才训练
FEATURE_DIM = 30          # 因子向量维度
HIT_THRESHOLD = 0.6       # 爆款概率阈值


@dataclass
class TrainResult:
    """训练结果"""
    sample_count: int = 0
    hit_count: int = 0
    baseline_hit_rate: float = 0.0
    accuracy: float = 0.0
    auc: float = 0.0
    cv_std: float = 0.0
    feature_importance: list[tuple[str, float]] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    train_time_ms: float = 0.0


class AestheticModel:
    """XGBoost 审美模型"""

    def __init__(self, model_path: str = ""):
        self._model = None
        self._model_path = model_path
        self._loaded = False
        self._factor_names: list[str] = []

        if not model_path:
            root = os.path.dirname(os.path.dirname(os.path.dirname(
                os.path.abspath(__file__))))
            self._model_path = os.path.join(root, "data", "aesthetic_model.json")

    @property
    def loaded(self) -> bool:
        return self._loaded and self._model is not None

    # ── 训练 ──

    def train(self, db=None, progress_callback=None) -> TrainResult:
        """从 hit_labels + factor_snapshots 训练模型"""
        t0 = time.time()

        if db is None:
            repo = AnalyticsRepo()
        else:
            repo = db if isinstance(db, AnalyticsRepo) else AnalyticsRepo()

        result = TrainResult()

        # 1. 提取训练数据
        try:
            X, y = repo.get_training_data(limit=500)
        except Exception as e:
            result.errors.append(f"数据提取失败: {e}")
            return result

        if len(y) < MIN_SAMPLES * 2:
            result.errors.append(
                f"样本不足 ({len(y)} < {MIN_SAMPLES * 2}), "
                f"需要至少 {MIN_SAMPLES * 2} 条标注数据"
            )
            return result

        result.sample_count = len(y)
        result.hit_count = int(sum(y))
        result.baseline_hit_rate = float(np.mean(y))

        # 2. 检查 xgboost
        try:
            import xgboost as xgb
        except ImportError:
            result.errors.append("xgboost 未安装: pip install xgboost")
            return result

        X = np.array(X, dtype=float)
        y = np.array(y, dtype=float)

        # 3. 处理类别不平衡
        hit_count = y.sum()
        if hit_count > 0 and hit_count < len(y):
            pos_weight = (len(y) - hit_count) / hit_count
        else:
            pos_weight = 1.0

        # 4. 交叉验证
        _log.info("训练审美模型: %d 样本, %d 爆款", len(y), int(hit_count))
        self._report(progress_callback, f"训练审美模型: {len(y)}样本...")

        try:
            dtrain = xgb.DMatrix(X, label=y)
            cv_params = {
                "max_depth": 4,
                "eta": 0.05,
                "objective": "binary:logistic",
                "eval_metric": "auc",
                "scale_pos_weight": pos_weight,
                "subsample": 0.8,
                "colsample_bytree": 0.8,
            }
            cv_result = xgb.cv(
                cv_params, dtrain, num_boost_round=200,
                nfold=min(5, int(len(y) / 5)),
                early_stopping_rounds=20,
                verbose_eval=False, seed=42,
            )
            best_rounds = len(cv_result)
            result.auc = float(cv_result["test-auc-mean"].iloc[-1])
            result.cv_std = float(cv_result["test-auc-std"].iloc[-1])
        except Exception as e:
            _log.warning("CV失败: %s, 用默认参数", e)
            best_rounds = 100
            result.auc = 0.5

        # 5. 全量训练
        self._model = xgb.train(cv_params, dtrain, num_boost_round=best_rounds)
        self._loaded = True

        # 6. 特征重要性
        importance = self._model.get_score(importance_type="gain")
        sorted_imp = sorted(importance.items(), key=lambda x: x[1], reverse=True)

        # 因子名映射
        self._factor_names = self._get_factor_names()
        named_imp = []
        for fkey, score in sorted_imp[:15]:
            try:
                idx = int(fkey.replace("f", ""))
                name = self._factor_names[idx] if idx < len(self._factor_names) else fkey
            except (ValueError, IndexError):
                name = fkey
            named_imp.append((name, round(score, 1)))
        result.feature_importance = named_imp

        # 7. 准确率
        preds = self._model.predict(dtrain)
        pred_labels = (preds >= HIT_THRESHOLD).astype(int)
        result.accuracy = float((pred_labels == y).mean())

        result.train_time_ms = (time.time() - t0) * 1000

        self._report(progress_callback,
                     f"训练完成 AUC={result.auc:.3f} "
                     f"准确率={result.accuracy:.1%} "
                     f"耗时{result.train_time_ms:.0f}ms")

        return result

    # ── 预测 ──

    def predict(self, factors, as_vector: bool = False) -> float:
        """预测爆款概率 0-1

        Args:
            factors: VideoFactors 对象 或 30维 list
            as_vector: True=factors是list, False=VideoFactors对象
        """
        if not self.loaded:
            return 0.5

        try:
            import xgboost as xgb
            if as_vector:
                vec = np.array(factors, dtype=float)
            else:
                vec = np.array(factors.to_vector(), dtype=float)

            if len(vec) < FEATURE_DIM:
                vec = np.pad(vec, (0, FEATURE_DIM - len(vec)))
            vec = vec[:FEATURE_DIM]

            dmat = xgb.DMatrix(vec.reshape(1, -1))
            proba = float(self._model.predict(dmat)[0])
            return proba
        except Exception as e:
            _log.warning("预测失败: %s", e)
            return 0.5

    # ── 特征重要性 ──

    def feature_importance(self) -> list[tuple[str, float]]:
        """返回 (因子名, 重要性) 排序"""
        if not self.loaded:
            return []
        importance = self._model.get_score(importance_type="gain")
        sorted_imp = sorted(importance.items(), key=lambda x: x[1], reverse=True)
        result = []
        for fkey, score in sorted_imp[:15]:
            try:
                idx = int(fkey.replace("f", ""))
                name = self._factor_names[idx] if idx < len(self._factor_names) else fkey
            except (ValueError, IndexError):
                name = fkey
            result.append((name, round(score, 1)))
        return result

    # ── 保存/加载 ──

    def save(self, path: str = ""):
        if not self.loaded:
            return
        save_path = path or self._model_path
        if not save_path:
            return
        try:
            os.makedirs(os.path.dirname(save_path), exist_ok=True)
            self._model.save_model(save_path)
            _log.info("审美模型已保存: %s", save_path)
        except Exception as e:
            _log.warning("模型保存失败: %s", e)

    def load(self, path: str = "") -> bool:
        load_path = path or self._model_path
        if not load_path or not os.path.exists(load_path):
            return False
        try:
            import xgboost as xgb
            self._model = xgb.Booster()
            self._model.load_model(load_path)
            self._loaded = True
            self._model_path = load_path
            self._factor_names = self._get_factor_names()
            _log.info("审美模型已加载: %s", load_path)
            return True
        except Exception as e:
            _log.warning("模型加载失败: %s", e)
            return False

    # ── 内部 ──

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

    @staticmethod
    def _report(callback, msg: str):
        if callback:
            try:
                callback(msg)
            except Exception:
                pass
