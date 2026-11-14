# -*- coding: utf-8 -*-
"""
角度使用历史库 — 按产品持久化，指数衰减降权

规则:
  未使用:     weight = 1.0 (100%)
  使用1次:    weight = 0.3
  使用2次:    weight = 0.09
  使用3次+:   weight = 0.01
  24h冷却期内: weight = 0.0
"""
import json
import os
from datetime import datetime, timedelta


class AngleHistory:
    """角度历史 — 按产品分文件"""

    DECAY_BASE = 0.3
    COOLDOWN_HOURS = 24
    MAX_PER_PRODUCT = 200

    def __init__(self, product_id: str = "", product_name: str = ""):
        self.product_id = product_id or "default"
        self.product_name = product_name
        self._dir = os.path.join(
            os.path.dirname(__file__), "..", "data", "angle_history")
        os.makedirs(self._dir, exist_ok=True)
        self._angles: dict[str, dict] = {}
        self._load()

    @property
    def _path(self) -> str:
        return os.path.join(self._dir, f"{self.product_id}.json")

    def get_weight(self, angle_key: str) -> float:
        """获取角度当前权重"""
        if angle_key not in self._angles:
            return 1.0
        a = self._angles[angle_key]
        # 冷却期内 = 0
        if a.get("cooldown_until"):
            try:
                until = datetime.fromisoformat(a["cooldown_until"])
                if datetime.now() < until:
                    return 0.0
            except Exception:
                pass
        use_count = a.get("use_count", 0)
        if use_count == 0:
            return 1.0
        w = self.DECAY_BASE ** use_count
        # 投放效果好的适当回选
        perf = a.get("performance_score", 0)
        if perf > 0:
            w *= (1 + perf * 0.5)
        return round(w, 4)

    def mark_used(self, angle_key: str, selling_point: str = "",
                  audience: str = "", script_id: str = ""):
        """标记角度已使用"""
        if angle_key in self._angles:
            self._angles[angle_key]["use_count"] += 1
        else:
            self._angles[angle_key] = {
                "angle_key": angle_key,
                "selling_point": selling_point,
                "audience": audience,
                "use_count": 1,
                "performance_score": 0.0,
            }
        self._angles[angle_key]["last_used_at"] = datetime.now().isoformat()
        self._angles[angle_key]["cooldown_until"] = (
            datetime.now() + timedelta(hours=self.COOLDOWN_HOURS)
        ).isoformat()
        # 限制大小
        if len(self._angles) > self.MAX_PER_PRODUCT:
            sorted_items = sorted(
                self._angles.items(),
                key=lambda x: x[1].get("use_count", 0))
            self._angles = dict(sorted_items[-self.MAX_PER_PRODUCT:])
        self._save()

    def select_best(self, candidates: list[dict], n: int = 5) -> list[dict]:
        """加权随机选择最优角度"""
        import random
        # 计算权重
        for c in candidates:
            c["_weight"] = self.get_weight(c.get("angle_key", ""))
        # 优先从未使用过的选
        unused = [c for c in candidates if c["_weight"] >= 0.9]
        if len(unused) >= n:
            return random.sample(unused, n)
        # 混合
        selected = list(unused)
        remaining = [c for c in candidates if c not in selected]
        weights = [c["_weight"] for c in remaining]
        total_w = sum(weights) or 1
        probs = [w / total_w for w in weights]
        if remaining:
            extra = random.choices(
                remaining, weights=probs, k=n - len(selected))
            selected.extend(extra)
        return selected[:n]

    def _load(self):
        if not os.path.exists(self._path):
            return
        try:
            with open(self._path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self._angles = data.get("angles", {})
        except Exception:
            self._angles = {}

    def _save(self):
        with open(self._path, "w", encoding="utf-8") as f:
            json.dump({
                "product_id": self.product_id,
                "product_name": self.product_name,
                "angles": self._angles,
                "last_updated": datetime.now().isoformat(),
            }, f, ensure_ascii=False, indent=2)
