# -*- coding: utf-8 -*-
"""
签名历史库 — 持久化缓存，跨批次记录所有生成过的文案结构

按品类分库: data/diversity_history/{category}.json
30天自动衰减: 旧签名降权，保留高分签名
"""
import json
import os
from datetime import datetime, timedelta


class SignatureHistory:
    """签名历史库 — 品类分库 + 自动衰减"""

    MAX_SIZE = 500
    DECAY_DAYS = 30

    def __init__(self, category: str = "通用"):
        self.category = category
        self._dir = os.path.join(
            os.path.dirname(__file__), "..", "data", "diversity_history")
        os.makedirs(self._dir, exist_ok=True)
        self._records: list[dict] = []
        self._records: list[dict] = []
        self._load()

    @property
    def _path(self) -> str:
        return os.path.join(self._dir, f"{self.category}.json")

    def add(self, signature, script_id: str = "",
            product_name: str = "", score: float = 0):
        """添加签名到历史库"""
        from adflow.engine.signature_extractor import Signature
        sig_dict = {dim: list(getattr(signature, dim))
                     for dim in signature._fields}
        self._records.append({
            "signature": sig_dict,
            "script_id": script_id,
            "product_name": product_name,
            "score": score,
            "created_at": datetime.now().isoformat(),
        })
        # 限制大小
        if len(self._records) > self.MAX_SIZE:
            self._records = self._records[-self.MAX_SIZE:]
        self._save()

    def get_recent(self, n: int = 200) -> list:
        """获取最近 N 条记录"""
        from adflow.engine.signature_extractor import Signature
        recent = self._records[-n:]
        return [Signature(**r["signature"]) for r in recent]

    def count_collisions(self, signature) -> int:
        """统计签名在历史中的碰撞次数"""
        count = 0
        for r in self._records:
            if r["signature"] == {dim: list(getattr(signature, dim))
                                   for dim in signature._fields}:
                count += 1
        return count

    def decay_old(self):
        """清理过期记录（30天前+低分）"""
        cutoff = datetime.now() - timedelta(days=self.DECAY_DAYS)
        self._records = [
            r for r in self._records
            if datetime.fromisoformat(r["created_at"]) > cutoff
            or r.get("score", 0) > 70
        ]
        self._save()

    @property
    def total_count(self) -> int:
        return len(self._records)

    def _load(self):
        if not os.path.exists(self._path):
            self._records = []
            return
        try:
            with open(self._path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self._records = data.get("records", [])[-self.MAX_SIZE:]
        except Exception:
            self._records = []

    def _save(self):
        with open(self._path, "w", encoding="utf-8") as f:
            json.dump({
                "category": self.category,
                "total_count": len(self._records),
                "last_updated": datetime.now().isoformat(),
                "records": self._records,
            }, f, ensure_ascii=False, indent=2)
