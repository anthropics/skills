# -*- coding: utf-8 -*-
"""
预算追踪器 — 对标 OpenMontage 的 budget governance

功能:
  1. 执行前成本估算: LLM token + TTS 字符 + API 调用次数
  2. 执行中实时追踪: 累计 token / API 调用 / 成本
  3. 执行后成本报告: 每次任务输出到 project.json

成本参考 (2026年7月):
  - Qwen-Max:        ¥0.02/1K tokens (input), ¥0.06/1K tokens (output)
  - Qwen3:8b (本地):  ¥0 (Ollama)
  - CosyVoice:       ¥2/万字符
  - Edge-TTS:        ¥0 (免费)
  - 火山 TTS:         ¥2/万字符 (免费额度 50万字符/月)
  - Piper TTS:       ¥0 (本地离线)
"""
import json
import logging
import os
import time
from dataclasses import dataclass, field
from datetime import datetime
from typing import Optional

logger = logging.getLogger("adflow.budget")


@dataclass
class CostEstimate:
    """成本估算"""
    llm_input_tokens: int = 0
    llm_output_tokens: int = 0
    llm_cost: float = 0.0

    tts_chars: int = 0
    tts_cost: float = 0.0

    total_cost: float = 0.0
    currency: str = "CNY"

    breakdown: str = ""  # 人类可读的成本明细


@dataclass
class BudgetRecord:
    """单次任务的实际成本记录"""
    task_id: str = ""
    started_at: str = ""
    completed_at: str = ""

    # LLM 用量
    llm_input_tokens: int = 0
    llm_output_tokens: int = 0
    llm_calls: int = 0
    llm_cost: float = 0.0

    # TTS 用量
    tts_backend: str = ""
    tts_chars: int = 0
    tts_cost: float = 0.0

    # 其他
    total_cost: float = 0.0
    currency: str = "CNY"

    # 明细
    phases: list[dict] = field(default_factory=list)


class BudgetTracker:
    """预算追踪器"""

    # 成本单价
    PRICES = {
        "qwen-max": {"input": 0.02, "output": 0.06},    # ¥/1K tokens
        "qwen-plus": {"input": 0.002, "output": 0.006},
        "qwen-turbo": {"input": 0.0008, "output": 0.002},
        "cosyvoice": 2.0,      # ¥/万字符
        "volcano_tts": 2.0,     # ¥/万字符
        "edge_tts": 0,          # 免费
        "piper_tts": 0,          # 免费离线
        "llm_local": 0,         # 本地 Ollama
    }

    def __init__(self):
        self._current: Optional[BudgetRecord] = None
        self._phase_start: float = 0
        self._history: list[BudgetRecord] = []
        self._history_path = os.path.join(
            os.path.dirname(__file__), "..", "..", "data", "_budget_history.json")
        self._load_history()

    def estimate(self, variant_count: int = 5,
                 avg_script_length: int = 500,
                 tts_backend: str = "cosyvoice",
                 llm_model: str = "qwen-max") -> CostEstimate:
        """执行前成本估算

        Args:
            variant_count: 变体数量
            avg_script_length: 平均脚本长度（字）
            tts_backend: TTS 后端
            llm_model: LLM 模型

        Returns:
            CostEstimate
        """
        # LLM 估算
        # Strategy Agent: ~2K input + ~500 output
        # Script Agent: ~3K input + ~2K output per variant
        llm_input = 2000 + 3000 * variant_count
        llm_output = 500 + 2000 * variant_count

        prices = self.PRICES.get(llm_model, self.PRICES.get("qwen-max", {}))
        if isinstance(prices, dict):
            llm_cost = (llm_input / 1000 * prices.get("input", 0.02) +
                        llm_output / 1000 * prices.get("output", 0.06))
        else:
            llm_cost = 0  # 本地模型

        # TTS 估算
        tts_chars = avg_script_length * variant_count
        tts_price = self.PRICES.get(tts_backend, 2.0)
        tts_cost = tts_chars / 10000 * tts_price if isinstance(tts_price, (int, float)) else 0

        total = llm_cost + tts_cost

        breakdown = (
            f"LLM: {llm_input:,}→{llm_output:,} tokens = ¥{llm_cost:.3f}\n"
            f"TTS ({tts_backend}): {tts_chars:,} 字 = ¥{tts_cost:.3f}\n"
            f"预估总计: ¥{total:.3f}"
        )

        return CostEstimate(
            llm_input_tokens=llm_input,
            llm_output_tokens=llm_output,
            llm_cost=round(llm_cost, 4),
            tts_chars=tts_chars,
            tts_cost=round(tts_cost, 4),
            total_cost=round(total, 4),
            breakdown=breakdown,
        )

    def start_task(self, task_id: str):
        """开始追踪一个任务"""
        self._current = BudgetRecord(
            task_id=task_id,
            started_at=datetime.now().isoformat(),
        )
        self._phase_start = time.time()

    def record_llm(self, input_tokens: int, output_tokens: int,
                   model: str = "qwen-max"):
        """记录一次 LLM 调用"""
        if not self._current:
            return
        self._current.llm_input_tokens += input_tokens
        self._current.llm_output_tokens += output_tokens
        self._current.llm_calls += 1

        prices = self.PRICES.get(model, self.PRICES.get("qwen-max", {}))
        if isinstance(prices, dict):
            cost = (input_tokens / 1000 * prices.get("input", 0.02) +
                    output_tokens / 1000 * prices.get("output", 0.06))
            self._current.llm_cost += cost

    def record_phase(self, name: str, cost: float = 0):
        """记录一个阶段的耗时和成本"""
        if not self._current:
            return
        elapsed = time.time() - self._phase_start
        self._current.phases.append({
            "name": name,
            "elapsed_sec": round(elapsed, 1),
            "cost": round(cost, 4),
        })
        self._phase_start = time.time()

    def finish_task(self) -> Optional[BudgetRecord]:
        """结束追踪，保存记录"""
        if not self._current:
            return None

        self._current.completed_at = datetime.now().isoformat()
        self._current.total_cost = round(
            self._current.llm_cost + self._current.tts_cost, 4)

        self._history.append(self._current)
        self._save_history()

        record = self._current
        logger.info(
            "任务成本: LLM=¥%.4f (%d调用) TTS=¥%.4f (%d字) 总计=¥%.4f",
            record.llm_cost, record.llm_calls,
            record.tts_cost, record.tts_chars,
            record.total_cost,
        )

        self._current = None
        return record

    def get_summary(self, days: int = 30) -> dict:
        """获取汇总统计"""
        cutoff = datetime.now().timestamp() - days * 86400
        recent = [
            r for r in self._history
            if r.completed_at
            if datetime.fromisoformat(r.completed_at).timestamp() > cutoff
        ]

        total_cost = sum(r.total_cost for r in recent)
        total_tasks = len(recent)
        total_tokens = sum(r.llm_input_tokens + r.llm_output_tokens for r in recent)
        total_tts_chars = sum(r.tts_chars for r in recent)

        return {
            "period_days": days,
            "total_tasks": total_tasks,
            "total_cost": round(total_cost, 2),
            "avg_cost_per_task": round(total_cost / max(total_tasks, 1), 4),
            "total_llm_tokens": total_tokens,
            "total_tts_chars": total_tts_chars,
            "currency": "CNY",
        }

    def to_dict(self, record: BudgetRecord) -> dict:
        """转为可序列化字典（用于 project.json）"""
        from dataclasses import asdict
        return asdict(record)

    def _load_history(self):
        if not os.path.exists(self._history_path):
            return
        try:
            with open(self._history_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self._history = [BudgetRecord(**r) for r in data]
        except Exception:
            self._history = []

    def _save_history(self):
        os.makedirs(os.path.dirname(self._history_path), exist_ok=True)
        with open(self._history_path, "w", encoding="utf-8") as f:
            from dataclasses import asdict
            json.dump(
                [asdict(r) for r in self._history[-200:]],
                f, ensure_ascii=False, indent=2,
            )


# ── 全局单例 ──
_budget_tracker: Optional[BudgetTracker] = None


def get_budget_tracker() -> BudgetTracker:
    global _budget_tracker
    if _budget_tracker is None:
        _budget_tracker = BudgetTracker()
    return _budget_tracker
