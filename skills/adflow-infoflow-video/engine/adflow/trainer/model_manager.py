# -*- coding: utf-8 -*-
"""
模型管理器 — 管理多个 LoRA adapter 的加载、切换、A/B 对比

支持:
  - 多品类 adapter（零食/护肤/数码/...各一个）
  - 运行时热切换（Ollama API 切换模型名）
  - A/B 对比评估（base vs adapter）
  - adapter 版本管理（v1/v2/...）
"""
import json
import logging
import os
from dataclasses import dataclass
from datetime import datetime
from typing import Optional

logger = logging.getLogger("adflow.trainer.manager")


@dataclass
class AdapterInfo:
    """LoRA Adapter 元信息"""
    name: str = ""                    # "adflow-copy-v1"
    ollama_model: str = ""            # Ollama 模型名
    category: str = ""                # 适配品类（空=通用）
    adapter_path: str = ""
    base_model: str = "qwen3:8b"
    lora_rank: int = 16
    samples_count: int = 0
    eval_loss: float = 0.0
    trained_at: str = ""
    active: bool = True
    notes: str = ""


class ModelManager:
    """模型管理器 — LoRA adapter 的增删改查 + A/B 测试"""

    def __init__(self, registry_path: str = ""):
        self.registry_path = registry_path or os.path.join(
            os.path.dirname(__file__), "..", "..", "data", "_lora_registry.json")
        self._adapters: dict[str, AdapterInfo] = {}
        self._load_registry()

    # ── Adapter 管理 ──

    def register(
        self, name: str, ollama_model: str, category: str = "",
        adapter_path: str = "", **kwargs,
    ) -> AdapterInfo:
        """注册一个 LoRA adapter"""
        info = AdapterInfo(
            name=name,
            ollama_model=ollama_model,
            category=category,
            adapter_path=adapter_path,
            trained_at=datetime.now().isoformat(),
            **kwargs,
        )
        self._adapters[name] = info
        self._save_registry()
        logger.info("Adapter 已注册: %s → %s", name, ollama_model)
        return info

    def get(self, name: str = "", category: str = "") -> Optional[AdapterInfo]:
        """获取 adapter（按名称或品类）"""
        if name and name in self._adapters:
            return self._adapters[name]
        if category:
            for info in self._adapters.values():
                if info.category == category and info.active:
                    return info
        return None

    def get_for_category(self, category: str) -> Optional[AdapterInfo]:
        """获取指定品类的最佳 adapter"""
        # 精确匹配优先
        exact = self.get(category=category)
        if exact:
            return exact
        # 回退到通用 adapter
        return self.get(name="adflow-copy-default")

    def remove(self, name: str):
        if name in self._adapters:
            del self._adapters[name]
            self._save_registry()

    # ── ScriptAgent 集成 ──

    def get_model_for_task(self, product_category: str = "") -> str:
        """根据品类返回应使用的 Ollama 模型名

        优先级: 品类 adapter > 通用 adapter > base model

        Returns:
            Ollama 模型名 (如 "qwen3:8b-adflow-snack")
        """
        # 获取 config 中的 copy_optimization 配置
        try:
            from adflow.config_loader import config
            copy_cfg = config.get("copy_optimization", {}) or {}
            lora_enabled = copy_cfg.get("lora_enabled", False)
            if not lora_enabled:
                return self._get_base_model()
        except Exception:
            pass

        adapter = self.get_for_category(product_category)
        if adapter:
            logger.info("使用 LoRA adapter: %s (品类=%s)",
                         adapter.name, product_category)
            return adapter.ollama_model

        return self._get_base_model()

    @staticmethod
    def _get_base_model() -> str:
        try:
            from adflow.config_loader import config
            return config.get("llm.local.model", "qwen3:8b")
        except Exception:
            return "qwen3:8b"

    # ── 持久化 ──

    def _load_registry(self):
        if not os.path.exists(self.registry_path):
            self._adapters = {}
            return
        try:
            with open(self.registry_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self._adapters = {
                name: AdapterInfo(**info)
                for name, info in data.items()
            }
        except Exception as e:
            logger.warning("Adapter 注册表加载失败: %s", e)
            self._adapters = {}

    def _save_registry(self):
        os.makedirs(os.path.dirname(self.registry_path), exist_ok=True)
        with open(self.registry_path, "w", encoding="utf-8") as f:
            from dataclasses import asdict
            json.dump(
                {name: asdict(info) for name, info in self._adapters.items()},
                f, ensure_ascii=False, indent=2,
            )


# ── 全局单例 ──
_model_manager: Optional[ModelManager] = None


def get_model_manager() -> ModelManager:
    global _model_manager
    if _model_manager is None:
        _model_manager = ModelManager()
    return _model_manager
