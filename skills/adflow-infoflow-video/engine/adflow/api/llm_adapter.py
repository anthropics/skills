# -*- coding: utf-8 -*-
"""
多 LLM 适配器 — 统一 OpenAI-compatible 接口，支持多供应商切换

支持的供应商:
  - dashscope: 阿里百炼（Qwen 系列）
  - deepseek: DeepSeek（逻辑推理强）
  - moonshot: Moonshot（长上下文）
  - openai: OpenAI（GPT 系列）
  - ollama: 本地 Ollama（免费）

使用方式:
  from adflow.api.llm_adapter import get_llm_config
  api_key, base_url, model = get_llm_config("deepseek")
"""

import os
from dataclasses import dataclass


@dataclass
class LLMProviderConfig:
    """单个 LLM 供应商配置"""
    name: str                 # 供应商标识（dashscope/deepseek/moonshot/openai/ollama）
    base_url: str             # API base URL
    api_key_env: str          # 环境变量名
    default_model: str        # 默认模型
    api_key: str = ""         # 可选：直接在 config 里写 api_key（低安全）


# 默认供应商配置（config.yaml 中 llm.providers 未配置时使用）
_DEFAULT_PROVIDERS: dict[str, LLMProviderConfig] = {
    "dashscope": LLMProviderConfig(
        name="dashscope",
        base_url="https://dashscope.aliyuncs.com/compatible-mode/v1",
        api_key_env="DASHSCOPE_API_KEY",
        default_model="qwen-max",
    ),
    "deepseek": LLMProviderConfig(
        name="deepseek",
        base_url="https://api.deepseek.com/v1",
        api_key_env="DEEPSEEK_API_KEY",
        default_model="deepseek-chat",
    ),
    "moonshot": LLMProviderConfig(
        name="moonshot",
        base_url="https://api.moonshot.cn/v1",
        api_key_env="MOONSHOT_API_KEY",
        default_model="moonshot-v1-8k",
    ),
    "openai": LLMProviderConfig(
        name="openai",
        base_url="https://api.openai.com/v1",
        api_key_env="OPENAI_API_KEY",
        default_model="gpt-4o-mini",
    ),
    "ollama": LLMProviderConfig(
        name="ollama",
        base_url="http://localhost:11434/v1",
        api_key_env="",
        default_model="qwen3:8b",
        api_key="ollama",
    ),
}


def _load_providers_from_config() -> dict[str, LLMProviderConfig]:
    """从 config.yaml 加载供应商配置，合并默认值"""
    try:
        from adflow.config_loader import config
        providers_cfg = config.get("llm.providers")
        if not providers_cfg or not isinstance(providers_cfg, dict):
            return dict(_DEFAULT_PROVIDERS)

        result = dict(_DEFAULT_PROVIDERS)
        for name, cfg in providers_cfg.items():
            if isinstance(cfg, dict):
                # 合并：config.yaml 的值覆盖默认值
                default = result.get(name)
                if default:
                    result[name] = LLMProviderConfig(
                        name=name,
                        base_url=cfg.get("base_url", default.base_url),
                        api_key_env=cfg.get("api_key_env", default.api_key_env),
                        default_model=cfg.get("model", default.default_model),
                        api_key=cfg.get("api_key", default.api_key),
                    )
                else:
                    # 全新的供应商
                    result[name] = LLMProviderConfig(
                        name=name,
                        base_url=cfg.get("base_url", ""),
                        api_key_env=cfg.get("api_key_env", ""),
                        default_model=cfg.get("model", ""),
                        api_key=cfg.get("api_key", ""),
                    )
        return result
    except Exception:
        return dict(_DEFAULT_PROVIDERS)


def get_llm_config(provider_name: str | None = None) -> tuple[str, str, str]:
    """获取 LLM 配置 (api_key, base_url, model)

    Args:
        provider_name: 供应商名称，为 None 时使用 config.yaml 中 llm.active

    Returns:
        (api_key, base_url, model) 三元组
    """
    providers = _load_providers_from_config()

    # 记录是否显式指定供应商（显式路由时 llm.model 不应覆盖供应商自己的 model）
    explicit = provider_name is not None

    # 确定使用的供应商
    if not provider_name:
        try:
            from adflow.config_loader import config
            provider_name = config.get("llm.active", "dashscope")
        except Exception:
            provider_name = "dashscope"

    provider = providers.get(provider_name)
    if not provider:
        # 回退到 dashscope
        provider = providers.get("dashscope")
        if not provider:
            raise RuntimeError(f"LLM供应商 '{provider_name}' 未配置且无默认回退")

    # 获取 api_key
    api_key = provider.api_key
    if not api_key and provider.api_key_env:
        api_key = os.environ.get(provider.api_key_env, "")

    # 兼容旧配置：仅当未显式指定供应商（走默认 active）时，llm.model 才覆盖 model
    # 显式路由（task_routing）时用供应商自己的 model，避免全局覆盖导致 base_url/model 错配
    if not explicit:
        try:
            from adflow.config_loader import config
            model_override = config.get("llm.model")
            if model_override:
                return api_key, provider.base_url, model_override
        except Exception:
            pass

    return api_key, provider.base_url, provider.default_model


def get_task_provider(task: str) -> str:
    """按任务路由获取供应商名称

    支持 config.yaml 中 llm.task_routing:
      strategy: deepseek    # 策略用DeepSeek（逻辑强）
      script: qwen          # 脚本用Qwen（创意好）
      rewrite: moonshot     # 改写用Moonshot（长上下文）

    Args:
        task: 任务类型（strategy/script/rewrite/optimization/match）

    Returns:
        供应商名称，无路由配置时返回 None（使用默认 active provider）
    """
    try:
        from adflow.config_loader import config
        routing = config.get("llm.task_routing")
        if routing and isinstance(routing, dict):
            return routing.get(task)
    except Exception:
        pass
    return None


def get_llm_config_for_task(task: str) -> tuple[str, str, str]:
    """按任务获取 LLM 配置（自动路由）

    Args:
        task: 任务类型

    Returns:
        (api_key, base_url, model)
    """
    provider = get_task_provider(task)
    return get_llm_config(provider)
