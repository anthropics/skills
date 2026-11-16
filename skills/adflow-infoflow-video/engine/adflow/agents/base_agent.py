"""
LLM API 调用封装
- OpenAI 兼容 SDK 统一入口（阿里百炼 / 通义千问）
- 自动重试 (3次)
- 结构化输出（Prompt 约束 JSON Schema）
- Token 用量统计
"""

import json
import logging
import os
import time

from openai import OpenAI

from adflow.config_loader import config

logger = logging.getLogger("adflow.agent")

# 云端额度耗尽/欠费后的进程级标记：置位后所有 Agent 直接走本地兜底，
# 避免每次调用都先撞云端 403（额度耗尽是稳定状态，非临时抖动）
_CLOUD_UNAVAILABLE = False


def cloud_unavailable() -> bool:
    """云端已确认不可用（额度耗尽/欠费），调用方据此降级本地、减少变体数。"""
    return _CLOUD_UNAVAILABLE


class BaseAgent:
    """Agent 基类 — 封装 LLM API 调用"""

    def __init__(
        self,
        model: str | None = None,
        max_tokens: int | None = None,
        temperature: float | None = None,
        task: str | None = None,
    ):
        # ── 多 LLM 适配器：优先使用 adapter 获取配置 ──
        try:
            from adflow.api.llm_adapter import get_llm_config, get_llm_config_for_task
            if task:
                self.api_key, self.base_url, default_model = get_llm_config_for_task(task)
            else:
                self.api_key, self.base_url, default_model = get_llm_config()
        except Exception:
            default_model = config.llm_model
            self.api_key = config.llm_api_key or os.environ.get("DASHSCOPE_API_KEY", "")
            self.base_url = config.llm_base_url

        # 本地 Ollama 兜底配置（云端失败时降级使用，而非主模式）
        local_cfg = config.get("llm.local", {}) or {}
        self._local_enabled = bool(local_cfg.get("enabled", False))
        self._local_model = local_cfg.get("model", "qwen3:8b")
        self._local_base_url = local_cfg.get("base_url", "http://localhost:11434/v1")
        self._local_api_key = local_cfg.get("api_key", "ollama")
        self._local_timeout = int(local_cfg.get("timeout", 300))
        self._local_client: OpenAI | None = None

        # 云端为主
        self.model = model or default_model

        self.max_tokens = max_tokens or config.llm_max_tokens
        self.temperature = temperature if temperature is not None else config.llm_temperature
        self._client: OpenAI | None = None
        self._total_tokens_used = 0
        self._used_local_fallback = False  # 实际已降级本地（区别于 _local_enabled「允许降级」）

    @property
    def client(self) -> OpenAI:
        if self._client is None:
            self._client = OpenAI(api_key=self.api_key, base_url=self.base_url,
                                  timeout=60, max_retries=0)
        return self._client

    def call(
        self,
        system_prompt: str,
        user_message: str,
        temperature: float | None = None,
        max_retries: int = 3,
    ) -> str:
        """
        调用 LLM API，返回文本响应
        自动重试，指数退避
        """
        last_error = None
        global _CLOUD_UNAVAILABLE
        if _CLOUD_UNAVAILABLE and self._local_enabled:
            fallback = self._try_local_fallback(system_prompt, user_message, temperature)
            if fallback is not None:
                return fallback
            # 本地也失败（如 ollama 未启动），重置标记回退云端再试
            _CLOUD_UNAVAILABLE = False
        for attempt in range(max_retries):
            try:
                response = self.client.chat.completions.create(
                    model=self.model,
                    max_tokens=self.max_tokens,
                    temperature=temperature if temperature is not None else self.temperature,
                    messages=[
                        {"role": "system", "content": system_prompt},
                        {"role": "user", "content": user_message},
                    ],
                )
                content = response.choices[0].message.content
                if content is None:
                    raise RuntimeError("LLM 返回空响应")
                if response.usage and response.usage.total_tokens:
                    self._total_tokens_used += response.usage.total_tokens
                    try:
                        from adflow.monitor.budget_tracker import get_budget_tracker
                        get_budget_tracker().record_llm(
                            input_tokens=response.usage.prompt_tokens or 0,
                            output_tokens=response.usage.completion_tokens or 0,
                            model=self.model,
                        )
                    except Exception as e:
                        logging.getLogger("adflow.agent").warning("计费记录失败: %s", e)
                return content

            except Exception as e:
                err_msg = str(e)
                # 判断是否可重试的错误
                if "rate" in err_msg.lower() or "限流" in err_msg:
                    wait = 2 ** attempt * 5
                    logger.warning(f"[Agent] 速率限制，等待 {wait}s 后重试...")
                    time.sleep(wait)
                    last_error = "速率限制"
                elif "timeout" in err_msg.lower() or "超时" in err_msg or "连接" in err_msg:
                    wait = 2 ** attempt
                    logger.warning(f"[Agent] 网络错误: {e}, 等待 {wait}s 后重试...")
                    time.sleep(wait)
                    last_error = str(e)
                else:
                    # 额度耗尽/欠费：重试无用，先降级本地；本地也失败则立即抛错（不进入重试循环）
                    if ("quota" in err_msg.lower() or "额度" in err_msg
                            or "arrearage" in err_msg.lower()
                            or "欠费" in err_msg or "overdue" in err_msg.lower()):
                        fallback = self._try_local_fallback(
                            system_prompt, user_message, temperature)
                        if fallback is not None:
                            _CLOUD_UNAVAILABLE = True
                            return fallback
                        # 永久性错误（欠费/额度耗尽）：重试无意义，直接终止
                        raise
                    if attempt == max_retries - 1:
                        # 最后一次失败：先尝试本地 Ollama 兜底
                        fallback = self._try_local_fallback(
                            system_prompt, user_message, temperature)
                        if fallback is not None:
                            return fallback
                        raise
                    wait = 2 ** attempt
                    logger.warning(f"[Agent] API 错误: {e}, 等待 {wait}s 后重试...")
                    time.sleep(wait)
                    last_error = str(e)

        raise RuntimeError(f"Agent 调用失败（{max_retries}次重试后）: {last_error}")

    def _try_local_fallback(
        self, system_prompt: str, user_message: str,
        temperature: float | None = None,
    ) -> str | None:
        """云端失败后尝试本地 Ollama 兜底，成功返回内容，失败返回 None"""
        if not self._local_enabled:
            return None
        try:
            if self._local_client is None:
                self._local_client = OpenAI(
                    api_key=self._local_api_key, base_url=self._local_base_url,
                    timeout=self._local_timeout, max_retries=0)
            response = self._local_client.chat.completions.create(
                model=self._local_model,
                max_tokens=self.max_tokens,
                temperature=temperature if temperature is not None else self.temperature,
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": user_message},
                ],
            )
            content = response.choices[0].message.content
            if content:
                self._used_local_fallback = True
                logger.warning(f"[Agent] 云端失败，已降级本地 Ollama ({self._local_model})")
                return content
        except Exception as e:
            logger.warning(f"[Agent] 本地 Ollama 兜底也失败: {e}")
        return None

    def call_structured(
        self,
        system_prompt: str,
        user_message: str,
        output_schema: dict,
        temperature: float | None = None,
    ) -> dict:
        """
        调用 LLM API，强制输出符合 JSON Schema 的结构化数据
        通过 Prompt 约束格式（国内模型通用方案）
        """
        # 在系统提示中追加格式要求
        schema_json = json.dumps(output_schema, ensure_ascii=False, indent=2)
        system_with_schema = (
            f"{system_prompt}\n\n"
            f"## 输出格式要求\n"
            f"你必须严格按以下 JSON Schema 输出，不要输出其他内容：\n"
            f"```json\n{schema_json}\n```\n"
            f"请直接输出 JSON，不要包裹在 ```json 代码块中。"
        )

        raw = self.call(system_with_schema, user_message, temperature=temperature)

        # 解析 JSON（容错处理）
        return self._parse_json(raw)

    @property
    def total_tokens(self) -> int:
        return self._total_tokens_used

    @staticmethod
    def _parse_json(raw: str) -> dict:
        """从响应中提取 JSON（增强容错）"""
        raw = raw.strip()
        # 去除可能的 Markdown 代码块标记（首尾 ``` 都处理，不管开头是否 ```）
        lines = raw.split("\n")
        if lines and lines[0].strip().startswith("```"):
            lines = lines[1:]
        if lines and lines[-1].strip().startswith("```"):
            lines = lines[:-1]
        raw = "\n".join(lines).strip()

        # 尝试直接解析
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            pass

        # 容错: 尝试修复常见JSON问题
        import re

        # 1. 尾部多余逗号 (LLM 常见错误)
        raw = re.sub(r',\s*([}\]])', r'\1', raw)

        # 2. 缺少引号的key (非标准但常见)
        # 简单检测: 花括号内没被引号包围的标识符

        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            pass

        # 3. 尝试用 ast.literal_eval (处理单引号JSON)
        try:
            import ast
            return ast.literal_eval(raw)
        except (ValueError, SyntaxError):
            pass

        # 4. 提取第一个有效的 JSON 对象/数组
        # 找到第一个 { 或 [ 和最后一个 } 或 ]
        for start_ch, end_ch in [('{', '}'), ('[', ']')]:
            start = raw.find(start_ch)
            end = raw.rfind(end_ch)
            if start >= 0 and end > start:
                try:
                    return json.loads(raw[start:end + 1])
                except json.JSONDecodeError:
                    continue

        # 最终: 抛出原始错误
        raise json.JSONDecodeError(
            f"无法解析JSON: {raw[:200]}...", raw, 0)
