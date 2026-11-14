# -*- coding: utf-8 -*-
"""
智能断句引擎 — 基于本地 LLM 的中文语义断句

输入: 旁白文案 → 输出: 按语义断句的分段列表（8-20字/段）

后端: 优先本地 Ollama（Qwen2.5:3b），不可用时回退到标点规则。
"""
import hashlib
import json
import logging
from typing import Optional

logger = logging.getLogger("adflow.segmenter")

# ── 断句专用 System Prompt ──
SEGMENTATION_PROMPT = """你是一个中文文案断句专家。将给定的中文文案按人类阅读习惯断句。

## 断句规则
1. 一句话表达完才断句：宁可句子长一点，也不要为了字数把一个意思拦腰斩断
2. 每句一般 8-22 字，只是参考范围，语义完整永远优先于字数
3. 在语义边界处断句：主谓之间、分句之间、连词之前
4. 不要在词中间断开（如"无花果"不能断成"无花"+"果"）
5. 不要在修饰语和中心语之间断开（如"天然高纤低糖的"不断开）
6. 数字+量词保持完整（如"两颗""30秒"不拆分）
7. 保持每句是一个完整的语义单元
8. 考虑口语节奏：说话时自然停顿的地方就是断句点

## 输出格式
直接输出 JSON 数组，每段一个字符串：
["第一句", "第二句", "第三句"]

## 示例
输入: "其实有一种天然高纤低糖的水果无花果可以帮你轻松控糖不仅好吃而且便宜每天吃两颗就够了"
输出: ["其实有一种天然高纤低糖的水果无花果", "可以帮你轻松控糖", "不仅好吃而且便宜", "每天吃两颗就够了"]
"""

# 断句结果缓存
_segment_cache: dict[str, list[str]] = {}

# 防递归保护：segment() 兜底会调 break_by_punctuation，后者兜底又调 segment()
_segmenting: set[str] = set()


class IntelligentSegmenter:
    """智能断句引擎 — 本地 LLM 语义断句 + 规则后处理"""

    def __init__(self, model: str = "", base_url: str = "", api_key: str = ""):
        # 读取配置
        try:
            from adflow.config_loader import config
            seg_cfg = config.get("segmentation", {}) or {}
        except Exception:
            seg_cfg = {}

        self.enabled = seg_cfg.get("enabled", True)
        self.backend = seg_cfg.get("backend", "ollama")
        self.model = model or seg_cfg.get("model", "qwen3:8b")
        self.base_url = base_url or seg_cfg.get("base_url", "http://localhost:11434/v1")
        self.api_key = api_key or seg_cfg.get("api_key", "ollama")
        self.temperature = seg_cfg.get("temperature", 0.1)
        self.max_tokens = seg_cfg.get("max_tokens", 2048)
        self.timeout = seg_cfg.get("timeout", 30)
        self.fallback = seg_cfg.get("fallback", "punctuation")
        self.cache_enabled = seg_cfg.get("cache_enabled", True)
        self.min_chars = seg_cfg.get("min_chars", 5)
        self.max_chars = seg_cfg.get("max_chars", 25)
        self.target_range = seg_cfg.get("target_range", [8, 20])

        # 情绪-长度映射
        self.emotion_length = seg_cfg.get("emotion_length", {
            "激昂": [6, 12],
            "紧迫": [5, 10],
            "温和": [12, 22],
            "中性": [8, 18],
        })

        self._client = None
        self._available: Optional[bool] = None
        self._active_backend = ""   # "ollama" | "cloud"（available 检测时确定）
        self._cloud_model = ""      # 云端断句用的模型名

    @property
    def available(self) -> bool:
        """检测断句后端是否可用：优先本地 Ollama，不可用走设置页配置的云端 LLM"""
        if self._available is not None:
            return self._available
        if not self.enabled:
            self._available = False
            return False
        self._active_backend = ""
        # ── 1. 本地 Ollama（免费，断句零成本）──
        if self.backend == "ollama":
            try:
                from openai import OpenAI
                client = OpenAI(base_url=self.base_url, api_key=self.api_key,
                                timeout=5)
                models = client.models.list()
                model_ids = [m.id for m in models]
                if any(self.model in mid for mid in model_ids):
                    self._client = client
                    self._active_backend = "ollama"
                    self._available = True
                    logger.info("本地模型 %s 可用", self.model)
                    return True
                logger.warning("本地模型 %s 未找到，可用: %s", self.model, model_ids)
            except Exception as e:
                logger.warning("本地模型不可用: %s，尝试云端 LLM 断句", e)
        # ── 2. 云端 LLM（设置页配置的平台，如阿里百炼/DeepSeek）──
        try:
            from adflow.api.llm_adapter import get_llm_config
            api_key, base_url, model = get_llm_config()
            if api_key:
                from openai import OpenAI
                self._client = OpenAI(base_url=base_url, api_key=api_key,
                                      timeout=self.timeout)
                self._cloud_model = model
                self._active_backend = "cloud"
                self._available = True
                logger.info("云端 LLM 断句可用: %s", model)
                return True
        except Exception as e:
            logger.warning("云端 LLM 断句不可用: %s，回退到标点断句", e)
        self._available = False
        return False

    def segment(self, text: str, emotion: str = "中性") -> list[str]:
        """智能断句

        Args:
            text: 待断句的文案
            emotion: 情绪标签（影响断句长度偏好）

        Returns:
            分段列表 ["句1", "句2", ...]
        """
        global _segment_cache
        text = text.strip()
        if not text:
            return []

        # 防递归：本函数兜底会调 break_by_punctuation，其兜底又会调本函数
        if text in _segmenting:
            return []
        _segmenting.add(text)
        try:
            return self._segment_inner(text, emotion)
        finally:
            _segmenting.discard(text)

    def _segment_inner(self, text: str, emotion: str) -> list[str]:
        global _segment_cache

        # 短文本直接返回
        if len(text) <= self.max_chars:
            return [text]

        # 查缓存
        cache_key = ""
        if self.cache_enabled:
            cache_key = hashlib.md5(f"{text}_{emotion}".encode()).hexdigest()
            if cache_key in _segment_cache:
                return _segment_cache[cache_key]

        # 尝试本地模型
        segments = []
        if self.available:
            try:
                segments = self._model_segment(text, emotion)
            except Exception as e:
                logger.warning("模型断句失败: %s，回退标点规则", e)

        # 回退到标点断句
        if not segments:
            from adflow.engine.subtitle_renderer import break_by_punctuation
            segments = break_by_punctuation(text)

        # 规则后处理
        segments = self._post_process(segments, text)

        # 写缓存
        if self.cache_enabled and cache_key:
            _segment_cache[cache_key] = segments

        return segments

    def _model_segment(self, text: str, emotion: str) -> list[str]:
        """调用断句模型（本地 Ollama 或设置页配置的云端 LLM）"""
        from openai import OpenAI
        if self._client is None:
            # available 未探测过（直接调 segment 的场景），按后端兜底建客户端
            if self._active_backend == "cloud" or (
                    self._active_backend == "" and self.backend != "ollama"):
                from adflow.api.llm_adapter import get_llm_config
                api_key, base_url, model = get_llm_config()
                if not api_key:
                    return []
                self._client = OpenAI(base_url=base_url, api_key=api_key,
                                      timeout=self.timeout)
                self._cloud_model = model
                self._active_backend = "cloud"
            else:
                self._client = OpenAI(base_url=self.base_url, api_key=self.api_key)
                self._active_backend = "ollama"

        model = (self._cloud_model if self._active_backend == "cloud"
                 else self.model)

        # 情绪提示
        emo_range = self.emotion_length.get(emotion, [8, 18])
        emo_hint = (
            f"当前文案情绪为 [{emotion}]，"
            f"请尽量将每段控制在{emo_range[0]}-{emo_range[1]}字。"
        )

        user_msg = f"{emo_hint}\n\n请将以下文案断句：\n{text}"

        response = self._client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": SEGMENTATION_PROMPT},
                {"role": "user", "content": user_msg},
            ],
            temperature=self.temperature,
            max_tokens=self.max_tokens,
            timeout=self.timeout,
        )

        raw = response.choices[0].message.content or "[]"
        segments = self._parse_output(raw)
        logger.info("模型断句: %d字 → %d段 (模型=%s)", len(text), len(segments), model)
        return segments

    @staticmethod
    def _parse_output(raw: str) -> list[str]:
        """解析模型输出为分段列表"""
        raw = raw.strip()
        # 去除可能的 markdown 代码块
        if raw.startswith("```"):
            lines = raw.split("\n")
            lines = lines[1:] if lines[0].startswith("```") else lines
            if lines and lines[-1].startswith("```"):
                lines = lines[:-1]
            raw = "\n".join(lines)
        try:
            result = json.loads(raw)
            if isinstance(result, list):
                return [s.strip() for s in result if isinstance(s, str) and s.strip()]
        except json.JSONDecodeError:
            pass
        return []

    def _post_process(self, segments: list[str], original_text: str) -> list[str]:
        """规则后处理：验证完整性 + 合并过短段 + 拆分过长段"""
        if not segments:
            return [original_text]

        # 1. 验证拼接完整性
        joined = "".join(segments)
        if joined != original_text:
            logger.warning("断句拼接不匹配原文，回退标点规则")
            from adflow.engine.subtitle_renderer import break_by_punctuation
            return break_by_punctuation(original_text)

        # 2. 合并过短段（< min_chars 字合并到前一段）
        merged = []
        for seg in segments:
            if merged and len(seg) < self.min_chars:
                merged[-1] += seg
            else:
                merged.append(seg)

        # 3. 拆分过长段（> max_chars 字在标点处切分）
        from adflow.engine.subtitle_renderer import break_by_punctuation
        final = []
        for seg in merged:
            if len(seg) > self.max_chars:
                sub_segs = break_by_punctuation(seg)
                final.extend(sub_segs)
            else:
                final.append(seg)

        return final


# ── 全局单例 ──
_segmenter: Optional[IntelligentSegmenter] = None


def get_segmenter() -> IntelligentSegmenter:
    """获取断句器单例"""
    global _segmenter
    if _segmenter is None:
        _segmenter = IntelligentSegmenter()
    return _segmenter
