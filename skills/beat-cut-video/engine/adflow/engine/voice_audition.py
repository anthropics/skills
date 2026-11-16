# -*- coding: utf-8 -*-
"""
配音试听服务 — 列出可用音色 + 生成试听样本

用于 GUI 的"AI配音选择（带试听）"功能:
  1. list_voices() → 返回所有可用音色列表（名称/性别/风格）
  2. audition(voice_id) → 生成一段试听音频（"你好，这是我的配音风格..."）
  3. 试听音频缓存，避免重复合成
"""
import logging
import os
from dataclasses import dataclass, field

logger = logging.getLogger("adflow.audition")


@dataclass
class VoiceInfo:
    """音色信息"""
    voice_id: str = ""
    name: str = ""
    gender: str = ""      # male/female
    style: str = ""       # 活泼/沉稳/温柔/...
    backend: str = ""     # volcano/edge/cosyvoice
    tags: list[str] = field(default_factory=list)


class VoiceAuditionService:
    """配音试听服务"""

    AUDITION_TEXT = "你好，我是你的AI配音助手。无论是产品介绍、促销广告还是品牌故事，我都能用最合适的风格来呈现。试试看吧！"

    def __init__(self):
        from adflow.config_loader import config
        self.output_dir = os.path.join(config.output_dir, "_auditions")
        os.makedirs(self.output_dir, exist_ok=True)

    def list_voices(self, backend: str = "") -> list[VoiceInfo]:
        """列出所有可用音色

        Args:
            backend: 限定后端 (volcano/edge/cosyvoice)，空=全部

        Returns:
            音色列表
        """
        voices = []

        # 火山引擎
        if not backend or backend == "volcano":
            try:
                from adflow.engine.volcano_tts import VOLCANO_VOICES, VolcanoTTSEngine
                try:
                    VolcanoTTSEngine()  # 测试连接
                    available = True
                except Exception:
                    available = False
                for vid, vp in VOLCANO_VOICES.items():
                    voices.append(VoiceInfo(
                        voice_id=vid, name=vp.name, gender=vp.gender,
                        style=vp.style, backend="volcano",
                        tags=["已连接"] if available else [],
                    ))
            except ImportError:
                pass

        # Edge-TTS
        if not backend or backend == "edge":
            try:
                from adflow.engine.tts_engine import EDGE_VOICES, EdgeTTSEngine
                try:
                    e = EdgeTTSEngine()
                    available = e.available
                except Exception:
                    available = False
                for vid, vp in EDGE_VOICES.items():
                    voices.append(VoiceInfo(
                        voice_id=vid, name=vp.name, gender=vp.gender,
                        style=vp.style, backend="edge",
                        tags=["免费"] if available else ["不可用"],
                    ))
            except ImportError:
                pass

        # CosyVoice
        if not backend or backend == "cosyvoice":
            try:
                from adflow.engine.tts_engine import COSY_VOICES
                for vid, vp in COSY_VOICES.items():
                    voices.append(VoiceInfo(
                        voice_id=vid, name=vp.name, gender=vp.gender,
                        style=vp.style, backend="cosyvoice",
                        tags=["阿里云"],
                    ))
            except ImportError:
                pass

        return voices

    def audition(self, voice_id: str, backend: str = "",
                 text: str = "") -> str:
        """生成试听音频

        Args:
            voice_id: 音色ID
            backend: TTS后端
            text: 试听文本（默认用预设文本）

        Returns:
            试听音频文件路径
        """
        text = text or self.AUDITION_TEXT

        # 缓存
        import hashlib
        cache_key = hashlib.md5(
            f"{voice_id}_{backend}_{text}".encode()).hexdigest()[:8]
        cache_path = os.path.join(self.output_dir, f"audition_{cache_key}.mp3")
        if os.path.exists(cache_path):
            logger.info("试听缓存: %s", cache_path)
            return cache_path

        try:
            if not backend:
                # 从 voice_id 推断后端
                if voice_id.startswith("BV") or "bigtts" in voice_id:
                    backend = "volcano"
                elif voice_id.startswith("zh-CN-"):
                    backend = "edge"
                else:
                    backend = "cosyvoice"

            if backend == "volcano":
                from adflow.engine.volcano_tts import VolcanoTTSEngine
                tts = VolcanoTTSEngine(voice=voice_id)
            elif backend == "edge":
                from adflow.engine.tts_engine import EdgeTTSEngine
                tts = EdgeTTSEngine(voice=voice_id)
            else:
                from adflow.engine.tts_engine import CosyVoiceEngine
                tts = CosyVoiceEngine(voice=voice_id)

            result = tts.synthesize(text, cache_path)
            logger.info("试听生成: %s → %s", voice_id, result)
            return result

        except Exception as e:
            logger.error("试听失败: %s", e)
            return ""
