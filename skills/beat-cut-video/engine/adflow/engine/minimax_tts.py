# -*- coding: utf-8 -*-
"""
MiniMax TTS 引擎 — speech-2.8-hd 超自然语音合成

API: https://platform.minimax.io/docs/api-reference/speech-t2a-http

MiniMax 中文音色自然度极高，比火山引擎标准音色更自然。
"""
import hashlib
import logging
import os
import subprocess
import tempfile
from dataclasses import dataclass

import requests

from adflow.config_loader import config

logger = logging.getLogger("adflow.tts.minimax")


@dataclass
class MiniMaxVoice:
    voice_id: str
    name: str
    gender: str
    style: str


# MiniMax 中文音色
MINIMAX_VOICES: dict[str, MiniMaxVoice] = {
    "Chinese_Warm_Woman": MiniMaxVoice(
        "Chinese_Warm_Woman", "温暖女声", "female", "温暖自然"),
    "Chinese_Gentle_Man": MiniMaxVoice(
        "Chinese_Gentle_Man", "温和男声", "male", "温和磁性"),
    "Calm_Woman": MiniMaxVoice(
        "Calm_Woman", "沉稳女声", "female", "沉稳大气"),
    "male-qn-qingse": MiniMaxVoice(
        "male-qn-qingse", "青涩男声", "male", "年轻活力"),
    "tiger_li_voice": MiniMaxVoice(
        "tiger_li_voice", "虎哥", "male", "激情带货"),
}


class MiniMaxTTSEngine:
    """MiniMax TTS — speech-2.8-hd 超自然语音"""

    API_URL = "https://api.minimax.io/v1/t2a_v2"
    MODEL = "speech-2.8-hd"

    def __init__(self, voice: str = "", voice_pool=None):
        tts_cfg = config.tts_config or {}
        mm_cfg = tts_cfg.get("minimax", {})

        self.api_key = mm_cfg.get("api_key") or os.environ.get("MINIMAX_API_KEY", "")
        self.group_id = mm_cfg.get("group_id") or os.environ.get("MINIMAX_GROUP_ID", "")

        if not self.api_key:
            raise RuntimeError(
                "MiniMax TTS 未配置: 设置环境变量 MINIMAX_API_KEY"
            )

        if voice:
            self.voice = voice
        elif voice_pool:
            self.voice = voice_pool.next()
        else:
            self.voice = mm_cfg.get("voice", "Chinese_Warm_Woman")

        self._voice_pool = voice_pool
        self.output_dir = os.path.join(config.output_dir, "_narration")
        os.makedirs(self.output_dir, exist_ok=True)

    @property
    def current_voice_name(self) -> str:
        vp = MINIMAX_VOICES.get(self.voice)
        return vp.name if vp else self.voice

    @property
    def backend_name(self) -> str:
        return "MiniMax"

    def next_voice(self) -> str:
        if self._voice_pool:
            self.voice = self._voice_pool.next()
        return self.voice

    def synthesize(self, text: str, output_path: str | None = None,
                   speech_rate: float = 1.0, volume: int = 50,
                   emotion: str = "") -> str:
        """合成语音"""
        text = text.strip()
        if not text:
            raise ValueError("合成文本不能为空")

        if output_path is None:
            output_path = os.path.join(
                self.output_dir,
                f"mm_{hashlib.md5(text.encode('utf-8')).hexdigest()[:8]}.mp3",
            )

        if os.path.exists(output_path):
            logger.info("MiniMax TTS 缓存命中: %s", output_path)
            return output_path

        body = {
            "model": self.MODEL,
            "text": text,
            "stream": False,
            "output_format": "hex",
            "language_boost": "auto",
            "voice_setting": {
                "voice_id": self.voice,
                "speed": speech_rate,
                "vol": volume / 50.0,
                "pitch": 0,
            },
            "audio_setting": {
                "sample_rate": 32000,
                "bitrate": 128000,
                "format": "mp3",
                "channel": 1,
            },
        }

        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }

        logger.info("MiniMax TTS: %s voice=%s", text[:40], self.voice)

        try:
            r = requests.post(self.API_URL, json=body, headers=headers, timeout=30)
            data = r.json()
        except Exception as e:
            raise RuntimeError(f"MiniMax API 请求失败: {e}")

        if "data" not in data or "audio" not in data["data"]:
            err = data.get("base_resp", {}).get("status_msg", "unknown")
            raise RuntimeError(f"MiniMax TTS 错误: {err}")

        audio_bytes = bytes.fromhex(data["data"]["audio"])
        with open(output_path, "wb") as f:
            f.write(audio_bytes)

        logger.info("MiniMax TTS 完成: %s (%d bytes)", output_path, len(audio_bytes))
        return output_path

    def synthesize_segments(self, segments: list[str],
                            output_path: str = "",
                            emotion: str = "",
                            pause_ms: int | None = None,
                            segment_roles: list[str] | None = None,
                            speech_rate: float = 0.0,
                            ) -> tuple[str, list[int], list[int]]:
        """分段合成"""
        if not segments:
            raise ValueError("segments 不能为空")

        tmp_dir = tempfile.mkdtemp(prefix="mm_seg_")
        seg_paths = []
        seg_durations = []

        for i, seg in enumerate(segments):
            seg_path = os.path.join(tmp_dir, f"seg_{i:03d}.mp3")
            try:
                self.synthesize(seg, seg_path,
                                speech_rate=(speech_rate if speech_rate > 0 else 1.0))
                seg_paths.append(seg_path)
                from moviepy import AudioFileClip
                ac = AudioFileClip(seg_path)
                seg_durations.append(max(int(ac.duration * 1000), 200))
                ac.close()
            except Exception as e:
                logger.error("MiniMax 分段%d失败: %s", i, e)
                fallback = max(len(seg) * 250, 500)
                seg_durations.append(fallback)
                # 与 CosyVoice/Volcano 对齐：失败段插静音占位，避免总时长与 seg_durations 错位
                from adflow.engine.tts_engine import _generate_silence_mp3
                seg_paths.append(_generate_silence_mp3(
                    fallback, tmp_dir, sample_rate=32000))

        valid = [sp for sp in seg_paths if sp]
        if not valid:
            raise RuntimeError("MiniMax 全部分段合成失败")

        concat_list = os.path.join(tmp_dir, "concat.txt")
        with open(concat_list, "w", encoding="utf-8") as f:
            for sp in valid:
                f.write(f"file '{sp}'\n")

        if not output_path:
            output_path = os.path.join(
                self.output_dir,
                f"mm_seg_{hashlib.md5(''.join(segments).encode('utf-8')).hexdigest()[:8]}.mp3")

        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
        total_sec = sum(seg_durations) / 1000.0
        afade_filter = (f"afade=t=in:st=0:d=0.03,"
                        f"afade=t=out:st={max(0, total_sec - 0.03):.4f}:d=0.03")
        subprocess.run(
            [get_ffmpeg_cmd(), "-y", "-f", "concat", "-safe", "0",
             "-i", concat_list, "-c:a", "libmp3lame", "-q:a", "2",
             "-af", afade_filter, output_path],
            capture_output=True, timeout=60,
        )

        import shutil
        shutil.rmtree(tmp_dir, ignore_errors=True)
        return output_path, seg_durations, [0] * len(seg_durations)
