# -*- coding: utf-8 -*-
"""
Qwen3-TTS 引擎 — 本地免费兜底方案

需要: pip install qwen3-tts
模型: Qwen/Qwen3-TTS-1.5B (自动下载)
"""
import hashlib
import logging
import os
import subprocess
import tempfile

from adflow.config_loader import config

logger = logging.getLogger("adflow.tts.qwen3")


class Qwen3TTSEngine:
    """Qwen3-TTS 本地引擎 — 最后的兜底"""

    def __init__(self, voice: str = "", voice_pool=None):
        self._available = self._check()
        self.voice = voice or "default"
        self._voice_pool = voice_pool
        self.output_dir = os.path.join(config.output_dir, "_narration")
        os.makedirs(self.output_dir, exist_ok=True)

    @staticmethod
    def _check() -> bool:
        try:
            from qwen3_tts import Qwen3TTS
            return True
        except ImportError:
            logger.warning("Qwen3-TTS 未安装: pip install qwen3-tts")
            return False

    @property
    def available(self) -> bool:
        return self._available

    @property
    def current_voice_name(self) -> str:
        return "Qwen3-TTS"

    @property
    def backend_name(self) -> str:
        return "Qwen3TTS"

    def next_voice(self) -> str:
        return self.voice

    def synthesize(self, text: str, output_path: str | None = None,
                   speech_rate: float = 1.0, volume: int = 50,
                   emotion: str = "") -> str:
        if not self._available:
            raise RuntimeError("Qwen3-TTS 不可用")

        if output_path is None:
            output_path = os.path.join(
                self.output_dir, f"q3_{hashlib.md5(text.encode('utf-8')).hexdigest()[:8]}.wav")

        if os.path.exists(output_path):
            return output_path

        try:
            from qwen3_tts import Qwen3TTS
            tts = Qwen3TTS()
            tts.synthesize(text, output_path)
            return output_path
        except Exception as e:
            raise RuntimeError(f"Qwen3-TTS 合成失败: {e}")

    def synthesize_segments(self, segments: list[str],
                            output_path: str = "",
                            emotion: str = "",
                            pause_ms: int | None = None,
                            segment_roles: list[str] | None = None,
                            speech_rate: float = 0.0,
                            ) -> tuple[str, list[int], list[int]]:
        if not segments:
            raise ValueError("segments 不能为空")

        tmp_dir = tempfile.mkdtemp(prefix="q3_seg_")
        seg_paths = []
        seg_durations = []

        for i, seg in enumerate(segments):
            seg_path = os.path.join(tmp_dir, f"seg_{i:03d}.wav")
            try:
                self.synthesize(seg, seg_path,
                                speech_rate=(speech_rate if speech_rate > 0 else 1.0))
                seg_paths.append(seg_path)
                from moviepy import AudioFileClip
                ac = AudioFileClip(seg_path)
                seg_durations.append(max(int(ac.duration * 1000), 200))
                ac.close()
            except Exception:
                fallback = max(len(seg) * 250, 500)
                seg_durations.append(fallback)
                # 与 CosyVoice/Volcano 对齐：失败段插静音占位，避免 seg_paths/seg_durations 长度错位
                silence_wav = os.path.join(tmp_dir, f"_silence_{i}_{fallback}ms.wav")
                try:
                    from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
                    subprocess.run(
                        [get_ffmpeg_cmd(), "-y", "-f", "lavfi",
                         "-i", "anullsrc=r=24000:cl=mono",
                         "-t", f"{fallback / 1000:.3f}",
                         "-c:a", "pcm_s16le", silence_wav],
                        capture_output=True, timeout=10,
                    )
                    seg_paths.append(silence_wav if os.path.exists(silence_wav) else "")
                except Exception:
                    seg_paths.append("")

        valid = [sp for sp in seg_paths if sp]
        if not valid:
            raise RuntimeError("全部分段合成失败")

        concat_list = os.path.join(tmp_dir, "concat.txt")
        with open(concat_list, "w", encoding="utf-8") as f:
            for sp in valid:
                f.write(f"file '{sp}'\n")

        if not output_path:
            output_path = os.path.join(
                self.output_dir, f"q3_seg_{hashlib.md5(''.join(segments).encode('utf-8')).hexdigest()[:8]}.mp3")

        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
        subprocess.run(
            [get_ffmpeg_cmd(), "-y", "-f", "concat", "-safe", "0",
             "-i", concat_list, "-c:a", "libmp3lame", "-q:a", "2",
             output_path],
            capture_output=True, timeout=60,
        )

        import shutil
        shutil.rmtree(tmp_dir, ignore_errors=True)
        return output_path, seg_durations, [0] * len(seg_durations)
