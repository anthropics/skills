# -*- coding: utf-8 -*-
"""
TTS 静音裁剪 — 消除段间"静音叠加"导致的长间隔

核心: 用 FFmpeg silenceremove 裁掉每段 TTS 音频首尾的"真静音"
(数字 padding)，让段间停顿值 = 真实听感间隔。

设计要点(不误伤语音表达):
  - 阈值默认 -50dB: 只裁准数字静音(<-60dB)，轻声尾音("吗/了")最低
    约 -45dB，绝不会被误判。
  - 头部保留 20ms、尾部保留 50ms: 双重余量，保护开头送气音和句末轻声余韵。
"""
import logging
import os
import subprocess

from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd, get_ffprobe_cmd

logger = logging.getLogger("adflow.audio_trim")


def _probe_duration_ms(audio_path: str) -> int:
    """FFprobe 精确读取音频时长(ms)，失败返回 0"""
    try:
        result = subprocess.run(
            [get_ffprobe_cmd(), "-v", "quiet",
             "-show_entries", "format=duration",
             "-of", "default=noprint_wrappers=1:nokey=1",
             audio_path],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10,
        )
        return int(float(result.stdout.strip()) * 1000)
    except (ValueError, subprocess.TimeoutExpired, OSError):
        return 0


def trim_edge_silence(
    audio_path: str,
    output_path: str = "",
    threshold_db: float = -50.0,
    keep_head_ms: int = 20,
    keep_tail_ms: int = 50,
    min_keep_ms: int = 150,
) -> tuple[str, int]:
    """裁掉音频首尾的准数字静音，返回 (输出路径, 裁剪后真实时长ms)。

    Args:
        audio_path: 输入音频路径
        output_path: 输出路径，空则自动生成 *_trimmed 后缀
        threshold_db: 静音阈值(dB)，-50 只裁真静音，不碰轻声
        keep_head_ms: 开头保留静音(ms)，保护首字送气音
        keep_tail_ms: 结尾保留静音(ms)，保护句末轻声余韵
        min_keep_ms: 裁剪后低于此时长则放弃裁剪(极短文本)

    Returns:
        (输出路径, 裁剪后真实时长ms)；裁剪失败时返回原路径和原时长
    """
    src_ms = _probe_duration_ms(audio_path)
    if src_ms <= 0:
        return audio_path, 0

    if not output_path:
        base, ext = os.path.splitext(audio_path)
        output_path = f"{base}_trimmed{ext}"

    # silenceremove: start_periods=1 裁开头, stop_periods=-1 裁所有结尾静音
    # start/stop_silence 是"保留"的静音量，避免切到语音边界
    af = (
        f"silenceremove=start_periods=1:start_threshold={threshold_db}dB:"
        f"start_silence={keep_head_ms / 1000:.3f}:"
        f"stop_periods=-1:stop_threshold={threshold_db}dB:"
        f"stop_silence={keep_tail_ms / 1000:.3f}"
    )
    result = subprocess.run(
        [get_ffmpeg_cmd(), "-y", "-i", audio_path,
         "-af", af, "-c:a", "libmp3lame", "-q:a", "2",
         output_path],
        capture_output=True, timeout=30,
    )
    if result.returncode != 0 or not os.path.exists(output_path):
        logger.warning("静音裁剪失败，保留原文件: %s", audio_path)
        return audio_path, src_ms

    trimmed_ms = _probe_duration_ms(output_path)
    if trimmed_ms < min_keep_ms:
        # 极短文本裁剪后过短，放弃裁剪，保留原音频
        return audio_path, src_ms

    logger.debug(
        "静音裁剪: %s %dms → %dms",
        os.path.basename(audio_path), src_ms, trimmed_ms,
    )
    return output_path, trimmed_ms
