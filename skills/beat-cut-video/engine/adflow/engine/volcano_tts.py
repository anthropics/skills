# -*- coding: utf-8 -*-
"""
火山引擎 TTS 引擎 — 剪映同源配音

前置条件:
  1. 注册火山引擎账号: https://www.volcengine.com/
  2. 开通语音合成服务
  3. 获取 APP_ID 和 ACCESS_TOKEN

配置方式（二选一）:
  - config.yaml → tts.volcano
  - 环境变量 → VOLCANO_TTS_APP_ID / VOLCANO_TTS_TOKEN

音色与剪映对应:
  灿灿 ← zh_female_zhaolaosa_moon_bigtts
  擎苍 ← zh_male_qingcang_moon_bigtts
  丁丁 ← zh_female_dingdang_mars_bigtts
  懂懂 ← zh_male_dongdong_mars_bigtts
  炀炀 ← zh_female_yangyang_mars_bigtts
  朝辞 ← zh_female_chaohao_mars_bigtts
  暮迟 ← zh_male_mood_happy_mars_bigtts
"""
import base64
import logging
import os
import time
import uuid
from dataclasses import dataclass

import requests

from adflow.config_loader import config

logger = logging.getLogger("adflow.tts.volcano")


# ── 音色定义 ──
@dataclass
class VolcanoVoiceProfile:
    voice_id: str
    name: str
    gender: str
    style: str


# 火山引擎 TTS 音色库
VOLCANO_VOICES: dict[str, VolcanoVoiceProfile] = {
    # ── 标准音色（已验证可用）──
    "BV001_streaming": VolcanoVoiceProfile(
        "BV001_streaming", "标准女声", "female", "标准"),
    "BV002_streaming": VolcanoVoiceProfile(
        "BV002_streaming", "标准男声", "male", "标准"),
    "BV700_streaming": VolcanoVoiceProfile(
        "BV700_streaming", "温柔女声", "female", "温柔"),
    # ── bigtts 大模型音色（需要企业认证，剪映同款）──
    "zh_female_zhaolaosa_moon_bigtts": VolcanoVoiceProfile(
        "zh_female_zhaolaosa_moon_bigtts", "灿灿", "female", "活泼"),
    "zh_male_qingcang_moon_bigtts": VolcanoVoiceProfile(
        "zh_male_qingcang_moon_bigtts", "擎苍", "male", "沉稳"),
    "zh_female_dingdang_mars_bigtts": VolcanoVoiceProfile(
        "zh_female_dingdang_mars_bigtts", "丁丁", "female", "温柔"),
    "zh_male_dongdong_mars_bigtts": VolcanoVoiceProfile(
        "zh_male_dongdong_mars_bigtts", "懂懂", "male", "年轻"),
    "zh_female_yangyang_mars_bigtts": VolcanoVoiceProfile(
        "zh_female_yangyang_mars_bigtts", "炀炀", "female", "激情"),
}


class VolcanoTTSEngine:
    """火山引擎 TTS — 剪映同源配音引擎

    API 文档: https://www.volcengine.com/docs/6561/79817
    可用音色: https://www.volcengine.com/docs/6561/97465
    """

    API_URL = "https://openspeech.bytedance.com/api/v1/tts"

    def __init__(self, voice: str = "", voice_pool=None):
        tts_cfg = config.tts_config or {}
        vol_cfg = tts_cfg.get("volcano", {})

        self.app_id = vol_cfg.get("app_id") or os.environ.get("VOLCANO_TTS_APP_ID", "")
        self.access_token = vol_cfg.get("access_token") or os.environ.get("VOLCANO_TTS_TOKEN", "")
        self.cluster = vol_cfg.get("cluster", "volcano_tts")

        if not self.app_id or not self.access_token:
            raise RuntimeError(
                "火山引擎 TTS 未配置: 请设置环境变量 "
                "VOLCANO_TTS_APP_ID 和 VOLCANO_TTS_TOKEN，"
                "或配置 config.yaml → tts.volcano"
            )

        # 初始音色
        if voice:
            self.voice = voice
        elif voice_pool:
            self.voice = voice_pool.next()
        else:
            self.voice = vol_cfg.get("voice", "BV001_streaming")

        self._voice_pool = voice_pool
        self.output_dir = os.path.join(config.output_dir, "_narration")
        os.makedirs(self.output_dir, exist_ok=True)

    @property
    def current_voice_name(self) -> str:
        vp = VOLCANO_VOICES.get(self.voice)
        return vp.name if vp else self.voice

    @property
    def backend_name(self) -> str:
        return "VolcanoTTS"

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
            # 缓存 key 纳入文本+音色+情绪+语速，避免不同参数命中同一缓存；md5 跨进程稳定
            import hashlib
            cache_key = f"{text}|{self.voice}|{emotion}|{speech_rate:.2f}".encode("utf-8")
            output_path = os.path.join(
                self.output_dir,
                f"vol_{hashlib.md5(cache_key).hexdigest()[:8]}.mp3",
            )

        if os.path.exists(output_path):
            logger.info("火山TTS 缓存命中: %s", output_path)
            return output_path

        # 情绪控制
        emotion = emotion or _detect_emotion(text)
        speed_ratio = speech_rate

        request_body = {
            "app": {
                "appid": self.app_id,
                "token": self.access_token,
                "cluster": self.cluster,
            },
            "user": {"uid": "adflow"},
            "audio": {
                "voice_type": self.voice,
                "encoding": "mp3",
                "rate": 24000,
                "speed_ratio": speed_ratio,
                "volume_ratio": volume / 50.0,
                "pitch_ratio": 1.0,
            },
            "request": {
                "reqid": str(uuid.uuid4()),
                "text": text,
                "text_type": "plain",
                "operation": "query",
            },
        }

        if emotion and emotion != "中性":
            emo_mapped = self._map_emotion(emotion)
            if emo_mapped:
                request_body["audio"]["emotion"] = emo_mapped

        logger.info(
            "火山TTS 合成: %s voice=%s emotion=%s speed=%.2f",
            text[:40], self.voice, emotion, speed_ratio)

        try:
            response = requests.post(
                self.API_URL,
                json=request_body,
                headers={
                    "Content-Type": "application/json",
                    "Authorization": f"Bearer;{self.access_token}",
                },
                timeout=30,
            )
            data = response.json()
        except Exception as e:
            raise RuntimeError(f"火山TTS API 请求失败: {e}")

        code = data.get("code")
        if code != 3000:
            msg = data.get("message", "unknown error")
            raise RuntimeError(f"火山TTS 错误 (code={code}): {msg}")

        audio_data = base64.b64decode(data["data"])
        with open(output_path, "wb") as f:
            f.write(audio_data)

        logger.info("火山TTS 完成: %s (%d bytes)", output_path, len(audio_data))
        return output_path

    def synthesize_segments(self, segments: list[str],
                            output_path: str = "",
                            emotion: str = "",
                            pause_ms: int | None = None,
                            segment_roles: list[str] | None = None,
                            speech_rate: float = 0.0,
                            ) -> tuple[str, list[int], list[int]]:
        """分段合成+拼接：每段独立配音→FFmpeg拼接+角色动态停顿→精确时间戳

        Args:
            segments: 配音文本列表
            output_path: 输出路径
            emotion: 情绪标签
            pause_ms: 段间停顿时长(ms)，None=按角色动态
            segment_roles: 每段的角色（hook/problem/product_demo/cta/b_roll）
            speech_rate: 语速倍率，0=用 config tts.speech_rate（默认1.1），>0=强制倍率
        """
        import subprocess
        import tempfile
        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd

        if not segments:
            raise ValueError("segments 不能为空")

        # ── 角色动态停顿：钩子快节奏100ms，CTA前制造期待400ms ──
        ROLE_PAUSE = {
            "hook": 100, "problem": 200, "solution": 200,
            "product_demo": 180, "b_roll": 150, "cta": 400,
        }
        if segment_roles is None:
            segment_roles = ["default"] * len(segments)

        # ── 内容寻址缓存：同 segments/voice/emotion/pause/speech_rate/roles 命中跳过合成 ──
        import hashlib
        cache_key = (f"{'|'.join(segments)}|{self.voice}|{emotion}|{pause_ms}|"
                     f"{speech_rate}|{'|'.join(segment_roles)}")
        cache_id = hashlib.md5(cache_key.encode("utf-8")).hexdigest()[:8]
        cache_path = os.path.join(self.output_dir, f"vol_seg_{cache_id}.mp3")
        meta_path = cache_path + ".meta.json"
        if os.path.exists(cache_path) and os.path.exists(meta_path):
            try:
                import json
                with open(meta_path, "r", encoding="utf-8") as f:
                    meta = json.load(f)
                if (meta.get("cache_id") == cache_id
                        and len(meta.get("seg_durations", [])) == len(segments)):
                    return cache_path, meta["seg_durations"], meta.get(
                        "pause_durations", [0] * len(segments))
            except Exception as e:
                logger.warning("火山TTS 分段缓存元数据损坏，重新合成: %s", e)

        # ── 读取段间停顿配置 ──
        if pause_ms is None:
            try:
                from adflow.config_loader import config as _cfg
                seg_tts = _cfg.get("segment_tts", {}) or {}
                pause_ms = int(seg_tts.get("pause_normal", 380))
            except Exception:
                pause_ms = 380

        tmp_dir = tempfile.mkdtemp(prefix="vol_tts_seg_")
        seg_paths = []
        seg_durations = []

        # ── 静音裁剪配置（裁掉 TTS 首尾真静音，让段间停顿=真实听感间隔）──
        from adflow.engine.audio_trim import trim_edge_silence
        _tts_cfg = config.get("segment_tts", {}) or {}
        _trim_enabled = bool(_tts_cfg.get("trim_silence", True))
        _trim_db = float(_tts_cfg.get("trim_threshold_db", -50.0))
        _trim_keep_head = int(_tts_cfg.get("trim_keep_head_ms", 20))
        _trim_keep_tail = int(_tts_cfg.get("trim_keep_tail_ms", 50))

        # ── 语速配置（角色语速 × 整体基准语速）──
        from adflow.engine.tts_engine import (
            get_speech_rate_for_role, _generate_silence_mp3)
        _base_rate = speech_rate if speech_rate > 0 else float(config.get("tts.speech_rate", 1.1))

        # ── 生成静音片段（段间停顿用）──
        silence_path = ""
        if pause_ms > 0 and len(segments) > 1:
            silence_path = os.path.join(tmp_dir, f"_silence_{pause_ms}ms.mp3")
            try:
                subprocess.run(
                    [get_ffmpeg_cmd(), "-y", "-f", "lavfi",
                     "-i", f"anullsrc=r=22050:cl=mono",
                     "-t", f"{pause_ms / 1000:.3f}",
                     "-c:a", "libmp3lame", "-q:a", "2",
                     silence_path],
                    capture_output=True, timeout=10,
                )
            except Exception:
                silence_path = ""

        for i, seg in enumerate(segments):
            seg_path = os.path.join(tmp_dir, f"seg_{i:03d}.mp3")
            _role = (segment_roles[i]
                     if segment_roles and i < len(segment_roles) else "default")
            _rate = get_speech_rate_for_role(_role, _base_rate)
            synth_ok = False
            for attempt in range(2):
                try:
                    self.synthesize(seg, seg_path, emotion=emotion, speech_rate=_rate)
                    synth_ok = True
                    break
                except Exception as e:
                    if attempt == 0:
                        logger.warning("火山TTS 分段%d失败，退避1s重试: %s", i, e)
                        time.sleep(1)
                    else:
                        logger.error("火山TTS 分段%d重试仍失败: %s", i, e)
            if synth_ok:
                if _trim_enabled:
                    # 裁掉首尾真静音，seg_durations 存真实语音时长
                    seg_path, dur_ms = trim_edge_silence(
                        seg_path, threshold_db=_trim_db,
                        keep_head_ms=_trim_keep_head,
                        keep_tail_ms=_trim_keep_tail)
                    seg_durations.append(dur_ms)
                else:
                    from moviepy import AudioFileClip
                    ac = AudioFileClip(seg_path)
                    seg_durations.append(max(int(ac.duration * 1000), 200))
                    ac.close()
                seg_paths.append(seg_path)
            else:
                # 与 CosyVoice/Edge 对齐：失败段插入等长静音占位，保证拼接总时长与
                # seg_durations 一致，否则下游字幕按 seg_durations 对齐会错位、尾部黑屏
                fallback = max(len(seg) * 250, 500)
                seg_durations.append(fallback)
                seg_paths.append(_generate_silence_mp3(
                    fallback, tmp_dir, sample_rate=22050))

        valid_paths = [sp for sp in seg_paths if sp]
        if not valid_paths:
            raise RuntimeError("火山TTS 全部分段合成失败")

        # ── FFmpeg concat 拼接（段间角色动态停顿）──
        concat_list = os.path.join(tmp_dir, "concat.txt")
        with open(concat_list, "w", encoding="utf-8") as f:
            for idx, sp in enumerate(valid_paths):
                f.write(f"file '{sp}'\n")
                if idx < len(valid_paths) - 1:
                    # 用当前段的角色决定停顿
                    role = segment_roles[idx] if idx < len(segment_roles) else "default"
                    role_pause = ROLE_PAUSE.get(role, pause_ms)
                    if role_pause > 0:
                        rp_path = os.path.join(tmp_dir, f"_rp_{idx}_{role_pause}ms.mp3")
                        if not os.path.exists(rp_path):
                            subprocess.run(
                                [get_ffmpeg_cmd(), "-y", "-f", "lavfi",
                                 "-i", f"anullsrc=r=22050:cl=mono",
                                 "-t", f"{role_pause / 1000:.3f}",
                                 "-c:a", "libmp3lame", "-q:a", "2",
                                 rp_path],
                                capture_output=True, timeout=10,
                            )
                        f.write(f"file '{rp_path}'\n")

        # ── 调整 seg_durations：角色动态停顿（同时记录每段停顿，供字幕对齐）──
        pause_durations = [0] * len(seg_durations)
        valid_count = len(valid_paths)
        dur_idx = 0
        for i, sp in enumerate(seg_paths):
            if sp in valid_paths:
                if dur_idx < valid_count - 1:
                    role = segment_roles[i] if i < len(segment_roles) else "default"
                    role_pause = ROLE_PAUSE.get(role, pause_ms)
                    seg_durations[i] += role_pause
                    pause_durations[i] = role_pause
                dur_idx += 1

        # 输出落到内容寻址路径（忽略调用方传入的 output_path，实现跨变体复用配音）
        output_path = cache_path

        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
        result = subprocess.run(
            [get_ffmpeg_cmd(), "-y", "-f", "concat", "-safe", "0",
             "-i", concat_list, "-c:a", "libmp3lame", "-q:a", "2",
             output_path],
            capture_output=True, timeout=60,
        )
        if result.returncode != 0:
            import shutil
            shutil.copy2(valid_paths[0], output_path)
            logger.warning("火山TTS 分段拼接失败，降级为单段: %s", result.stderr.decode()[-200:])
            # 降级为单段：仅保留首段真实时长（不含段间停顿），避免下游按全量时长对齐错位
            seg_durations = [seg_durations[0] - pause_durations[0]]
            pause_durations = [0]

        try:
            import shutil
            shutil.rmtree(tmp_dir, ignore_errors=True)
        except Exception:
            pass

        # 写缓存元数据（供下次命中时还原 seg_durations/pause_durations）
        try:
            import json
            with open(meta_path, "w", encoding="utf-8") as f:
                json.dump({"cache_id": cache_id,
                           "seg_durations": seg_durations,
                           "pause_durations": pause_durations},
                          f, ensure_ascii=False)
        except Exception as e:
            logger.warning("火山TTS 写缓存元数据失败: %s", e)

        return output_path, seg_durations, pause_durations

    @staticmethod
    def _map_emotion(emotion: str) -> str:
        mapping = {
            "激昂": "happy",
            "紧迫": "excited",
            "温和": "gentle",
            "悲伤": "sad",
            "愤怒": "angry",
            "惊讶": "surprised",
            "中性": "neutral",
        }
        return mapping.get(emotion, "neutral")


def _detect_emotion(text: str) -> str:
    """简单的情绪检测（避免循环导入 tts_engine）"""
    keywords = {
        "激昂": ["震撼", "重磅", "疯抢", "爆款", "绝了", "冲", "抢", "限时"],
        "紧迫": ["最后", "马上", "立刻", "仅剩", "倒计时", "手慢无", "快", "赶紧"],
        "温和": ["推荐", "分享", "好用", "喜欢", "温暖", "日常", "实用"],
    }
    for emotion, kws in keywords.items():
        if sum(1 for kw in kws if kw in text) >= 2:
            return emotion
    return "中性"
