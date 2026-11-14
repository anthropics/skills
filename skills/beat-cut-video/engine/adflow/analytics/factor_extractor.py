# -*- coding: utf-8 -*-
"""视频因子提取引擎 — FFprobe逐帧分析 + 脚本分析 + 音频分析

核心: FactorExtractor.extract() 从视频/脚本/TTS参数中提取6大类30+因子。
零额外API调用 — 只依赖 FFprobe(已有) + MoviePy(已有) + librosa(已有)。
"""

import logging
import os
import subprocess

import numpy as np

from adflow.analytics.factor_types import (
    VideoFactors, RhythmFactors, EmotionFactors, VisualFactors,
    CopyFactors, VoiceFactors, StructureFactors,
)
from adflow.engine.video_probe import VideoProbe
from adflow.engine.tts_engine import detect_emotion
from adflow.utils.ffmpeg_finder import get_ffprobe_cmd, get_ffmpeg_cmd

logger = logging.getLogger("adflow.analytics")


class FactorExtractor:
    """视频因子提取引擎 — 从视频文件 + 脚本 + 编辑参数中提取因子向量"""

    # ── 公开 API ──

    @staticmethod
    def extract(
        video_path: str = "",
        script=None,               # StoryboardScript | None
        edit_timeline=None,        # EditTimeline | None
        tts_voice: str = "",
        tts_speed: float = 1.0,
        tts_emotion: str = "",
        bgm_path: str = "",
        frame_sample_rate: int = 2,
    ) -> VideoFactors:
        """主入口: 从所有可用数据源提取完整因子快照。

        Args:
            video_path: 成品视频文件路径（可选, 用于视觉因子）
            script: StoryboardScript 对象（可选, 用于文案/情绪/结构因子）
            edit_timeline: EditTimeline 对象（可选, 用于节奏因子）
            tts_voice: TTS音色ID（可选）
            tts_speed: TTS语速（可选）
            tts_emotion: TTS情绪标签（可选, 不传则自动检测）
            bgm_path: BGM文件路径（可选, 用于音色因子）
            frame_sample_rate: 视觉分析每秒采样帧数

        Returns:
            VideoFactors 完整因子快照
        """
        factors = VideoFactors()

        # ── 节奏因子（从编辑时间线）──
        if edit_timeline is not None:
            factors.rhythm = FactorExtractor._extract_rhythm(edit_timeline)

        # ── 情绪因子（从脚本旁白）──
        if script is not None:
            factors.emotion = FactorExtractor._extract_emotion(script)

        # ── 视觉因子（从视频文件）──
        if video_path and os.path.exists(video_path):
            factors.visual = FactorExtractor._extract_visual(
                video_path, frame_sample_rate)
            factors.video_path = video_path

        # ── 文案因子（从脚本旁白）──
        if script is not None:
            factors.copy = FactorExtractor._extract_copy(script)

        # ── 音色因子（从TTS+BGM参数）──
        factors.voice = FactorExtractor._extract_voice(
            tts_voice, tts_speed, tts_emotion, bgm_path,
            narration_text=FactorExtractor._get_narration_text(script),
        )

        # ── 结构因子（从脚本+时间线）──
        if script is not None:
            factors.structure = FactorExtractor._extract_structure(
                script, edit_timeline)

        return factors

    # ═══════════════════════════════════
    # 各维度提取方法
    # ═══════════════════════════════════

    @staticmethod
    def _extract_rhythm(timeline) -> RhythmFactors:
        """从编辑时间线提取节奏因子"""
        shots = getattr(timeline, 'shots', []) or []
        n = len(shots)
        if n == 0:
            return RhythmFactors()

        durations = []
        total_ms = 0
        for shot in shots:
            dur = (getattr(shot, 'end_ms', 0) or 0) - (getattr(shot, 'start_ms', 0) or 0)
            if dur > 0:
                durations.append(dur / 1000.0)  # → 秒
                total_ms += dur

        total_sec = total_ms / 1000.0 if total_ms > 0 else 1.0
        avg_dur = np.mean(durations) if durations else 0.0
        var_dur = np.std(durations) if len(durations) > 1 else 0.0

        return RhythmFactors(
            avg_shot_duration=round(avg_dur, 2),
            shot_count=n,
            shot_duration_variance=round(var_dur, 2),
            cut_speed=round(n / total_sec, 3),
            tempo_bpm=0.0,  # 需要BGM文件才能提取, 见 _extract_voice
        )

    @staticmethod
    def _extract_emotion(script) -> EmotionFactors:
        """从脚本旁白提取情绪曲线因子"""
        shots = getattr(script, 'shots', []) or []
        # 用已有的 detect_emotion 对每段旁白做情绪标注
        emotions = []
        for shot in shots:
            text = getattr(shot, 'narration_text', '') or ''
            if text.strip():
                emotions.append(detect_emotion(text))
            else:
                emotions.append("中性")

        # 情绪→能量映射
        ENERGY_MAP = {
            "激昂": 9, "紧迫": 8, "愤怒": 8, "惊讶": 7,
            "恐惧": 6, "温和": 4, "悲伤": 3, "中性": 5,
        }
        energy = [ENERGY_MAP.get(e, 5) for e in emotions]
        avg_energy = np.mean(energy) if energy else 5.0

        # 情绪峰值位置
        if energy:
            peak_idx = int(np.argmax(energy))
            peak_pos = peak_idx / len(energy) if len(energy) > 1 else 0.5
        else:
            peak_pos = 0.5

        # 情绪波动率
        changes = sum(1 for i in range(1, len(emotions))
                      if emotions[i] != emotions[i - 1])
        volatility = changes / len(emotions) if len(emotions) > 1 else 0.0

        hook_emotion = emotions[0] if emotions else "中性"

        return EmotionFactors(
            emotion_sequence=emotions,
            peak_emotion_position=round(peak_pos, 3),
            emotion_volatility=round(volatility, 3),
            hook_emotion=hook_emotion,
            emotion_energy=round(avg_energy, 1),
        )

    @staticmethod
    def _extract_visual(video_path: str, sample_rate: int = 2
                         ) -> VisualFactors:
        """从视频文件提取视觉因子（FFprobe逐帧采样）。

        策略: 不依赖 MoviePy 逐帧加载（内存杀手），用 FFmpeg 直接输出
        帧统计数据，零 Python 层解码开销。
        """
        try:
            info = VideoProbe.probe(video_path)
        except Exception as e:
            logger.warning("FFprobe 失败: %s", e)
            return VisualFactors()

        dur = max(info.duration_sec, 1.0)
        fps = max(info.fps, 1.0)

        # 采样策略: 最多取60帧
        max_frames = min(60, int(dur * sample_rate))
        interval = max(1.0, dur / max_frames)

        # FFmpeg 直接输出帧统计数据（signalstats filter）
        # 返回每帧的 Y(亮度)均值
        try:
            cmd = [
                get_ffmpeg_cmd(), "-v", "info",
                "-i", video_path,
                "-vf", f"fps=1/{interval},signalstats",
                "-f", "null", "-",
            ]
            # signalstats 输出到 stderr 的 metadata
            result = subprocess.run(
                cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=30)
            stderr = result.stderr or ""

            # 解析 signalstats 输出（亮度+饱和度）
            brightness_vals = []
            saturation_vals = []
            for line in stderr.split("\n"):
                if "YAVG" in line:
                    try:
                        val = float(line.split("YAVG=")[-1].split()[0])
                        brightness_vals.append(val)
                    except (ValueError, IndexError):
                        pass
                if "SATAVG" in line:
                    try:
                        val = float(line.split("SATAVG=")[-1].split()[0])
                        saturation_vals.append(val / 255.0)
                    except (ValueError, IndexError):
                        pass

            if not brightness_vals:
                brightness_vals = FactorExtractor._sample_brightness(
                    video_path, max_frames)

            b_mean = np.mean(brightness_vals) if brightness_vals else 128.0
            b_var = np.std(brightness_vals) if brightness_vals else 0.0
            sat_mean = np.mean(saturation_vals) if saturation_vals else 0.5

            # 运动强度：帧间亮度差的均方根
            motion = 0.3
            if len(brightness_vals) >= 2:
                diffs = [abs(brightness_vals[i] - brightness_vals[i-1])
                         for i in range(1, len(brightness_vals))]
                motion = min(1.0, np.mean(diffs) / 30.0) if diffs else 0.3

        except Exception as e:
            logger.warning("视觉分析失败: %s, 使用默认值", e)
            b_mean, b_var = 128.0, 0.0
            sat_mean = 0.5
            motion = 0.3

        # 场景切换率（FFprobe scene detection）
        scene_rate = FactorExtractor._detect_scene_changes(video_path, dur)

        return VisualFactors(
            brightness_mean=round(b_mean, 1),
            brightness_variance=round(b_var, 1),
            color_saturation=round(sat_mean, 3),
            scene_change_rate=round(scene_rate, 3),
            motion_intensity=round(motion, 3),
        )

    @staticmethod
    def _extract_copy(script) -> CopyFactors:
        """从脚本旁白提取文案密度因子"""
        shots = getattr(script, 'shots', []) or []
        all_text = ""
        for shot in shots:
            text = getattr(shot, 'narration_text', '') or ''
            all_text += text

        if not all_text.strip():
            return CopyFactors()

        # 总字数和时长
        char_count = len(all_text.replace(" ", ""))
        total_dur = 0
        for shot in shots:
            total_dur += (getattr(shot, 'duration_ms', 0) or 0)
        total_sec = total_dur / 1000.0 if total_dur > 0 else 1.0

        # 语速
        wps = char_count / total_sec

        # 行动词密度
        # 注：「独家/仅剩/手慢无」已移除——它们与 compliance/ad_law_checker.py 的
        # 敏感词表冲突（绝对化用语/虚假紧迫），作为正向因子会反向鼓励违规词，故不统计
        POWER_WORDS = [
            "限时", "马上", "立刻", "抢", "点击", "下单", "错过",
            "爆款", "限量", "必入",
            "免费", "优惠", "折扣", "秒杀", "捡漏", "天花板",
        ]
        power_count = sum(1 for w in POWER_WORDS if w in all_text)
        keyword_density = power_count / max(char_count, 1)

        # CTA位置
        cta_text = getattr(script, 'cta_text', '') or ''
        cta_pos = 1.0
        if cta_text and script.shots:
            # 找CTA镜头位置
            for i, shot in enumerate(script.shots):
                if getattr(shot, 'role', '') == 'cta':
                    cta_pos = i / len(script.shots)
                    break

        # 平均句长
        sentences = [s.strip() for s in all_text.replace("。", ".").split(".")
                     if s.strip()]
        avg_sent_len = np.mean([len(s) for s in sentences]) if sentences else 0

        # 问句占比
        question_count = all_text.count("？") + all_text.count("?")
        total_sentences = max(len(sentences), 1)
        question_ratio = question_count / total_sentences

        return CopyFactors(
            words_per_second=round(wps, 1),
            keyword_density=round(keyword_density, 4),
            cta_position_ratio=round(cta_pos, 3),
            sentence_length_avg=round(avg_sent_len, 1),
            question_ratio=round(question_ratio, 3),
            power_word_count=power_count,
        )

    @staticmethod
    def _extract_voice(tts_voice: str, tts_speed: float,
                       tts_emotion: str, bgm_path: str,
                       narration_text: str = "") -> VoiceFactors:
        """从TTS+BGM参数提取音色因子"""
        # 性别
        gender = ""
        if "xiaoxia" in tts_voice or "xiaoyi" in tts_voice or \
           "jing" in tts_voice or "shao" in tts_voice or \
           "chun" in tts_voice or "longxia" in tts_voice:
            gender = "female"
        elif "bai" in tts_voice or "yun" in tts_voice or \
             "cheng" in tts_voice or "fei" in tts_voice or \
             "ye" in tts_voice:
            gender = "male"

        # 情绪
        emotion = tts_emotion or detect_emotion(narration_text) or "中性"

        # BGM 能量
        bgm_energy = FactorExtractor._extract_bgm_energy(bgm_path)

        # 音画协调度: 配音情绪 vs 假设BGM情绪
        BGM_EMOTION_MAP = {
            "激昂": 0.9, "紧迫": 0.85, "温和": 0.5, "悲伤": 0.3,
        }
        voice_energy_map = {"激昂": 0.9, "紧迫": 0.8, "温和": 0.4, "悲伤": 0.3,
                           "愤怒": 0.95, "恐惧": 0.7, "惊讶": 0.6, "中性": 0.5}
        ve = voice_energy_map.get(emotion, 0.5)
        be = BGM_EMOTION_MAP.get(emotion, 0.5)
        match_score = 1.0 - abs(ve - be)

        return VoiceFactors(
            voice_gender=gender,
            voice_speed=round(tts_speed, 2),
            voice_emotion=emotion,
            bgm_energy=round(bgm_energy, 3),
            voice_bgm_match=round(match_score, 3),
            has_bgm=bool(bgm_path and os.path.exists(bgm_path)),
        )

    @staticmethod
    def _extract_structure(script, timeline=None) -> StructureFactors:
        """从脚本+时间线提取结构比例因子"""
        shots = getattr(script, 'shots', []) or []

        # 总时长
        total_ms = 0
        hook_ms = 0
        product_ms = 0
        cta_ms = 0
        roles = set()
        first_product_idx = -1

        for i, shot in enumerate(shots):
            dur = getattr(shot, 'duration_ms', 0) or 0
            total_ms += dur
            role = getattr(shot, 'role', '') or ''
            roles.add(role)

            if role == 'hook':
                hook_ms += dur
            elif role in ('product_demo', 'solution'):
                product_ms += dur
                if first_product_idx < 0:
                    first_product_idx = i
            elif role == 'cta':
                cta_ms += dur

        total_sec = total_ms / 1000.0 if total_ms > 0 else 1.0
        n = len(shots)

        # 结构模式识别
        hook_first = (getattr(shots[0], 'role', '') == 'hook') if shots else False
        if hook_first and cta_ms > 0:
            pattern = "hook-first"
        elif not hook_first:
            pattern = "direct-sell"
        else:
            pattern = "story"

        return StructureFactors(
            hook_ratio=round(hook_ms / total_ms, 3) if total_ms > 0 else 0,
            product_intro_time=round(first_product_idx / n, 3) if first_product_idx >= 0 and n > 0 else 0.5,
            cta_duration=round(cta_ms / 1000.0, 1),
            total_duration=round(total_sec, 1),
            shot_role_diversity=round(len(roles) / 9, 3),  # 9种角色
            structure_pattern=pattern,
        )

    # ═══════════════════════════════════
    # 辅助方法
    # ═══════════════════════════════════

    @staticmethod
    def _sample_brightness(video_path: str, max_frames: int = 60
                           ) -> list[float]:
        """FFmpeg简单亮度采样（signalstats失败时的fallback）"""
        try:
            cmd = [
                get_ffmpeg_cmd(), "-v", "quiet",
                "-i", video_path,
                "-vf", f"fps=1,scale=32:32,format=gray",
                "-f", "rawvideo", "-pix_fmt", "gray", "-"
            ]
            result = subprocess.run(
                cmd, capture_output=True, timeout=30)
            raw = result.stdout
            if not raw:
                return []
            # 每32×32=1024字节一帧，取均值
            frame_size = 32 * 32
            vals = []
            for i in range(0, len(raw), frame_size):
                chunk = raw[i:i + frame_size]
                if len(chunk) < frame_size:
                    break
                vals.append(sum(chunk) / len(chunk))
                if len(vals) >= max_frames:
                    break
            return vals
        except Exception:
            return []

    @staticmethod
    def _detect_scene_changes(video_path: str, duration_sec: float
                              ) -> float:
        """FFprobe场景检测 → 场景切换率(次/秒)"""
        try:
            cmd = [
                get_ffprobe_cmd(), "-v", "quiet",
                "-show_frames", "-select_streams", "v:0",
                "-show_entries", "frame=pict_type",
                video_path,
            ]
            result = subprocess.run(
                cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=30)
            # 统计 I 帧数量（I帧≈场景切换）
            i_count = result.stdout.count("pict_type=I")
            dur = max(duration_sec, 1.0)
            return i_count / dur
        except Exception:
            return 0.0

    @staticmethod
    def _extract_bgm_energy(bgm_path: str) -> float:
        """从BGM文件提取RMS能量(0-1)"""
        if not bgm_path or not os.path.exists(bgm_path):
            return 0.0
        try:
            import librosa
            y, sr = librosa.load(bgm_path, sr=None, duration=10)
            rms = np.sqrt(np.mean(y ** 2))
            # 归一化到 0-1（经验值: 典型BGM RMS≈0.1-0.3）
            return float(np.clip(rms * 5, 0.0, 1.0))
        except Exception:
            return 0.5

    @staticmethod
    def _get_narration_text(script) -> str:
        """从脚本中提取完整旁白文本"""
        if script is None:
            return ""
        shots = getattr(script, 'shots', []) or []
        texts = []
        for shot in shots:
            text = getattr(shot, 'narration_text', '') or ''
            if text.strip():
                texts.append(text)
        return "。".join(texts)
