# -*- coding: utf-8 -*-
"""
配音质量过滤器 — 6维度评分

维度:
  1. audio_quality        — 音频质量（clipping/噪声/静音）
  2. duration_match       — 时长与脚本预期匹配度
  3. voice_fit            — 音色与品类/情绪匹配度
  4. pace                 — 语速合理性
  5. volume_consistency   — 音量一致性
  6. alignment            — 字幕对齐精度（根据方法评分）
"""
import logging
import statistics

from adflow.filters.base_filter import BaseFilter, FilterResult, Verdict, weighted_total

logger = logging.getLogger("adflow.filters.tts")


class TTSFilter(BaseFilter):
    """配音质量过滤器"""

    # 品类-音色推荐表（音色名包含这些关键词即为匹配）
    VOICE_CATEGORY_MAP = {
        "零食": {"灿灿", "炀炀", "丁丁", "晓晓", "晓伊", "云希"},
        "护肤品": {"灿灿", "丁丁", "朝辞", "晓晓", "晓墨", "晓睿"},
        "数码": {"擎苍", "懂懂", "暮迟", "云扬", "云健", "云野"},
        "母婴": {"丁丁", "少女", "朝辞", "晓伊", "晓涵"},
        "运动": {"炀炀", "擎苍", "懂懂", "云野", "云枫"},
        "服饰": {"灿灿", "少女", "朝辞", "晓晓", "晓萱"},
    }

    def __init__(self):
        super().__init__(
            name="配音过滤",
            pass_threshold=6.0,
            warning_threshold=4.0,
            max_retries=2,
        )

    def _evaluate(self, data: tuple, context: dict) -> FilterResult:
        """data = (audio_path, script)"""
        audio_path, script = data
        sub_scores = {}
        issues = []
        suggestions = []

        # 1. 音频质量检测
        sub_scores["audio_quality"] = self._check_audio_quality(audio_path)
        if sub_scores["audio_quality"] < 5:
            issues.append("音频质量差（可能有 clipping/噪声/静音）")
            suggestions.append("检查 TTS 引擎参数，降低 volume_ratio")

        # 2. 时长匹配
        expected_ms = sum(s.duration_ms for s in script.shots)
        actual_ms = self._get_audio_duration_ms(audio_path)
        if expected_ms > 0 and actual_ms > 0:
            ratio = actual_ms / expected_ms
            if 0.85 <= ratio <= 1.15:
                sub_scores["duration_match"] = 8
            elif 0.7 <= ratio <= 1.3:
                sub_scores["duration_match"] = 5
                issues.append(
                    f"时长偏差: 预期{expected_ms}ms 实际{actual_ms}ms")
                suggestions.append("调整 TTS 语速参数 speech_rate")
            else:
                sub_scores["duration_match"] = 2
                issues.append(
                    f"时长严重不匹配: 预期{expected_ms}ms 实际{actual_ms}ms")
        else:
            sub_scores["duration_match"] = 7

        # 3. 音色匹配度
        voice_name = context.get("voice_name", "")
        category = context.get("category", "")
        sub_scores["voice_fit"] = self._score_voice_fit(voice_name, category)
        if sub_scores["voice_fit"] < 5:
            issues.append(
                f"音色 '{voice_name}' 与品类 '{category}' 匹配度低")
            suggestions.append("尝试更换音色（如零食类推荐活泼女声）")

        # 4. 语速合理性
        all_text = " ".join(s.narration_text or "" for s in script.shots)
        if actual_ms > 0 and all_text:
            chars_per_sec = len(all_text) / (actual_ms / 1000)
            if 4 <= chars_per_sec <= 7:
                sub_scores["pace"] = 9
            elif 3 <= chars_per_sec <= 8:
                sub_scores["pace"] = 6
                if chars_per_sec > 7:
                    suggestions.append("语速偏快，考虑降低 speech_rate")
                else:
                    suggestions.append("语速偏慢，考虑提高 speech_rate")
            else:
                sub_scores["pace"] = 3
                issues.append(f"语速异常: {chars_per_sec:.1f}字/秒")
        else:
            sub_scores["pace"] = 6

        # 5. 音量一致性
        sub_scores["volume_consistency"] = self._check_volume(audio_path)

        # 6. 对齐精度
        alignment_method = context.get("alignment_method", "")
        sub_scores["alignment"] = self._score_alignment(alignment_method)

        # 加权
        weights = {
            "audio_quality": 0.20,
            "duration_match": 0.15,
            "voice_fit": 0.20,
            "pace": 0.15,
            "volume_consistency": 0.15,
            "alignment": 0.15,
        }
        total = weighted_total(sub_scores, weights)

        return FilterResult(
            verdict=Verdict.PASS,
            score=total,
            sub_scores=sub_scores,
            issues=issues,
            suggestions=suggestions,
        )

    @staticmethod
    def _check_audio_quality(audio_path: str) -> float:
        """检测音频质量（DC offset / clipping / 静音）"""
        try:
            from pydub import AudioSegment
            audio = AudioSegment.from_file(audio_path)
            score = 8.0
            if abs(audio.dc_offset) > 0.1:
                score -= 2
            if audio.max > audio.max_possible * 0.99:
                score -= 3
            if audio.dBFS < -40:
                score -= 2
            return max(0, min(10, score))
        except ImportError:
            return 7  # pydub 未安装给中等分
        except Exception:
            return 7

    @staticmethod
    def _get_audio_duration_ms(audio_path: str) -> int:
        """获取音频时长（毫秒）"""
        try:
            from moviepy import AudioFileClip
            ac = AudioFileClip(audio_path)
            ms = int(ac.duration * 1000)
            ac.close()
            return ms
        except Exception:
            return 0

    @classmethod
    def _score_voice_fit(cls, voice_name: str, category: str) -> float:
        """评估音色与品类的匹配度"""
        if not category:
            return 7
        rec_names = cls.VOICE_CATEGORY_MAP.get(category, set())
        if not rec_names:
            return 7
        for name in rec_names:
            if name in voice_name:
                return 9
        return 5

    @staticmethod
    def _check_volume(audio_path: str) -> float:
        """检测音量一致性（分段标准差）"""
        try:
            from pydub import AudioSegment
            audio = AudioSegment.from_file(audio_path)
            chunk_ms = 1000
            chunks = [audio[i:i + chunk_ms]
                      for i in range(0, len(audio), chunk_ms)]
            if len(chunks) < 2:
                return 8
            volumes = [c.dBFS for c in chunks if c.dBFS > -float('inf')]
            if len(volumes) < 2:
                return 5
            stdev = statistics.stdev(volumes)
            if stdev < 3:
                return 9
            elif stdev < 6:
                return 6
            else:
                return 3
        except ImportError:
            return 7
        except Exception:
            return 7

    @staticmethod
    def _score_alignment(method: str) -> float:
        """评估对齐方法精度"""
        scores = {
            "segment_tts": 10,      # 分段合成，零漂移
            "edge_submaker": 8,     # 词级时间戳，~50ms
            "aeneas": 6,            # aeneas 对齐，中文精度一般
            "char_ratio": 3,        # 字数比例估算
        }
        return scores.get(method, 5)
