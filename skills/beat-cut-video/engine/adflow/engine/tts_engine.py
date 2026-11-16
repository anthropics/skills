# -*- coding: utf-8 -*-
"""
AdFlow 语音合成引擎 — 双后端 + 情绪控制

后端:
  1. CosyVoice (阿里 DashScope)  — 9个系统音色, instruction情绪控制
  2. Edge-TTS (Microsoft)        — 30+中文音色, SSML情绪控制, 完全免费

情绪: 自动从文本检测情绪(激昂/温和/紧迫/悲伤/喜悦), 注入合成参数
"""
import hashlib
import os
import logging
import asyncio
from dataclasses import dataclass

from adflow.config_loader import config

logger = logging.getLogger("adflow.tts")

# ═══════════════════════════════════════
# 辅助函数
# ═══════════════════════════════════════


def _get_pause_normal_ms() -> int:
    """读取 segment_tts.pause_normal 配置，单位ms"""
    try:
        from adflow.config_loader import config
        seg_tts = config.get("segment_tts", {}) or {}
        return int(seg_tts.get("pause_normal", 380))
    except Exception:
        return 300


def _generate_silence_mp3(duration_ms: int, tmp_dir: str,
                          sample_rate: int = 22050) -> str:
    """用 FFmpeg 生成一段静音 mp3，返回文件路径。
    失败时返回空字符串，调用方应跳过静音插入。"""
    import subprocess
    from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd

    silence_path = os.path.join(tmp_dir, f"_silence_{duration_ms}ms.mp3")
    dur_sec = duration_ms / 1000.0
    result = subprocess.run(
        [get_ffmpeg_cmd(), "-y", "-f", "lavfi",
         "-i", f"anullsrc=r={sample_rate}:cl=mono",
         "-t", f"{dur_sec:.3f}",
         "-c:a", "libmp3lame", "-q:a", "2",
         silence_path],
        capture_output=True, timeout=10,
    )
    if result.returncode != 0 or not os.path.exists(silence_path):
        logger.warning("静音生成失败: %s", result.stderr.decode()[-120:] if result.stderr else "")
        return ""
    return silence_path


# ═══════════════════════════════════════
# 音色定义
# ═══════════════════════════════════════

@dataclass
class VoiceProfile:
    voice_id: str
    name: str
    gender: str       # "female" | "male"
    style: str        # "活泼" | "沉稳" | "温柔" | "专业" | "激情" | "年轻"


# ── CosyVoice 音色 ──
COSY_VOICES: dict[str, VoiceProfile] = {
    "longxiaoxia": VoiceProfile("longxiaoxia", "龙小夏", "female", "活泼"),
    "longjing":    VoiceProfile("longjing",    "龙婧",   "female", "温柔"),
    "longshao":    VoiceProfile("longshao",    "龙韶",   "female", "专业"),
    "longchun":    VoiceProfile("longchun",    "龙纯",   "female", "清新"),
    "longxiaobai": VoiceProfile("longxiaobai", "龙小白", "male",   "年轻"),
    "longyuan":    VoiceProfile("longyuan",    "龙源",   "male",   "沉稳"),
    "longfei":     VoiceProfile("longfei",     "龙飞",   "male",   "活力"),
    "longcheng":   VoiceProfile("longcheng",   "龙成",   "male",   "成熟"),
    "longye":      VoiceProfile("longye",      "龙野",   "male",   "激情"),
}

# ── Edge-TTS 中文音色（最常用的12个，类似剪映内置配音）──
EDGE_VOICES: dict[str, VoiceProfile] = {
    # 女声
    "zh-CN-XiaoxiaoNeural":  VoiceProfile("zh-CN-XiaoxiaoNeural",  "晓晓",   "female", "活泼"),
    "zh-CN-XiaoyiNeural":    VoiceProfile("zh-CN-XiaoyiNeural",    "晓伊",   "female", "温柔"),
    "zh-CN-XiaohanNeural":   VoiceProfile("zh-CN-XiaohanNeural",   "晓涵",   "female", "清新"),
    "zh-CN-XiaomoNeural":    VoiceProfile("zh-CN-XiaomoNeural",    "晓墨",   "female", "专业"),
    "zh-CN-XiaoruiNeural":   VoiceProfile("zh-CN-XiaoruiNeural",   "晓睿",   "female", "沉稳"),
    "zh-CN-XiaoxuanNeural":  VoiceProfile("zh-CN-XiaoxuanNeural",  "晓萱",   "female", "活泼"),
    # 男声
    "zh-CN-YunxiNeural":     VoiceProfile("zh-CN-YunxiNeural",     "云希",   "male",   "年轻"),
    "zh-CN-YunyangNeural":   VoiceProfile("zh-CN-YunyangNeural",   "云扬",   "male",   "专业"),
    "zh-CN-YunjianNeural":   VoiceProfile("zh-CN-YunjianNeural",   "云健",   "male",   "沉稳"),
    "zh-CN-YunyeNeural":     VoiceProfile("zh-CN-YunyeNeural",     "云野",   "male",   "活力"),
    "zh-CN-YunhaoNeural":    VoiceProfile("zh-CN-YunhaoNeural",    "云皓",   "male",   "成熟"),
    "zh-CN-YunfengNeural":   VoiceProfile("zh-CN-YunfengNeural",   "云枫",   "male",   "激情"),
}


# ═══════════════════════════════════════
# 情绪定义 + 自动检测
# ═══════════════════════════════════════

# 情绪 → (CosyVoice instruction, Edge-TTS express-as, SSML prosody)
EMOTION_MAP = {
    "激昂": {
        "cosy_instruction": "你说话的情感是happy。",
        "edge_style": "cheerful",
        "rate": "+15%", "pitch": "+10%",
    },
    "紧迫": {
        "cosy_instruction": "你正在进行广告促销，你说话的情感是happy。",
        "edge_style": "excited",
        "rate": "+20%", "pitch": "+8%",
    },
    "温和": {
        "cosy_instruction": "你说话的情感是neutral。",
        "edge_style": "gentle",
        "rate": "-5%", "pitch": "0%",
    },
    "悲伤": {
        "cosy_instruction": "你说话的情感是sad。",
        "edge_style": "sad",
        "rate": "-10%", "pitch": "-8%",
    },
    "愤怒": {
        "cosy_instruction": "你说话的情感是angry。",
        "edge_style": "angry",
        "rate": "+25%", "pitch": "+12%",
    },
    "恐惧": {
        "cosy_instruction": "你说话的情感是fearful。",
        "edge_style": "fearful",
        "rate": "+10%", "pitch": "+5%",
    },
    "惊讶": {
        "cosy_instruction": "你说话的情感是surprised。",
        "edge_style": "surprised",
        "rate": "+15%", "pitch": "+15%",
    },
    "中性": {
        "cosy_instruction": "你说话的情感是neutral。",
        "edge_style": "neutral",
        "rate": "0%", "pitch": "0%",
    },
}


# ═══════════════════════════════════════
# 语速分段控制 — 参考短视频广告配音最佳实践
# ═══════════════════════════════════════

SHOT_ROLE_SPEED = {
    "hook": 1.15,          # 钩子部分语速快 15%，制造紧迫感+信息密度
    "problem": 1.05,       # 痛点稍快，保持节奏
    "solution": 1.0,       # 解决方案正常语速
    "product_demo": 1.0,   # 产品演示正常
    "comparison": 1.0,     # 对比正常
    "testimonial": 0.95,   # 证言稍慢，增加可信度
    "cta": 0.9,            # CTA放慢，确保每个字都听清
    "transition": 1.0,     # 过渡正常
    "b_roll": 1.0,         # B-roll正常
}


def get_speech_rate_for_role(role: str, base_rate: float = 1.0) -> float:
    """根据分镜角色获取语速倍率"""
    multiplier = SHOT_ROLE_SPEED.get(role, 1.0)
    return base_rate * multiplier


# 情绪关键词 → 触发情绪
EMOTION_KEYWORDS = {
    "激昂": ["震撼", "重磅", "疯抢", "爆款", "惊呆了", "太牛了", "绝了",
             "限时", "错过", "必入", "冲", "抢", "史低", "天花板"],
    "紧迫": ["最后", "马上", "立刻", "仅剩", "倒计时", "手慢无", "快",
             "赶紧", "机会", "不等", "就现在", "秒杀", "限量"],
    "温和": ["推荐", "分享", "好用", "喜欢", "温暖", "日常", "实用",
             "小巧", "方便", "舒服", "简单", "划算"],
    "悲伤": ["遗憾", "可惜", "难过", "心酸", "泪目", "不行了", "撑不住"],
    "愤怒": ["太坑", "气死", "无语", "绝不", "居然", "垃圾", "凭什么"],
    "惊讶": ["竟然", "居然", "没想到", "天哪", "我的天", "不可思议"],
    "恐惧": ["担心", "害怕", "危险", "小心", "注意", "风险"],
}


def detect_emotion(text: str) -> str:
    """从文本自动检测情绪。

    规则: 统计各情绪关键词命中次数, 命中≥2个→返回该情绪, 否则返回"中性"。
    """
    scores = {}
    for emotion, keywords in EMOTION_KEYWORDS.items():
        hits = sum(1 for kw in keywords if kw in text)
        if hits > 0:
            scores[emotion] = hits

    if not scores:
        return "中性"

    # 取命中最多且≥2的情绪
    best = max(scores, key=scores.get)
    return best if scores[best] >= 2 else "中性"


def get_emotion_config(emotion: str) -> dict:
    """获取情绪的参数配置，不存在则返回'中性'"""
    return EMOTION_MAP.get(emotion, EMOTION_MAP["中性"])


# ═══════════════════════════════════════
# 音色池 (CosyVoice / Edge-TTS 通用)
# ═══════════════════════════════════════

class VoicePool:
    """音色池 — 按策略轮换音色，支持 CosyVoice 和 Edge-TTS"""

    def __init__(self, strategy: str = "round_robin", gender: str = "any",
                 voice_dict: dict[str, VoiceProfile] | None = None):
        self.strategy = strategy
        self.gender = gender
        self._idx = 0
        vd = voice_dict or COSY_VOICES

        # 按性别过滤
        if gender == "female":
            filtered = {k: v for k, v in vd.items() if v.gender == "female"}
        elif gender == "male":
            filtered = {k: v for k, v in vd.items() if v.gender == "male"}
        else:
            filtered = dict(vd)

        # 男女交替则交织排列
        if strategy == "gender_alternate" and gender == "any":
            females = [k for k, v in vd.items() if v.gender == "female"]
            males = [k for k, v in vd.items() if v.gender == "male"]
            self._pool = []
            for i in range(max(len(females), len(males))):
                if i < len(females):
                    self._pool.append(females[i])
                if i < len(males):
                    self._pool.append(males[i])
        else:
            self._pool = list(filtered.keys())

    def next(self) -> str:
        if not self._pool:
            return "longxiaoxia"
        if self.strategy == "random":
            import random
            return random.choice(self._pool)
        voice = self._pool[self._idx % len(self._pool)]
        self._idx += 1
        return voice

    def current(self) -> str:
        if not self._pool:
            return "longxiaoxia"
        return self._pool[self._idx % len(self._pool)]


def get_voice_dict_for_backend(backend: str) -> dict:
    """按后端返回音色字典（供 VoicePool 轮换音色）。

    各后端音色 Profile 均有 gender 属性，可直接用于 VoicePool 过滤。
    """
    if backend == "volcano":
        from adflow.engine.volcano_tts import VOLCANO_VOICES
        # bigtts 音色需企业认证，未认证会合成失败；认证后在 config 打开 use_bigtts 即可
        use_bigtts = bool((config.tts_config or {}).get("volcano", {}).get("use_bigtts", False))
        if use_bigtts:
            return VOLCANO_VOICES
        return {k: v for k, v in VOLCANO_VOICES.items() if k.startswith("BV")}
    if backend == "edge":
        return EDGE_VOICES
    if backend == "minimax":
        from adflow.engine.minimax_tts import MINIMAX_VOICES
        return MINIMAX_VOICES
    return COSY_VOICES


def resolve_voice_gender(voice_id: str, backend: str) -> str:
    """按音色 id 反查性别（"female"|"male"）；未知/本地兜底返回空串。

    供 pipeline 逐 script 记录配音性别，用于「女配音→女数字人、男配音→男数字人」。
    """
    if not voice_id:
        return ""
    profile = get_voice_dict_for_backend(backend).get(voice_id)
    return profile.gender if profile else ""


# ═══════════════════════════════════════
# CosyVoice 引擎（已有 + 情绪控制升级）
# ═══════════════════════════════════════

class CosyVoiceEngine:
    """阿里百炼 CosyVoice TTS — 支持 instruction 情绪控制"""

    MODEL_DEFAULT = "cosyvoice-v1"
    # cosyvoice-v1 支持 instruction 的音色（大部分不支持, 先列出来备用）
    INSTRUCT_VOICES = {"longanyang"}  # v3-flash 才广泛支持

    def __init__(self, voice: str = "", voice_pool: VoicePool | None = None,
                 model: str = ""):
        self.api_key = config.llm_api_key or os.environ.get("DASHSCOPE_API_KEY", "")
        self.model = model or self.MODEL_DEFAULT
        self._voice_pool = voice_pool

        if voice:
            self.voice = voice
        elif voice_pool:
            self.voice = voice_pool.next()
        else:
            tts_cfg = config.tts_config or {}
            self.voice = tts_cfg.get("voice", "longxiaoxia")

        self.output_dir = os.path.join(config.output_dir, "_narration")
        os.makedirs(self.output_dir, exist_ok=True)

        import dashscope
        dashscope.api_key = self.api_key
        dashscope.base_websocket_api_url = (
            "wss://dashscope.aliyuncs.com/api-ws/v1/inference"
        )

    @property
    def current_voice_name(self) -> str:
        vp = COSY_VOICES.get(self.voice)
        return vp.name if vp else self.voice

    def next_voice(self) -> str:
        if self._voice_pool:
            self.voice = self._voice_pool.next()
        return self.voice

    @property
    def backend_name(self) -> str:
        return "CosyVoice"

    def synthesize(self, text: str, output_path: str | None = None,
                   speech_rate: float = 1.0, volume: int = 50,
                   emotion: str = "") -> str:
        """合成语音，支持情绪控制 (instruction 参数)"""
        text = text.strip()
        if not text:
            raise ValueError("合成文本不能为空")

        # 提前确定最终情绪，纳入缓存 key（避免同文本不同情绪/音色/语速错误命中缓存）
        emotion = emotion or detect_emotion(text)

        if output_path is None:
            cache_key = f"{text}|{self.voice}|{emotion}|{speech_rate:.2f}".encode("utf-8")
            output_path = os.path.join(
                self.output_dir,
                f"cosy_{hashlib.md5(cache_key).hexdigest()[:8]}.mp3",
            )

        if os.path.exists(output_path):
            logger.info(f"TTS 缓存命中: {output_path}")
            return output_path

        from dashscope.audio.tts_v2 import SpeechSynthesizer, AudioFormat

        synthesizer = SpeechSynthesizer(
            model=self.model,
            voice=self.voice,
            format=AudioFormat.MP3_22050HZ_MONO_256KBPS,
        )

        # ── 情绪控制 ──
        emo_cfg = get_emotion_config(emotion)
        instruction = emo_cfg.get("cosy_instruction", "")
        # 语速叠加: 基础 speed × emotion rate
        if speech_rate == 1.0:  # 未显式指定语速
            rate_str = emo_cfg.get("rate", "0%")
            if rate_str:
                pct = int(rate_str.replace("%", "").replace("+", ""))
                speech_rate = 1.0 + pct / 100.0

        kwargs = {"text": text}
        if instruction:
            kwargs["instruction"] = instruction

        logger.info(
            f"CosyVoice 合成: {text[:40]}... voice={self.voice} "
            f"emotion={emotion} instruction={instruction[:30]}"
        )

        # 注意: SpeechSynthesizer.call() 的签名不同版本有差异
        if instruction:
            try:
                audio = synthesizer.call(text, instruction=instruction)
            except TypeError:
                # 旧版 dashscope 不支持 instruction 参数
                audio = synthesizer.call(text)
        else:
            audio = synthesizer.call(text)

        if audio is None:
            raise RuntimeError("CosyVoice 返回空音频")

        with open(output_path, "wb") as f:
            f.write(audio)

        logger.info(f"CosyVoice 完成: {output_path} ({len(audio)} bytes)")
        return output_path

    def synthesize_segments(self, segments: list[str],
                            output_path: str = "",
                            emotion: str = "",
                            pause_ms: int | None = None,
                            segment_roles: list[str] | None = None,
                            speech_rate: float = 0.0,
                            ) -> tuple[str, list[int], list[int]]:
        """分段合成+拼接：每段独立配音→FFmpeg拼接→精确时间戳。

        Args:
            pause_ms: 段间停顿时长(ms)，None=从config读取segment_tts.pause_normal
            speech_rate: 语速倍率，0=引擎默认（CosyVoice 内部按 config 读）

        Returns:
            (拼接后的MP3路径, [每段时长ms列表(含停顿)])
        """
        import subprocess
        import shutil
        import tempfile

        if not segments:
            raise ValueError("segments 不能为空")

        # ── 读取段间停顿配置 ──
        if pause_ms is None:
            pause_ms = _get_pause_normal_ms()

        # ── 分段结果缓存（内容寻址）：同 segments/voice/emotion/pause/speech_rate/roles 命中跳过合成 ──
        cache_key = (f"{'|'.join(segments)}|{self.voice}|{emotion}|{pause_ms}|"
                     f"{speech_rate}|{'|'.join(segment_roles or [])}")
        cache_id = hashlib.md5(cache_key.encode("utf-8")).hexdigest()[:8]
        # 忽略调用方传入的 output_path，按内容寻址，避免按 script_id 隔离导致同文案重复合成
        output_path = os.path.join(self.output_dir, f"tts_seg_{cache_id}.mp3")
        meta_path = output_path + ".meta.json"
        if os.path.exists(output_path) and os.path.exists(meta_path):
            try:
                import json
                with open(meta_path, "r", encoding="utf-8") as f:
                    meta = json.load(f)
                # 内容校验：文案/音色/情绪/停顿/语速任一变化即失效，避免按路径命中旧配音
                if meta.get("cache_id") != cache_id:
                    logger.info("CosyVoice 分段缓存内容已变，重新合成")
                else:
                    seg_durations = meta.get("seg_durations", [])
                    pause_durations = meta.get("pause_durations", [])
                    if len(seg_durations) == len(segments):
                        return output_path, seg_durations, pause_durations
            except Exception as e:
                logger.warning(f"CosyVoice 分段缓存元数据损坏，重新合成: {e}")

        tmp_dir = tempfile.mkdtemp(prefix="tts_seg_")
        seg_paths = []      # 与 segments 等长，失败段为 ""
        seg_durations = []  # 与 segments 等长
        silence_path = ""

        # ── 预生成静音片段（段间停顿用）──
        if pause_ms > 0 and len(segments) > 1:
            silence_path = _generate_silence_mp3(pause_ms, tmp_dir, sample_rate=22050)

        # 逐段合成
        for i, seg in enumerate(segments):
            seg_path = os.path.join(tmp_dir, f"seg_{i:03d}.mp3")
            try:
                self.synthesize(seg, seg_path, emotion=emotion,
                                speech_rate=(speech_rate if speech_rate > 0 else 1.0))
                seg_paths.append(seg_path)
                from moviepy import AudioFileClip
                ac = AudioFileClip(seg_path)
                dur = max(int(ac.duration * 1000), 200)
                seg_durations.append(dur)
                ac.close()
            except Exception as e:
                logger.error(f"分段{i}合成失败: {e}")
                fallback = max(len(seg) * 250, 500)
                seg_durations.append(fallback)
                # 生成静音占位，确保 concat 后总时长与 seg_durations 一致（字幕不错位）
                seg_paths.append(_generate_silence_mp3(
                    fallback, tmp_dir, sample_rate=22050))

        # 只取有效段
        valid_indices = [i for i, sp in enumerate(seg_paths) if sp]
        if not valid_indices:
            raise RuntimeError("全部分段合成失败")

        # FFmpeg concat 拼接（段间插入静音停顿）
        concat_list = os.path.join(tmp_dir, "concat.txt")
        with open(concat_list, "w", encoding="utf-8") as f:
            for idx, vi in enumerate(valid_indices):
                f.write(f"file '{seg_paths[vi]}'\n")
                if silence_path and idx < len(valid_indices) - 1:
                    f.write(f"file '{silence_path}'\n")

        # ── 调整 seg_durations：仅有效段间加停顿（记录停顿供字幕对齐）──
        pause_durations = [0] * len(seg_durations)
        if silence_path and pause_ms > 0:
            valid_set = set(valid_indices)
            for i in range(len(seg_durations)):
                if i in valid_set and (i + 1) in valid_set:
                    seg_durations[i] += pause_ms
                    pause_durations[i] = pause_ms

        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
        total_seg_sec = sum(seg_durations) / 1000.0
        afade_out_start = max(0, total_seg_sec - 0.03)
        afade_filter = (f"afade=t=in:st=0:d=0.03,"
                        f"afade=t=out:st={afade_out_start:.4f}:d=0.03")
        result = subprocess.run(
            [get_ffmpeg_cmd(), "-y", "-f", "concat", "-safe", "0",
             "-i", concat_list, "-c:a", "libmp3lame", "-q:a", "2",
             "-af", afade_filter,
             output_path],
            capture_output=True, timeout=60,
        )
        if result.returncode != 0:
            # 兜底：拷贝第一个有效段
            shutil.copy2(seg_paths[valid_indices[0]], output_path)

        # 精度校验
        total_seg = sum(seg_durations)
        try:
            from moviepy import AudioFileClip
            ac = AudioFileClip(output_path)
            total_out = int(ac.duration * 1000)
            ac.close()
            drift = abs(total_out - total_seg)
            if drift > 100:
                logger.warning(
                    f"分段拼接漂移 {drift}ms (段总和{total_seg}ms vs 输出{total_out}ms)")
        except Exception:
            pass

        # 清理临时文件
        try:
            shutil.rmtree(tmp_dir, ignore_errors=True)
        except Exception:
            pass

        # 写缓存元数据（供下次命中时还原 seg_durations/pause_durations，cache_id 用于内容校验）
        try:
            import json
            with open(meta_path, "w", encoding="utf-8") as f:
                json.dump({"cache_id": cache_id,
                           "seg_durations": seg_durations,
                           "pause_durations": pause_durations},
                          f, ensure_ascii=False)
        except Exception:
            pass

        return output_path, seg_durations, pause_durations

    def synthesize_script(self, texts: list[str], prefix: str = "shot",
                          emotion: str = "") -> list[str]:
        """批量合成"""
        paths = []
        for i, text in enumerate(texts):
            if not text.strip():
                paths.append("")
                continue
            out = os.path.join(self.output_dir, f"{prefix}_{i:02d}.mp3")
            try:
                paths.append(self.synthesize(text, out, emotion=emotion))
            except Exception as e:
                logger.error(f"镜头 {i} TTS 失败: {e}")
                paths.append("")
        return paths


# ═══════════════════════════════════════
# Edge-TTS 引擎（新增 — 免费 + 30+音色 + SSML情绪）
# ═══════════════════════════════════════

class EdgeTTSEngine:
    """Microsoft Edge TTS — 免费云端引擎, SSML 情绪控制。

    通过 edge-tts 库调用, 不依赖 API Key。
    pip install edge-tts (可选, 首次调用时自动提示)
    """

    def __init__(self, voice: str = "", voice_pool: VoicePool | None = None):
        # 检查依赖
        try:
            import edge_tts  # noqa: F401
            self._available = True
        except ImportError:
            self._available = False
            logger.debug("edge-tts 未安装（非默认后端，不影响使用）")

        if voice:
            self.voice = voice
        elif voice_pool:
            self.voice = voice_pool.next()
        else:
            tts_cfg = config.tts_config or {}
            edge_cfg = tts_cfg.get("edge_tts", {})
            self.voice = edge_cfg.get("voice", "zh-CN-XiaoxiaoNeural")

        self._voice_pool = voice_pool
        self.output_dir = os.path.join(config.output_dir, "_narration")
        os.makedirs(self.output_dir, exist_ok=True)

    @property
    def current_voice_name(self) -> str:
        vp = EDGE_VOICES.get(self.voice)
        return vp.name if vp else self.voice

    def next_voice(self) -> str:
        if self._voice_pool:
            self.voice = self._voice_pool.next()
        return self.voice

    @property
    def backend_name(self) -> str:
        return "EdgeTTS"

    @property
    def available(self) -> bool:
        return self._available

    def synthesize(self, text: str, output_path: str | None = None,
                   speech_rate: float = 1.0, volume: int = 50,
                   emotion: str = "") -> str:
        """合成语音，通过 SSML 注入情绪。

        使用 <prosody> 控制语速/音调 + 可选 <mstts:express-as> 情绪风格。
        """
        text = text.strip()
        if not text:
            raise ValueError("合成文本不能为空")

        if not self._available:
            raise RuntimeError(
                "Edge-TTS 不可用: pip install edge-tts"
            )

        # 提前确定最终情绪，纳入缓存 key（避免同文本不同情绪/音色/语速错误命中缓存）
        emotion = emotion or detect_emotion(text)

        if output_path is None:
            cache_key = f"{text}|{self.voice}|{emotion}|{speech_rate:.2f}".encode("utf-8")
            output_path = os.path.join(
                self.output_dir,
                f"edge_{hashlib.md5(cache_key).hexdigest()[:8]}.mp3",
            )

        if os.path.exists(output_path):
            logger.info(f"TTS 缓存命中: {output_path}")
            return output_path

        # ── 情绪配置 ──
        emo_cfg = get_emotion_config(emotion)
        rate = emo_cfg.get("rate", "0%")
        pitch = emo_cfg.get("pitch", "0%")

        # 语速叠加
        if speech_rate != 1.0:
            pct = int((speech_rate - 1.0) * 100)
            rate = f"{'+' if pct >= 0 else ''}{pct}%"

        # 构建 Edge 参数。注意：edge-tts 只接受纯文本 + rate/pitch 参数；
        # 传 SSML 字符串会被当成正文念出来（实测一句 3.5s 被念成 26s），
        # 2026-10 skill 版修正：SSML 注入改为 Communicate 原生参数
        kwargs = {}
        if rate and rate not in ("+0%", "0%"):
            kwargs["rate"] = rate
        if pitch and pitch not in ("+0%", "0%", "+0Hz", "0Hz"):
            kwargs["pitch"] = pitch

        logger.info(
            f"EdgeTTS 合成: {text[:40]}... voice={self.voice} "
            f"emotion={emotion} rate={rate} pitch={pitch}"
        )

        # edge-tts 是异步的，用 asyncio.run 执行（get_event_loop 在 3.10+ 已废弃）
        async def _run():
            import edge_tts
            communicate = edge_tts.Communicate(text, voice=self.voice, **kwargs)
            await communicate.save(output_path)

        asyncio.run(_run())

        logger.info(f"EdgeTTS 完成: {output_path}")
        return output_path

    def synthesize_segments(self, segments: list[str],
                            output_path: str = "",
                            emotion: str = "",
                            pause_ms: int | None = None,
                            segment_roles: list[str] | None = None,
                            speech_rate: float = 0.0,
                            ) -> tuple[str, list[int], list[int]]:
        """分段合成+拼接：每段独立配音→FFmpeg拼接→精确时间戳。

        Args:
            pause_ms: 段间停顿时长(ms)，None=从config读取segment_tts.pause_normal
            speech_rate: 语速倍率，0=引擎默认（Edge 1.0 原速）

        Returns:
            (拼接后的MP3路径, [每段时长ms列表(含停顿)])
        """
        import subprocess
        import shutil
        import tempfile

        if not segments:
            raise ValueError("segments 不能为空")

        if not self._available:
            raise RuntimeError("Edge-TTS 不可用: pip install edge-tts")

        # ── 读取段间停顿配置 ──
        if pause_ms is None:
            pause_ms = _get_pause_normal_ms()

        # ── 分段结果缓存（内容寻址）：同 segments/voice/emotion/pause/speech_rate/roles 命中跳过合成 ──
        cache_key = (f"{'|'.join(segments)}|{self.voice}|{emotion}|{pause_ms}|"
                     f"{speech_rate}|{'|'.join(segment_roles or [])}")
        cache_id = hashlib.md5(cache_key.encode("utf-8")).hexdigest()[:8]
        # 忽略调用方传入的 output_path，按内容寻址，避免按 script_id 隔离导致同文案重复合成
        output_path = os.path.join(self.output_dir, f"edge_seg_{cache_id}.mp3")
        meta_path = output_path + ".meta.json"
        if os.path.exists(output_path) and os.path.exists(meta_path):
            try:
                import json
                with open(meta_path, "r", encoding="utf-8") as f:
                    meta = json.load(f)
                # 内容校验：文案/音色/情绪/停顿/语速任一变化即失效，避免按路径命中旧配音
                if meta.get("cache_id") != cache_id:
                    logger.info("EdgeTTS 分段缓存内容已变，重新合成")
                else:
                    seg_durations = meta.get("seg_durations", [])
                    pause_durations = meta.get("pause_durations", [])
                    if len(seg_durations) == len(segments):
                        return output_path, seg_durations, pause_durations
            except Exception as e:
                logger.warning(f"EdgeTTS 分段缓存元数据损坏，重新合成: {e}")

        tmp_dir = tempfile.mkdtemp(prefix="tts_seg_")
        seg_paths = []
        seg_durations = []
        silence_path = ""

        # ── 预生成静音片段（edge-tts 默认 24kHz）──
        if pause_ms > 0 and len(segments) > 1:
            silence_path = _generate_silence_mp3(pause_ms, tmp_dir, sample_rate=24000)

        # 逐段合成
        for i, seg in enumerate(segments):
            seg_path = os.path.join(tmp_dir, f"seg_{i:03d}.mp3")
            try:
                self.synthesize(seg, seg_path, emotion=emotion,
                                speech_rate=(speech_rate if speech_rate > 0 else 1.0))
                seg_paths.append(seg_path)
                from moviepy import AudioFileClip
                ac = AudioFileClip(seg_path)
                dur = max(int(ac.duration * 1000), 200)
                seg_durations.append(dur)
                ac.close()
            except Exception as e:
                logger.error(f"EdgeTTS 分段{i}合成失败: {e}")
                fallback = max(len(seg) * 250, 500)
                seg_durations.append(fallback)
                # 生成静音占位，确保 concat 后总时长与 seg_durations 一致（字幕不错位）
                seg_paths.append(_generate_silence_mp3(
                    fallback, tmp_dir, sample_rate=24000))

        valid_indices = [i for i, sp in enumerate(seg_paths) if sp]
        if not valid_indices:
            raise RuntimeError("EdgeTTS 全部分段合成失败")

        # FFmpeg concat 拼接（段间插入静音停顿）
        concat_list = os.path.join(tmp_dir, "concat.txt")
        with open(concat_list, "w", encoding="utf-8") as f:
            for idx, vi in enumerate(valid_indices):
                f.write(f"file '{seg_paths[vi]}'\n")
                if silence_path and idx < len(valid_indices) - 1:
                    f.write(f"file '{silence_path}'\n")

        # ── 调整 seg_durations：仅有效段间加停顿（记录停顿供字幕对齐）──
        pause_durations = [0] * len(seg_durations)
        if silence_path and pause_ms > 0:
            valid_set = set(valid_indices)
            for i in range(len(seg_durations)):
                if i in valid_set and (i + 1) in valid_set:
                    seg_durations[i] += pause_ms
                    pause_durations[i] = pause_ms

        from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
        total_seg_sec = sum(seg_durations) / 1000.0
        afade_out_start = max(0, total_seg_sec - 0.03)
        afade_filter = (f"afade=t=in:st=0:d=0.03,"
                        f"afade=t=out:st={afade_out_start:.4f}:d=0.03")
        result = subprocess.run(
            [get_ffmpeg_cmd(), "-y", "-f", "concat", "-safe", "0",
             "-i", concat_list, "-c:a", "libmp3lame", "-q:a", "2",
             "-af", afade_filter,
             output_path],
            capture_output=True, timeout=60,
        )
        if result.returncode != 0:
            shutil.copy2(seg_paths[valid_indices[0]], output_path)

        # 精度校验
        total_seg = sum(seg_durations)
        try:
            from moviepy import AudioFileClip
            ac = AudioFileClip(output_path)
            total_out = int(ac.duration * 1000)
            ac.close()
            drift = abs(total_out - total_seg)
            if drift > 100:
                logger.warning(
                    f"EdgeTTS 分段拼接漂移 {drift}ms (段总和{total_seg}ms vs 输出{total_out}ms)")
        except Exception:
            pass

        try:
            shutil.rmtree(tmp_dir, ignore_errors=True)
        except Exception:
            pass

        # 写缓存元数据（供下次命中时还原 seg_durations/pause_durations，cache_id 用于内容校验）
        try:
            import json
            with open(meta_path, "w", encoding="utf-8") as f:
                json.dump({"cache_id": cache_id,
                           "seg_durations": seg_durations,
                           "pause_durations": pause_durations},
                          f, ensure_ascii=False)
        except Exception:
            pass

        return output_path, seg_durations, pause_durations

    def synthesize_script(self, texts: list[str], prefix: str = "shot",
                          emotion: str = "") -> list[str]:
        """批量合成"""
        paths = []
        for i, text in enumerate(texts):
            if not text.strip():
                paths.append("")
                continue
            out = os.path.join(self.output_dir, f"{prefix}_{i:02d}.mp3")
            try:
                paths.append(self.synthesize(text, out, emotion=emotion))
            except Exception as e:
                logger.error(f"镜头 {i} EdgeTTS 失败: {e}")
                paths.append("")
        return paths


# ═══════════════════════════════════════
# 工厂函数
# ═══════════════════════════════════════

def create_tts_engine(
    backend: str = "",
    voice: str = "",
    voice_pool: VoicePool | None = None,
):
    """工厂函数：按优先级选择 TTS 后端。

    优先级: volcano(免费) > minimax(付费) > qwen3-tts(本地)
    """
    if not backend:
        tts_cfg = config.tts_config or {}
        backend = tts_cfg.get("backend", "volcano")

    # ── 先尝试用户显式指定的后端 ──
    if backend == "edge":
        try:
            return EdgeTTSEngine(voice=voice, voice_pool=voice_pool)
        except Exception as e:
            logger.warning("Edge-TTS 不可用: %s，降级", e)

    if backend == "cosyvoice":
        try:
            return CosyVoiceEngine(voice=voice, voice_pool=voice_pool)
        except Exception as e:
            logger.warning("CosyVoice 不可用: %s，降级", e)

    # ── 1. 火山引擎 TTS（免费额度，优先）──
    if backend == "volcano":
        try:
            from adflow.engine.volcano_tts import VolcanoTTSEngine
            return VolcanoTTSEngine(voice=voice, voice_pool=voice_pool)
        except Exception as e:
            logger.warning("火山TTS 不可用: %s，降级 MiniMax", e)

    # ── 2. MiniMax TTS（超自然，需付费）──
    if backend in ("volcano", "minimax"):
        try:
            from adflow.engine.minimax_tts import MiniMaxTTSEngine
            engine = MiniMaxTTSEngine(voice=voice, voice_pool=voice_pool)
            test_out = engine.synthesize("测试")
            if os.path.exists(test_out) and os.path.getsize(test_out) > 100:
                return engine
        except Exception as e:
            logger.warning("MiniMax TTS 不可用: %s，降级 Qwen3-TTS", e)

    # ── 3. Qwen3-TTS 本地兜底（已安装） ──
    logger.warning("云端TTS全部不可用，启用本地 Qwen3-TTS 兜底...")
    try:
        from adflow.engine.qwen3_tts import Qwen3TTSEngine
        return Qwen3TTSEngine(voice=voice, voice_pool=voice_pool)
    except ImportError:
        pass

    raise RuntimeError(
        "所有TTS后端不可用。请检查网络连接或充值 MiniMax。")


# ── 向后兼容别名 ──
TTSEngine = CosyVoiceEngine
# 旧代码引用的 VOICES dict {voice_id: "龙小夏（女声，活泼）"}
VOICES = {
    vid: f"{vp.name}（{'女' if vp.gender == 'female' else '男'}声，{vp.style}）"
    for vid, vp in COSY_VOICES.items()
}
