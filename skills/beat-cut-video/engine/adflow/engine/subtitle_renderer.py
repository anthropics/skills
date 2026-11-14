"""
字幕渲染引擎
- 文本 → SRT 格式字幕
- moviepy TextClip 渲染 → CompositeVideoClip
- 安全区自动避让
"""

from dataclasses import dataclass
import logging
from typing import Optional

from moviepy import TextClip, CompositeVideoClip


@dataclass
class SubtitleBlock:
    """一条字幕"""
    text: str
    start_ms: int
    end_ms: int
    style: str = "default"  # default / highlight / cta


@dataclass
class SubtitleStyle:
    """字幕样式配置"""
    font: str = "C:/Windows/Fonts/msyhbd.ttc"  # 与 config.yaml 的 editing.subtitle.font 保持一致（粗体）
    font_size: int = 48
    color: str = "white"
    stroke_color: str = "black"
    stroke_width: int = 2
    position_y: str = "bottom"          # bottom / center / top
    safe_margin_bottom: int = 120
    safe_margin_sides: int = 80
    fixed_y: int = 0                     # >0 时锁定 Y 像素位置（从顶部算），忽略 position_y
    # 高亮样式
    highlight_color: str = "#FFD700"    # 金色
    # CTA 样式（只变色不变字号，字号与普通字幕统一走 font_size）
    cta_color: str = "#FF4444"          # 红色
    # 前3秒（hook）字幕放大
    hook_window_ms: int = 3000      # hook 段上界（脚本 hook 角色 0-3秒）
    hook_font_size_boost: int = 8   # 前3秒字号加量（像素）


def _text_to_clip(
    text: str, duration_sec: float, video_width: int, video_height: int,
    style: SubtitleStyle, text_style: str, hook_boost: bool = False,
) -> TextClip:
    """将单条字幕文本转为 TextClip"""
    color = style.color
    font_size = style.font_size

    if text_style == "highlight":
        color = style.highlight_color
        font_size = style.font_size + 4
    elif text_style == "cta":
        color = style.cta_color

    if hook_boost:
        font_size += style.hook_font_size_boost

    txt_clip = TextClip(
        text=text,
        font=style.font,
        font_size=font_size,
        color=color,
        stroke_color=style.stroke_color,
        stroke_width=style.stroke_width,
        method="caption",
        size=(video_width - style.safe_margin_sides * 2, None),
    ).with_duration(duration_sec)

    # 位置计算（统一保证文字底边不越过底部安全区：
    # 多行/大字号时底部对齐曾把文字顶边钉在安全线上，往下长出的部分被裁出画面）
    if style.fixed_y > 0:
        y = min(style.fixed_y,
                video_height - style.safe_margin_bottom - int(txt_clip.h))
        txt_clip = txt_clip.with_position(("center", max(y, 0)))
    elif style.position_y == "bottom":
        y = video_height - style.safe_margin_bottom - int(txt_clip.h)
        txt_clip = txt_clip.with_position(("center", max(y, 0)))
    elif style.position_y == "center":
        txt_clip = txt_clip.with_position("center")
    elif style.position_y == "top":
        txt_clip = txt_clip.with_position(("center", style.safe_margin_bottom))

    return txt_clip


def _clean_subtitle_text(text: str) -> str:
    """清理字幕文本：去掉尾部非疑问/感叹的标点符号"""
    # 去掉尾部除了 ？和！之外的所有标点
    import re
    # 保留: ？ ！ ... （末尾省略号）
    return re.sub(r'[，。、；：,\.;:\-]+$', '', text.strip())


def build_subtitle_track(
    subtitles: list[SubtitleBlock],
    video_width: int,
    video_height: int,
    video_duration_sec: float,
    style: Optional[SubtitleStyle] = None,
) -> list[TextClip]:
    """
    将字幕列表转为 moviepy TextClip 列表
    返回的列表可直接用于 CompositeVideoClip
    """
    if style is None:
        style = SubtitleStyle()

    clips = []
    for sub in subtitles:
        dur = (sub.end_ms - sub.start_ms) / 1000.0
        if dur <= 0:
            continue

        clean_text = _clean_subtitle_text(sub.text)
        # 前3秒（hook 段）字幕放大，静音观看时抓眼球
        is_hook = sub.start_ms < style.hook_window_ms
        clip = _text_to_clip(clean_text, dur, video_width, video_height,
                             style, sub.style, hook_boost=is_hook)
        clip = clip.with_start(sub.start_ms / 1000.0)
        clips.append(clip)

    return clips


def subtitles_to_srt(subtitles: list[SubtitleBlock]) -> str:
    """字幕列表 → SRT 格式字符串"""
    lines = []
    for i, sub in enumerate(subtitles, 1):
        start = _ms_to_srt_time(sub.start_ms)
        end = _ms_to_srt_time(sub.end_ms)
        lines.append(f"{i}\n{start} --> {end}\n{sub.text}\n")
    return "\n".join(lines)


def _ms_to_srt_time(ms: int) -> str:
    """毫秒 → SRT 时间格式 HH:MM:SS,mmm"""
    h = ms // 3600000
    m = (ms % 3600000) // 60000
    s = (ms % 60000) // 1000
    ms_rem = ms % 1000
    return f"{h:02d}:{m:02d}:{s:02d},{ms_rem:03d}"


def break_by_punctuation(text: str) -> list[str]:
    """按标点/空格断句，去标点，标点断出的碎片自动合并。

    "但其实有一种天然高纤低糖的水果--无花果，可以帮你轻松控糖"
    → ["但其实有一种天然高纤低糖的水果--无花果", "可以帮你轻松控糖"]

    空格、制表符、全角空格也作为断句符（用户贴文案常以空格分隔句子），
    空格断出的段视为完整语句，不参与碎片合并。
    """
    if not text.strip():
        return []

    PUNCT = "，。！？；：、,!.?;:"
    SPACE = " \t\n　"
    MIN_CHARS = 4  # <4 字的碎片合并（"低GI""高钾"、词间空格误断的"食的人"等）
    # 语气词：读起来有自然停顿，即使短也不合并
    INTERJECTIONS = {
        "妈呀", "天哪", "天呐", "天啊", "哎呀", "哎哟", "我的天", "我的妈",
        "老天", "老天爷", "天啦", "乖乖", "哇塞", "我去", "哦", "咦",
    }
    segments = []
    start = 0
    for i, ch in enumerate(text):
        if ch in PUNCT or ch in SPACE:
            seg = text[start:i].strip()
            if seg:
                segments.append(seg)
            start = i + 1
    last = text[start:].strip()
    if last:
        segments.append(last)
    if not segments:
        return [text.strip()]

    # 兜底：无标点长句 → 本地 LLM 语义断句（仅模型可用时），否则按 10 字硬断
    if len(segments) == 1 and len(segments[0]) > 12:
        seg = segments[0]
        try:
            from adflow.engine.segmenter import get_segmenter
            if get_segmenter().available:
                smart = get_segmenter().segment(seg)
                if len(smart) > 1:
                    return smart
        except Exception:
            pass
        segments = [seg[i:i + 10] for i in range(0, len(seg), 10)]

    # 合并太短的碎片（<MIN_CHARS 字、非语气词），合并到前一段
    merged = []
    for seg in segments:
        if merged and len(seg) < MIN_CHARS and seg not in INTERJECTIONS:
            merged[-1] = merged[-1] + seg  # 短碎片合并到前一段
        else:
            merged.append(seg)
    return merged


def detect_speech_segments(audio_path: str,
                           silence_threshold: int = -35,
                           min_silence: float = 0.25) -> list[tuple[int, int]]:
    """用 ffmpeg silencedetect 检测配音的有声段（句子），返回 [(start_ms, end_ms)]

    静音段（句子间停顿）把音频切成一个个有声段，每个有声段就是一句话。
    用于「配音裂变」时对齐字幕时间戳（替代字数比例估算）。
    """
    import subprocess
    from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd

    cmd = [get_ffmpeg_cmd(), "-i", audio_path, "-af",
           f"silencedetect=noise={silence_threshold}dB:d={min_silence}",
           "-f", "null", "-"]
    result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60)

    # 解析静音段 (start_sec, end_sec)
    silences = []
    pending = None
    for line in result.stderr.splitlines():
        if "silence_start" in line:
            pending = float(line.split("silence_start:")[1].strip())
        elif "silence_end" in line and pending is not None:
            end = float(line.split("silence_end:")[1].strip().split()[0])
            silences.append((pending, end))
            pending = None
    if not silences:
        return []

    # 音频总时长
    try:
        from moviepy import AudioFileClip
        ac = AudioFileClip(audio_path)
        total_sec = ac.duration
        ac.close()
    except Exception:
        total_sec = silences[-1][1] + 1.0

    # 静音段 → 有声段
    speech = []
    prev_end = 0.0
    for s_start, s_end in silences:
        if s_start > prev_end + 0.05:
            speech.append((int(prev_end * 1000), int(s_start * 1000)))
        prev_end = s_end
    if total_sec > prev_end + 0.05:
        speech.append((int(prev_end * 1000), int(total_sec * 1000)))
    return speech


def refine_speech_segments(
        speech: list[tuple[int, int]],
        min_gap_ms: int = 150, min_len_ms: int = 250) -> list[tuple[int, int]]:
    """精调语音段：合并间隙过小的相邻段（一句话被切两半的情况）、丢过短噪声段。"""
    if not speech:
        return []
    merged = [tuple(speech[0])]
    for s, e in speech[1:]:
        ps, pe = merged[-1]
        if s - pe < min_gap_ms:      # 间隙太小 → 同一句话，并回上一段
            merged[-1] = (ps, max(pe, e))
        else:
            merged.append((s, e))
    return [seg for seg in merged if seg[1] - seg[0] >= min_len_ms] or merged


def split_text_to_n(text: str, n: int,
                    weights: list[int] | None = None) -> list[str]:
    """把文案断成恰好 n 句，句子拼接恒等于原文（不错字、不丢字）。

    用已配置的 LLM 按语音停顿数断句（语义优先）；LLM 不可用或句数
    对不上时退回字数比例切分（切口吸附到附近标点）。
    weights: 每句的参考时长(ms)，比例切分时用作权重，None=等分。
    """
    text = text.strip()
    if n <= 0 or not text:
        return []
    if n == 1:
        return [text]

    # ── 1. LLM 语义断句：恰好 n 句 ──
    try:
        segs = _llm_split_to_n(text, n)
        if segs and len(segs) == n and "".join(segs) == text:
            return segs
    except Exception as e:
        logging.getLogger("adflow.subtitle").debug("LLM 断句失败: %s", e)

    # ── 2. 兜底：字数比例切分（纯切割，天然不丢字）──
    total_w = float(sum(weights)) if weights else 0.0
    total_chars = len(text)
    cuts = []
    acc_w = 0.0
    ws = weights or [1] * n
    for i in range(n - 1):
        acc_w += ws[i]
        pos = int(acc_w / total_w * total_chars) if total_w > 0 \
            else total_chars * (i + 1) // n
        pos = max(1, min(pos, total_chars - (n - 1 - i)))
        # 切口吸附到 6 字内最近的标点/空格，避免切在词中间
        best = pos
        for off in range(0, 7):
            for p in (pos - off, pos + off):
                if 0 < p < total_chars and text[p - 1] in "，。！？；、,!?; ":
                    best = p
                    break
            if best != pos:
                break
        cuts.append(best)
    parts, prev = [], 0
    for c in cuts:
        parts.append(text[prev:c])
        prev = c
    parts.append(text[prev:])
    return parts


def _llm_split_to_n(text: str, n: int) -> list[str]:
    """调设置页配置的 LLM，把文案断成恰好 n 句（输出校验由调用方做）"""
    from adflow.api.llm_adapter import get_llm_config
    api_key, base_url, model = get_llm_config()
    if not api_key:
        return []
    from openai import OpenAI
    client = OpenAI(base_url=base_url, api_key=api_key, timeout=30)
    prompt = (
        f"把下面的文案重新断句成【恰好 {n} 句】。这是给一段有 {n} 个语音停顿的"
        f"配音配字幕，一句对一条字幕。\n"
        "规则：\n"
        "1. 只能重新断句，不能增删改任何一个字（拼接结果必须和原文完全一致）\n"
        "2. 一句话表达完才断，语义完整优先\n"
        "3. 输出 JSON 数组，如 [\"第一句\", \"第二句\"]\n\n"
        f"文案：{text}"
    )
    resp = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": prompt}],
        temperature=0.1, max_tokens=2048, timeout=30,
    )
    import json as _json
    raw = (resp.choices[0].message.content or "").strip()
    if raw.startswith("```"):
        lines = raw.splitlines()
        lines = lines[1:] if lines[0].startswith("```") else lines
        if lines and lines[-1].startswith("```"):
            lines = lines[:-1]
        raw = "\n".join(lines)
    arr = _json.loads(raw)
    if isinstance(arr, list):
        return [s.strip() for s in arr if isinstance(s, str) and s.strip()]
    return []
