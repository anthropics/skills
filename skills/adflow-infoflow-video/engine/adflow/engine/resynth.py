"""改字幕后重新合成配音 — 供时间轴编辑「改字幕」场景复用

从 StoryboardScript 收集分段口播文本（含标点二次断句），重新走 TTS，
返回重渲染所需的新配音文件 + 分段时长 + 停顿。
"""

import json
import os

from adflow.engine.tts_engine import create_tts_engine, detect_emotion
from adflow.engine.subtitle_renderer import break_by_punctuation
from adflow.config_loader import config


def collect_shot_segments(shot) -> list[str]:
    """收集单个 shot 的口播段（含标点二次断句）"""
    shot_segs = []
    segs_raw = shot.narration_segments or ""
    if segs_raw:
        try:
            segs = json.loads(segs_raw)
            if isinstance(segs, list):
                shot_segs = [s.strip() for s in segs if s.strip()]
        except (json.JSONDecodeError, TypeError):
            pass
    if not shot_segs:
        text = (shot.narration_text or "").strip()
        if text:
            shot_segs = break_by_punctuation(text)
    refined = []
    for seg in shot_segs:
        refined.extend(break_by_punctuation(seg) or [seg])
    return refined


def collect_narration_segments(script) -> tuple[list[str], list[str]]:
    """收集脚本分段口播文本 + 每段角色（含标点二次断句）"""
    all_segments = []
    segment_roles = []
    for shot in script.shots:
        refined = collect_shot_segments(shot)
        all_segments.extend(refined)
        segment_roles.extend([shot.role] * len(refined))
    return all_segments, segment_roles


def collect_segment_shot_indices(script) -> list[int]:
    """返回「每段口播所属 shot 在 script.shots 中的索引」列表

    段顺序与 collect_narration_segments 完全一致，供镜头切分做 role 加权映射。
    """
    shot_indices = []
    for i, shot in enumerate(script.shots):
        refined = collect_shot_segments(shot)
        shot_indices.extend([i] * len(refined))
    return shot_indices


def resynthesize_narration(script) -> tuple[str, list[str], list[int], list[int]]:
    """重新合成整段配音，返回 (mp3路径, 分段文本, 段时长, 段停顿)"""
    all_segments, segment_roles = collect_narration_segments(script)
    if not all_segments:
        return "", [], [], []
    tts = create_tts_engine()
    emotion = detect_emotion("".join(all_segments))
    out_path = os.path.join(
        config.output_dir, "_narration", f"{script.script_id}.mp3")
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    mp3_path, seg_durs, pause_durs = tts.synthesize_segments(
        all_segments, out_path, emotion=emotion,
        pause_ms=None, segment_roles=segment_roles)
    return mp3_path, all_segments, seg_durs, pause_durs
