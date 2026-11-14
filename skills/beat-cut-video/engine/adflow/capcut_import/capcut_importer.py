"""
剪映草稿 → AdFlow 风格参数导入
读取剪映 draft_content.json，提取审美偏好
"""

import os, json, statistics
from pathlib import Path
from adflow.models import StyleProfile


def import_style_from_capcut(draft_dir: str | None = None) -> StyleProfile | None:
    """
    从剪映草稿目录提取风格参数
    若 draft_dir 为 None，自动搜索系统剪映草稿目录
    返回 StyleProfile 或 None
    """
    if draft_dir is None:
        draft_dir = _find_draft_interactive()
        if draft_dir is None:
            return None

    content_file = os.path.join(draft_dir, "draft_content.json")
    info_file = os.path.join(draft_dir, "draft_info.json")

    if not os.path.exists(content_file):
        raise FileNotFoundError(f"未找到 draft_content.json: {draft_dir}")

    with open(content_file, "r", encoding="utf-8") as f:
        content = json.load(f)

    # 获取草稿名称
    draft_name = Path(draft_dir).name
    if os.path.exists(info_file):
        with open(info_file, "r", encoding="utf-8") as f:
            info = json.load(f)
            draft_name = info.get("name", draft_name)

    style = StyleProfile(name=f"剪映: {draft_name}", source="capcut_import")

    materials = content.get("materials", {})
    tracks = content.get("tracks", [])

    # --- 提取字幕风格 ---
    fonts = materials.get("fonts", [])
    text_segments = _get_text_segments(tracks)
    if text_segments and fonts:
        ts = text_segments[0].get("extra_info", {}).get("text", {})
        style.subtitle_size = ts.get("font_size", 0)
        style.subtitle_color = ts.get("color", "")
        if ts.get("stroke_color"):
            style.subtitle_stroke_color = ts.get("stroke_color")
            style.subtitle_stroke_width = ts.get("stroke_width", 0)
        # 字体信息
        font_id = ts.get("font_id", "")
        for font in fonts:
            if font.get("id") == font_id:
                style.subtitle_font = font.get("path", "")
                break

    # --- 提取节奏 ---
    all_durations = []
    for track in tracks:
        if track.get("type") == "video":
            for seg in track.get("segments", []):
                dur = seg.get("target_timerange", {}).get("duration", 0)
                if dur > 0:
                    all_durations.append(dur / 1_000_000)  # us → seconds

    if all_durations:
        avg_dur = statistics.mean(all_durations)
        if avg_dur < 2.0:
            style.pace = "fast"
        elif avg_dur > 5.0:
            style.pace = "slow"
        else:
            style.pace = "medium"

    # --- 提取转场 ---
    transitions = set()
    for track in tracks:
        for seg in track.get("segments", []):
            trans = seg.get("extra_info", {}).get("transition", {})
            if trans.get("to_next"):
                transitions.add(trans["to_next"].get("type_name", ""))
    if "wipe" in transitions or "slide" in transitions:
        style.transition = "slide"
    elif "dissolve" in transitions:
        style.transition = "dissolve"
    elif "zoom" in transitions:
        style.transition = "zoom"
    elif transitions:
        style.transition = "cut"

    # --- 提取调色 ---
    color_adjusts = []
    for track in tracks:
        if track.get("type") == "video":
            for seg in track.get("segments", []):
                ca = seg.get("extra_info", {}).get("color_adjust", {})
                if ca:
                    color_adjusts.append(ca)
    if color_adjusts:
        # 取平均值
        avg_ca = {}
        for key in ["brightness", "contrast", "saturation", "temperature"]:
            vals = [c.get(key, 0) for c in color_adjusts if key in c]
            if vals:
                avg_ca[key] = statistics.mean(vals)
        style.brightness = avg_ca.get("brightness", 0.0)
        style.contrast = avg_ca.get("contrast", 0.0)
        style.saturation = avg_ca.get("saturation", 0.0)
        style.temperature = avg_ca.get("temperature", 0.0)

    # --- 提取动画 ---
    animations = set()
    for track in tracks:
        for seg in track.get("segments", []):
            anim = seg.get("extra_info", {}).get("animation", {})
            for key in ("in", "out"):
                if anim.get(key):
                    animations.add(anim[key].get("type_name", ""))
    if "fade" in animations:
        style.animation_in = "fade"
    elif "slide" in animations:
        style.animation_in = "slide"
    elif "zoom" in animations:
        style.animation_in = "zoom"

    return style


def _get_text_segments(tracks: list) -> list:
    """提取所有文字轨道片段"""
    result = []
    for track in tracks:
        if track.get("type") == "text":
            result.extend(track.get("segments", []))
    return result


def _find_draft_interactive() -> str | None:
    """
    尝试找到剪映草稿目录。优先查找系统默认位置。
    返回用户选中的草稿路径或 None
    """
    candidates = []

    # 剪映专业版
    local_appdata = os.environ.get("LOCALAPPDATA", "")
    jy_path = os.path.join(local_appdata, "JianyingPro", "Data")
    if os.path.exists(jy_path):
        # 查找版本号目录
        for version_dir in os.listdir(jy_path):
            drafts = os.path.join(jy_path, version_dir, "Drafts")
            if os.path.isdir(drafts):
                for d in os.listdir(drafts):
                    full = os.path.join(drafts, d)
                    if os.path.isdir(full):
                        content_file = os.path.join(full, "draft_content.json")
                        if os.path.exists(content_file):
                            candidates.append(full)

    # CapCut 国际版
    capcut_path = os.path.join(local_appdata, "CapCut", "Data")
    if os.path.exists(capcut_path):
        for version_dir in os.listdir(capcut_path):
            drafts = os.path.join(capcut_path, version_dir, "Drafts")
            if os.path.isdir(drafts):
                for d in os.listdir(drafts):
                    full = os.path.join(drafts, d)
                    if os.path.isdir(full):
                        content_file = os.path.join(full, "draft_content.json")
                        if os.path.exists(content_file):
                            candidates.append(full)

    # 简化的"打开目录"选择
    if not candidates:
        # 回退：让用户在 AdFlow output 中找已导出的草稿
        from adflow.config_loader import config
        jy_out = os.path.join(config.output_dir, "_jianying_drafts")
        if os.path.exists(jy_out):
            for d in os.listdir(jy_out):
                full = os.path.join(jy_out, d)
                if os.path.isdir(full) and os.path.exists(os.path.join(full, "draft_content.json")):
                    candidates.append(full)

    # 返回最近修改的草稿
    candidates.sort(key=lambda p: os.path.getmtime(
        os.path.join(p, "draft_content.json")), reverse=True)

    if candidates:
        return candidates[0]

    return None


def list_capcut_drafts() -> list[dict]:
    """列出系统中所有剪映草稿"""
    drafts = []

    for base in ["JianyingPro", "CapCut"]:
        data_dir = os.path.join(os.environ.get("LOCALAPPDATA", ""), base, "Data")
        if not os.path.exists(data_dir):
            continue
        for version_dir in os.listdir(data_dir):
            draft_dir = os.path.join(data_dir, version_dir, "Drafts")
            if not os.path.isdir(draft_dir):
                continue
            for d in os.listdir(draft_dir):
                full = os.path.join(draft_dir, d)
                content_file = os.path.join(full, "draft_content.json")
                if os.path.exists(content_file):
                    info_file = os.path.join(full, "draft_info.json")
                    name = d
                    if os.path.exists(info_file):
                        try:
                            with open(info_file, "r", encoding="utf-8") as f:
                                info = json.load(f)
                                name = info.get("name", d)
                        except Exception:
                            pass
                    mtime = os.path.getmtime(content_file)
                    drafts.append({
                        "path": full, "name": name,
                        "modified": mtime,
                    })

    drafts.sort(key=lambda x: x["modified"], reverse=True)
    return drafts
