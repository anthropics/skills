# -*- coding: utf-8 -*-
"""
数字人画中画 — 形象注册 + 对口型视频生成桥接

- Avatar: 一个数字人形象（人像图 + 性别）
- list_digital_humans: 扫描 avatars 目录，按文件名约定注册
- generate_talking_video: subprocess 调 MuseTalk 桥接脚本，幂等 + 超时 + 失败降级

对外契约（供 pipeline 调用）：
- list_digital_humans() -> list[Avatar]
- get_digital_human(avatar_id) -> Avatar | None
- avatars_for_gender(gender) -> list[Avatar]
- generate_talking_video(image, audio, out) -> str（失败返回空串）
"""
from __future__ import annotations

import os
import sys
import logging
import subprocess
from dataclasses import dataclass

from adflow.config_loader import config

logger = logging.getLogger("adflow.digital_human")


@dataclass
class Avatar:
    """一个数字人形象"""
    avatar_id: str
    image_path: str
    gender: str          # "female" | "male"
    display_name: str = ""


def _project_root() -> str:
    # digital_human.py 位于 adflow/engine/，项目根在上三级
    return os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _cfg() -> dict:
    return config.get("digital_human", {}) or {}


def is_enabled() -> bool:
    """数字人功能总开关（config.digital_human.enabled）。未装 MuseTalk 环境保持 False。"""
    return bool(_cfg().get("enabled", False))


def _avatars_dir() -> str:
    d = _cfg().get("avatars_dir", "digital_human/avatars")
    if not os.path.isabs(d):
        d = os.path.join(_project_root(), d)
    return d


def _parse_gender(filename: str) -> str:
    """从文件名提取性别（约定 dh_female_01.png / dh_male_01.png / 女_01.png 等）。"""
    if "female" in filename.lower() or "女" in filename:
        return "female"
    if "male" in filename.lower() or "男" in filename:
        return "male"
    return ""


def list_digital_humans() -> list[Avatar]:
    """扫描 avatars 目录，返回可用数字人形象（按 avatar_id 排序）。"""
    if not is_enabled():
        return []
    avatars: list[Avatar] = []
    d = _avatars_dir()
    if not os.path.isdir(d):
        return avatars
    for name in sorted(os.listdir(d)):
        path = os.path.join(d, name)
        if not os.path.isfile(path):
            continue
        ext = os.path.splitext(name)[1].lower()
        if ext not in (".png", ".jpg", ".jpeg", ".webp", ".mp4"):
            continue
        gender = _parse_gender(name)
        if not gender:
            continue  # 无法判性别的不注册（避免女脸配男声）
        avatars.append(Avatar(
            avatar_id=os.path.splitext(name)[0],
            image_path=path,
            gender=gender,
            display_name=name,
        ))
    return avatars


def get_digital_human(avatar_id: str) -> Avatar | None:
    for a in list_digital_humans():
        if a.avatar_id == avatar_id:
            return a
    return None


def avatars_for_gender(gender: str) -> list[Avatar]:
    """返回指定性别的全部可用形象（按 avatar_id 排序，顺序稳定）；gender 未知/空返回空列表。

    供 pipeline 自动匹配轮换用：同性别多形象时逐脚本轮着用，不总用第一个。
    """
    if gender not in ("female", "male"):
        return []
    return [a for a in list_digital_humans() if a.gender == gender]


def generate_talking_video(image: str, audio: str, out: str) -> str:
    """调用 MuseTalk 桥接脚本生成对口型视频。

    幂等：out 已存在且非空 → 直接返回 out，跳过推理。
    失败（环境未装 / 超时 / 非零退出）→ 返回空串，由调用方降级为「无数字人」。
    """
    if not image or not audio or not out:
        return ""
    if not is_enabled():
        return ""
    if os.path.exists(out) and os.path.getsize(out) > 0:
        logger.info("[数字人] cache hit: %s", os.path.basename(out))
        return out

    cfg = _cfg()
    # 未配 python 则用当前解释器（大概率 import 不到 MuseTalk → 降级，不抛异常）
    py = cfg.get("python", "") or sys.executable
    bridge = cfg.get("bridge", "digital_human/musetalk_bridge.py")
    if not os.path.isabs(bridge):
        bridge = os.path.join(_project_root(), bridge)
    timeout = int(cfg.get("timeout_sec", 600) or 600)

    if not os.path.exists(bridge):
        logger.warning("[数字人] 桥接脚本不存在: %s", bridge)
        return ""

    os.makedirs(os.path.dirname(out), exist_ok=True)
    cmd = [py, bridge, "--image", image, "--audio", audio, "--output", out]
    try:
        logger.info("[数字人] 生成中: %s", os.path.basename(out))
        r = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=timeout)
        if r.returncode != 0 or not (os.path.exists(out) and os.path.getsize(out) > 0):
            logger.warning("[数字人] 生成失败 rc=%s stderr=%s",
                           r.returncode, (r.stderr or "")[-200:])
            return ""
        return out
    except subprocess.TimeoutExpired:
        logger.warning("[数字人] 生成超时(%ss): %s", timeout, os.path.basename(out))
        return ""
    except Exception as e:
        logger.warning("[数字人] 生成异常: %s", e)
        return ""
