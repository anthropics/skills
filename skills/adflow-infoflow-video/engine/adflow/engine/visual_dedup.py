# -*- coding: utf-8 -*-
"""
pHash 视觉去重 — 本地感知哈希识别「画面相似」的重复镜头

不依赖 LLM 打标、零 API 成本：
  1. 抽视频中间帧（ffmpeg，时长用 MaterialRecord.duration_ms，不重复 probe）
  2. 算 dHash（9×8 灰度差异哈希，64bit）
  3. Hamming 距离 ≤ 阈值 视为重复，每组保留一条

phash 持久化到 materials.phash（16 位 hex，空串=未算），算一次永久复用。
"""
from __future__ import annotations

import os
import subprocess
import tempfile

from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd


def compute_dhash(img) -> int:
    """9×8 灰度差异哈希（dHash）→ 64bit 整数。img 为 numpy 数组（灰度或 BGR）。"""
    import cv2
    if img is None:
        return 0
    if img.ndim == 3:
        img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    # 缩放到 9×8（宽 9 高 8），比较相邻列 → 8×8 = 64 bit
    small = cv2.resize(img, (9, 8), interpolation=cv2.INTER_AREA)
    diff = small[:, 1:] > small[:, :-1]
    h = 0
    for b in diff.flatten():
        h = (h << 1) | (1 if b else 0)
    return h


def extract_mid_frame(file_path: str, duration_ms: int):
    """抽视频中间帧，返回 numpy BGR 数组；失败返回 None。"""
    import cv2
    import numpy as np
    if not file_path or not os.path.exists(file_path):
        return None
    # 中间时间点（秒），至少 0.5s 避免 -ss 0 或负值
    t = max(duration_ms, 1000) / 2000.0
    fd, out_path = tempfile.mkstemp(suffix=".jpg")
    os.close(fd)
    try:
        cmd = [
            get_ffmpeg_cmd(), "-y", "-v", "quiet",
            "-ss", f"{t:.3f}", "-i", file_path,
            "-vframes", "1", "-q:v", "2", out_path,
        ]
        subprocess.run(cmd, capture_output=True, timeout=30)
        if os.path.getsize(out_path) == 0:
            return None
        # 用 np.fromfile + imdecode 解码，绕过 OpenCV imread 对中文/非 ASCII 路径的坑
        data = np.fromfile(out_path, dtype=np.uint8)
        if data.size == 0:
            return None
        return cv2.imdecode(data, cv2.IMREAD_COLOR)
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return None
    finally:
        try:
            os.remove(out_path)
        except OSError:
            pass


def compute_phash_str(material) -> str:
    """素材 → 16 位 hex dHash；抽帧/解码失败返回空串（不参与去重）。"""
    img = extract_mid_frame(material.file_path, material.duration_ms)
    if img is None:
        return ""
    return f"{compute_dhash(img):016x}"


def ensure_phash(repo, materials: list, progress_cb=None) -> int:
    """对 phash 为空的素材批量补算并写回 materials.phash，返回新增数量。

    progress_cb(done, total) 每算完一条回调一次。
    """
    todo = [m for m in materials if not m.phash]
    if not todo:
        return 0
    done = 0
    total = len(todo)
    rows: list[tuple[str, str]] = []
    for i, m in enumerate(todo):
        ph = compute_phash_str(m)
        if ph:
            m.phash = ph  # 同步内存，供后续 dedup 使用
            rows.append((ph, m.material_id))
            done += 1
        if progress_cb:
            progress_cb(i + 1, total)
    repo.set_phash_batch(rows)
    return done


def dedup_by_phash(materials: list, threshold: int = 10) -> set[str]:
    """按 dHash Hamming 距离贪心去重，返回被剔除的 material_id 集合。

    贪心法：优质素材（performance_score 高者，平局取 duration_ms 长）优先保留，
    其余素材与「已保留集合」比 Hamming 距离，≤ threshold 即剔除。
    """
    import numpy as np
    hashed: list[tuple] = []
    for m in materials:
        if not m.phash:
            continue
        try:
            hashed.append((m, int(m.phash, 16)))
        except ValueError:
            continue
    if len(hashed) < 2:
        return set()

    hashed.sort(
        key=lambda x: (x[0].performance_score or 0.0, x[0].duration_ms or 0),
        reverse=True,
    )

    kept: list[np.uint64] = []
    removed: set[str] = set()
    for m, h in hashed:
        if kept:
            arr = np.array(kept, dtype=np.uint64)
            xor = arr ^ np.uint64(h)
            # 逐元素 popcount：uint64 → 8×uint8 → 8bit 展开 → 求和
            dist = np.unpackbits(xor.view(np.uint8), axis=-1).sum(axis=-1).sum(axis=-1)
            if int(dist.min()) <= threshold:
                removed.add(m.material_id)
                continue
        kept.append(np.uint64(h))
    return removed
