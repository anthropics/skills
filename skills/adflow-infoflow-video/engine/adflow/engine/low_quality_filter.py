# -*- coding: utf-8 -*-
"""
低质镜头过滤 — 按规则从素材库筛选可用的高质量镜头

规则（由 LowQualityRules 开关控制）：
  1. 时长过短：duration_ms < min_duration_ms（默认 2500ms）
  2. 镜头重复：md5_hash 完全一致，或 scene+shot_type+camera_movement 近似一致，
     每组只保留 performance_score 最高的一条

纯软过滤：只返回「保留 id 集合」和统计，不删库、不改 DB。
"""
from __future__ import annotations

from dataclasses import dataclass

from adflow.models import MaterialRecord
from adflow.db.material_repo import MaterialRepo


@dataclass
class LowQualityRules:
    """低质判定规则（阈值 + 开关）"""
    min_duration_ms: int = 2500   # 低于此时长视为低质
    filter_short: bool = True     # 启用短镜头过滤
    dedup_md5: bool = True        # md5 完全重复 → 去重保留最高分
    dedup_similar: bool = True    # 场景+景别+运镜近似重复 → 去重保留最高分
    dedup_visual: bool = True     # pHash 画面相似 → 去重保留最高分
    visual_sim_threshold: int = 10  # dHash Hamming 距离阈值（≤此值视为重复）


def _md5_key(m: MaterialRecord):
    """md5 去重分组键；空 md5 不参与（None=跳过）。"""
    return m.md5_hash or None


def _similarity_key(m: MaterialRecord):
    """近似重复分组键；未打场景标签（scene 空）不参与。"""
    if not m.scene:
        return None
    return (m.scene, m.shot_type, m.camera_movement)


def _dedup_by_key(materials: list[MaterialRecord], key) -> set[str]:
    """按 key 分组，每组保留 performance_score 最高一条，返回被剔除的 material_id 集合。"""
    groups: dict[object, list[MaterialRecord]] = {}
    for m in materials:
        k = key(m)
        if k is None:
            continue
        groups.setdefault(k, []).append(m)

    removed: set[str] = set()
    for grp in groups.values():
        if len(grp) <= 1:
            continue
        best = max(grp, key=lambda x: x.performance_score or 0)
        removed.update(x.material_id for x in grp if x.material_id != best.material_id)
    return removed


def classify(repo: MaterialRepo, rules: LowQualityRules) -> tuple[set[str], dict]:
    """拉全库素材，按规则分类，返回 (保留的 material_id 集合, 统计 dict)。

    统计字段：total / kept / removed / removed_by_duration /
              removed_by_md5 / removed_by_similar / removed_by_visual。
    """
    total = repo.count()
    materials = repo.get_all(limit=total or 1)
    all_ids = {m.material_id for m in materials}
    removed: set[str] = set()
    stats: dict = {"total": len(all_ids)}

    # 规则 1：时长过短
    dur_removed: set[str] = set()
    if rules.filter_short:
        dur_removed = {
            m.material_id for m in materials
            if (m.duration_ms or 0) < rules.min_duration_ms
        }
    removed |= dur_removed
    stats["removed_by_duration"] = len(dur_removed)

    # 规则 2：镜头重复（md5 完全重复 + 场景/景别/运镜近似重复）
    md5_removed: set[str] = set()
    if rules.dedup_md5:
        md5_removed = _dedup_by_key(materials, _md5_key)
    removed |= md5_removed
    stats["removed_by_md5"] = len(md5_removed)

    sim_removed: set[str] = set()
    if rules.dedup_similar:
        sim_removed = _dedup_by_key(materials, _similarity_key)
    removed |= sim_removed
    stats["removed_by_similar"] = len(sim_removed)

    # 规则 3：pHash 画面相似去重（只用已缓存 phash，不在此补算）
    visual_removed: set[str] = set()
    if rules.dedup_visual:
        from adflow.engine.visual_dedup import dedup_by_phash
        visual_removed = dedup_by_phash(materials, rules.visual_sim_threshold)
    removed |= visual_removed
    stats["removed_by_visual"] = len(visual_removed)

    stats["removed"] = len(removed)
    stats["kept"] = len(all_ids - removed)
    return all_ids - removed, stats
