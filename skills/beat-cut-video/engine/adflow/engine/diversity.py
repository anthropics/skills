"""
Diversity 控制系统
- 冷却时间：同一素材使用后有强制冷却期
- 滑动窗口：最近 N 条产出内同一素材最多出现 M 次
- 新鲜度评分：融入 match_agent 的素材评分体系
"""

from datetime import datetime, timedelta

from adflow.models import MaterialRecord, MaterialUsageLog
from adflow.db.material_repo import MaterialRepo
from adflow.config_loader import config


class DiversityController:
    """素材多样性控制器"""

    def __init__(self):
        cfg = config.diversity_config
        self.cooldown_default = cfg.get("cooldown_hours_default", 48)
        self.cooldown_hook = cfg.get("cooldown_hours_hook", 72)
        self.cooldown_cta = cfg.get("cooldown_hours_cta", 36)
        self.window_size = cfg.get("window_size", 20)
        self.max_usage_in_window = cfg.get("max_usage_in_window", 2)
        self.repo = MaterialRepo()

    def get_cooldown_hours(self, shot_role: str) -> int:
        """根据镜头角色返回冷却小时数"""
        role_lower = shot_role.lower()
        if "hook" in role_lower:
            return self.cooldown_hook
        if "cta" in role_lower:
            return self.cooldown_cta
        return self.cooldown_default

    def is_in_cooldown(self, material: MaterialRecord, shot_role: str = "default") -> bool:
        """检查素材是否在冷却期内"""
        if not material.last_used_at:
            return False
        required = self.get_cooldown_hours(shot_role)
        last = datetime.fromisoformat(material.last_used_at)
        return (datetime.now() - last) < timedelta(hours=required)

    def freshness_score(self, material: MaterialRecord, shot_role: str = "default") -> float:
        """新鲜度评分 0.0-1.0"""
        if not material.last_used_at:
            return 1.0
        required = self.get_cooldown_hours(shot_role)
        last = datetime.fromisoformat(material.last_used_at)
        hours_since = (datetime.now() - last).total_seconds() / 3600
        if hours_since >= required:
            return 1.0
        return hours_since / max(required, 1)

    def filter_by_diversity(
        self,
        candidates: list[MaterialRecord],
        account_id: str,
        shot_role: str = "default",
    ) -> list[MaterialRecord]:
        """
        过滤候选素材：
        1. 排除冷却期内的
        2. 排除滑动窗口超标的使用次数
        返回过滤后的列表（含新鲜度更新）
        """
        recent_usage = self.repo.get_recent_usage(account_id, self.window_size)

        filtered = []
        for mat in candidates:
            # 冷却检查（冷却期内的直接排除，不给分）
            if self.is_in_cooldown(mat, shot_role):
                continue

            # 滑动窗口计数
            window_count = sum(
                1 for u in recent_usage if u.material_id == mat.material_id
            )
            if window_count >= self.max_usage_in_window:
                continue

            filtered.append(mat)

        return filtered

    def apply_freshness_to_scores(
        self,
        scored_candidates: list[tuple[MaterialRecord, float]],
        shot_role: str = "default",
    ) -> list[tuple[MaterialRecord, float]]:
        """
        将新鲜度因子乘入已有评分（用于 match_agent 的评分阶段）
        输入: [(material, base_score), ...]
        输出: [(material, adjusted_score), ...]
        """
        adjusted = []
        for mat, base_score in scored_candidates:
            fresh = self.freshness_score(mat, shot_role)
            adjusted.append((mat, base_score * (0.5 + 0.5 * fresh)))

        adjusted.sort(key=lambda x: x[1], reverse=True)
        return adjusted

    def log_usage(
        self,
        material_id: str,
        variant_id: str,
        shot_position: int,
        account_id: str,
    ) -> None:
        """记录素材使用（出片后调用）"""
        usage = MaterialUsageLog(
            material_id=material_id,
            ad_variant_id=variant_id,
            shot_position=shot_position,
            used_at=datetime.now().isoformat(),
            account_id=account_id,
        )
        self.repo.log_usage(usage)
