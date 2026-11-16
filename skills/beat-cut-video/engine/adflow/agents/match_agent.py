"""
素材匹配 Agent — 分镜脚本 → 最优素材选择
- 标签过滤 + 评分排序（无 LLM）
- 匹配失败时调用 LLM fallback（创意替换）
- 集成 Diversity 控制 + 跨变体去重 + 随机化
"""
import random
from pathlib import Path
from dataclasses import dataclass

from adflow.models import (
    MaterialRecord, StoryboardShot, ShotMatchResult,
)
from adflow.db.material_repo import MaterialRepo
from adflow.config_loader import config


@dataclass
class MatchConfig:
    """匹配配置"""
    min_match_score: float = 0.0     # 最低匹配分（0=不拦截）
    tag_weight: float = 0.5
    performance_weight: float = 0.3
    freshness_weight: float = 0.2
    semantic_weight: float = 0.2     # 文案-画面语义相似度（中文CLIP）
    max_candidates: int = 30
    random_pick_top: int = 3         # 从Top-N候选随机选（1=确定性）


class MatchAgent:
    """素材匹配 Agent"""

    def __init__(self):
        self.repo = MaterialRepo()
        self.match_cfg = MatchConfig()
        diversity_cfg = config.diversity_config
        weights = diversity_cfg.get("match_weights", {})
        if weights:
            self.match_cfg.tag_weight = weights.get("tag_similarity", 0.5)
            self.match_cfg.performance_weight = weights.get("performance", 0.3)
            self.match_cfg.freshness_weight = weights.get("freshness", 0.2)
            self.match_cfg.semantic_weight = weights.get("semantic", 0.2)

    def match_script(
        self,
        shot_targets: list[StoryboardShot],
        account_id: str = "",
        reserved_material_ids: dict[str, int] | None = None,
        excluded_material_ids: set[str] | None = None,
        aspect: str = "portrait",
        variant_index: int = 0,
    ) -> tuple[list[ShotMatchResult], list[str]]:
        """
        为镜头目标列表匹配素材，带相邻差异化 + 跨变体去重：
        - 独立匹配每个镜头，确保每个 shot 都有素材
        - reserved_material_ids：material_id → 已使用次数（跨变体累计），严格按 0>1>2>...>n 分层
        - 素材不够时复用已有素材（选不同时间段）
        - aspect：输出画幅 portrait/landscape，按画幅过滤候选素材方向
        - variant_index：文案变体序号，参与截取窗口随机种子（跨变体同素材取不同画面段）
        返回 (匹配结果列表, 警告列表)
        """
        results = []
        warnings = []
        if reserved_material_ids is None:
            reserved_material_ids = {}
        if excluded_material_ids is None:
            excluded_material_ids = set()

        # 方向过滤白名单（None=不过滤）
        orientation_ok_ids = self._orientation_filter_ids(
            aspect, len(shot_targets))

        diversity_cfg = config.diversity_config
        window_size = diversity_cfg.get("window_size", 20)
        max_usage = diversity_cfg.get("max_usage_in_window", 2)
        recent_usage = self.repo.get_recent_usage(account_id, window_size)

        adj_cfg = diversity_cfg.get("adjacent_diversity", {})
        similarity_threshold = adj_cfg.get("similarity_threshold", 0.7)
        penalty_factor = adj_cfg.get("penalty_factor", 0.35)

        prev_material: MaterialRecord | None = None
        used_in_script: dict[str, int] = {}

        for shot in shot_targets:
            match_result = self._match_shot(
                shot, recent_usage, max_usage,
                penalize_similar_to=prev_material,
                similarity_threshold=similarity_threshold,
                penalty_factor=penalty_factor,
                used_in_script=used_in_script,
                reserved_material_ids=reserved_material_ids,
                excluded_material_ids=excluded_material_ids,
                orientation_ok_ids=orientation_ok_ids,
                variant_index=variant_index,
            )

            if match_result is None:
                fallback = self._fallback_match(
                    shot, recent_usage, max_usage,
                    used_in_script, reserved_material_ids,
                    excluded_material_ids,
                    orientation_ok_ids=orientation_ok_ids,
                    variant_index=variant_index)
                if fallback:
                    match_result = fallback
                    warnings.append(
                        f"镜{shot.shot_index}({shot.role}): 使用替代素材")
                else:
                    match_result = self._force_match(
                        shot, used_in_script, results, reserved_material_ids,
                        excluded_material_ids,
                        orientation_ok_ids=orientation_ok_ids)
                    if match_result:
                        warnings.append(
                            f"镜{shot.shot_index}({shot.role}): "
                            f"素材不足，复用已有素材")
                    else:
                        warnings.append(
                            f"镜{shot.shot_index}({shot.role}): 无可用素材，已跳过")
                        continue

            results.append(match_result)
            mid = match_result.material_id
            used_in_script[mid] = used_in_script.get(mid, 0) + 1

            prev_mat = self.repo.get_by_id(mid)
            if prev_mat:
                prev_material = prev_mat

        # ── 相邻相似度报告 ──
        for i in range(1, len(results)):
            mat_a = self.repo.get_by_id(results[i - 1].material_id)
            mat_b = self.repo.get_by_id(results[i].material_id)
            if mat_a and mat_b:
                sim = self._compute_visual_similarity(mat_a, mat_b)
                if sim >= similarity_threshold:
                    warnings.append(
                        f"⚠ 镜{results[i-1].shot_index}→镜{results[i].shot_index} "
                        f"素材相似度{sim:.0%}（{mat_a.scene}/{mat_a.shot_type} ↔ "
                        f"{mat_b.scene}/{mat_b.shot_type}），建议补充差异化素材"
                    )

        return results, warnings

    def _orientation_filter_ids(
            self, aspect: str, n_shots: int) -> set[str] | None:
        """按输出画幅过滤候选素材方向，返回放行的 material_id 集合（None=不过滤）。

        竖屏输出 → vertical + phone_rotated（渲染时自动回正）；
        横屏输出 → landscape。
        方向匹配的候选 < max(镜头数×1.5, 3) 时，放行另一方向素材兜底
        （按分辨率从高到低补够），保证能出片；探测失败的 unknown 永不放行。
        老库 orientation 未回填的，按宽高现推（h≥w=竖）。
        """
        if aspect not in ("portrait", "landscape"):
            return None
        want, alt = (
            (("vertical", "phone_rotated"), ("landscape",))
            if aspect == "portrait"
            else (("landscape",), ("vertical", "phone_rotated"))
        )

        def _ori(m: MaterialRecord) -> str:
            if m.orientation in ("vertical", "landscape", "phone_rotated"):
                return m.orientation
            # 未回填的老库行：宽高现推（元数据不在库里，宽高是够用的近似）
            return "vertical" if m.height >= m.width else "landscape"

        all_mats = self.repo.get_all(limit=0)
        primary = [m for m in all_mats if _ori(m) in want]
        min_needed = max(int(n_shots * 1.5), 3)
        ok_ids = {m.material_id for m in primary}
        if len(primary) >= min_needed:
            return ok_ids

        # 兜底：另一方向按分辨率从高到低补够
        alt_sorted = sorted(
            (m for m in all_mats if _ori(m) in alt),
            key=lambda m: m.width * m.height, reverse=True)
        for m in alt_sorted[:min_needed - len(primary)]:
            ok_ids.add(m.material_id)
        return ok_ids

    def _match_shot(
        self,
        shot: StoryboardShot,
        recent_usage: list,
        max_usage_in_window: int,
        penalize_similar_to: MaterialRecord | None = None,
        similarity_threshold: float = 0.7,
        penalty_factor: float = 0.35,
        used_in_script: dict[str, int] | None = None,
        reserved_material_ids: dict[str, int] | None = None,
        excluded_material_ids: set[str] | None = None,
        orientation_ok_ids: set[str] | None = None,
        variant_index: int = 0,
    ) -> ShotMatchResult | None:
        """为单个镜头匹配最佳素材（规则评分 + 相邻差异化 + 去重）。"""
        if used_in_script is None:
            used_in_script = {}
        if reserved_material_ids is None:
            reserved_material_ids = {}
        if excluded_material_ids is None:
            excluded_material_ids = set()

        # 1. 标签过滤（先精确匹配，不够时自动扩展到全部素材）
        #    limit=0 = 不设上限：用完优先，候选池必须覆盖全部素材，
        #    否则 scene 全空 + performance 全相同时，LIMIT 30 永远只取 rowid 前 30 个
        candidates = self.repo.get_available_for_shot(
            required_scene=shot.required_scene,
            required_emotion=shot.required_emotion,
            required_product_vis=shot.required_product_visibility,
            limit=0,
        )
        # 过滤掉本脚本已用过的素材 + 低质素材 + 跨变体已用素材，看还剩多少「未使用」候选
        unused = [m for m in candidates
                  if m.material_id not in used_in_script
                  and m.material_id not in excluded_material_ids
                  and m.material_id not in reserved_material_ids]
        # 如果未使用候选不够 → 扩展到全部素材（放宽标签限制）
        if len(unused) < 3:
            all_materials = self.repo.get_all(limit=0)
            # 合并：精确匹配优先，全库补充（set 差集去重）
            existing_ids = {m.material_id for m in candidates}
            candidates.extend(m for m in all_materials if m.material_id not in existing_ids)
        # 统一排除低质素材（精确匹配 + 全库扩展都过滤）
        if excluded_material_ids:
            candidates = [m for m in candidates if m.material_id not in excluded_material_ids]
        # 方向过滤（按输出画幅；None=不过滤）
        if orientation_ok_ids is not None:
            candidates = [m for m in candidates if m.material_id in orientation_ok_ids]
        if not candidates:
            return None

        # 2. 评分
        scored = []
        for mat in candidates:
            usage_count = sum(
                1 for u in recent_usage if u.material_id == mat.material_id)
            if usage_count >= max_usage_in_window:
                continue

            tag_score = self._compute_tag_similarity(shot, mat)
            perf = mat.performance_score / 100.0
            freshness = mat.freshness_score(shot.role, config.diversity_config)

            final = (
                self.match_cfg.tag_weight * tag_score +
                self.match_cfg.performance_weight * perf +
                self.match_cfg.freshness_weight * freshness
            )

            # ── 镜头角色类型权重：不同角色需要不同画面特质 ──
            role_bonus = MatchAgent._role_match_bonus(shot.role, mat)
            final += role_bonus * 0.15  # 15%权重

            # ── 短素材降权：<2s 内容力差，排序靠后（优先选够长的）──
            if mat.duration_ms < 2000:
                final *= 0.5

            # 相邻去重
            if penalize_similar_to is not None:
                sim = self._compute_visual_similarity(penalize_similar_to, mat)
                if sim >= similarity_threshold:
                    final *= penalty_factor

            # 同脚本复用：硬阻止——同一个视频内不重复用同一个素材
            reuse_count = used_in_script.get(mat.material_id, 0)
            if reuse_count > 0:
                continue  # 直接跳过，不重复使用

            # ── 跨变体去重：不再软降权，改为「未使用优先」硬分组（见下方挑选） ──
            scored.append((mat, final, tag_score))

        if not scored:
            return None

        # 2.5 语义对齐：只对规则分 Top-N 候选算中文 CLIP 语义相似度
        if self.match_cfg.semantic_weight > 0:
            scored.sort(key=lambda x: x[1], reverse=True)
            semantic_text = shot.narration_text or shot.description
            if semantic_text:
                semantic_n = min(10, len(scored))
                for i in range(semantic_n):
                    mat, final, tag_score = scored[i]
                    final += self.match_cfg.semantic_weight * self._semantic_score(
                        mat, semantic_text)
                    scored[i] = (mat, final, tag_score)

        # 3. 严格按使用次数分层 + 随机化挑选：0次>1次>2次>...>n次，同次数圈子内竞争
        def _usage(mid: str) -> int:
            return reserved_material_ids.get(mid, 0)
        min_usage = min(_usage(x[0].material_id) for x in scored)
        pool = [x for x in scored if _usage(x[0].material_id) == min_usage]
        pool.sort(key=lambda x: x[1], reverse=True)
        top_n = min(self.match_cfg.random_pick_top, len(pool))
        best_mat, best_score, _ = random.choice(pool[:top_n])

        # 4. 确定裁剪区间（复用时随机窗口 + 子片段重组，防跨视频画面重复）
        reuse_idx = used_in_script.get(best_mat.material_id, 0)
        use_total = reserved_material_ids.get(best_mat.material_id, 0)
        start_ms, end_ms, sub_ranges = self._build_clip_window(
            best_mat, shot.duration_ms, reuse_idx, use_total, variant_index)

        return ShotMatchResult(
            shot_index=shot.shot_index,
            material_id=best_mat.material_id,
            material_file=best_mat.file_path,
            start_ms=start_ms,
            end_ms=end_ms,
            match_score=best_score,
            sub_ranges=sub_ranges,
        )

    def _fallback_match(
        self,
        shot: StoryboardShot,
        recent_usage: list,
        max_usage_in_window: int,
        used_in_script: dict[str, int] | None = None,
        reserved_material_ids: dict[str, int] | None = None,
        excluded_material_ids: set[str] | None = None,
        orientation_ok_ids: set[str] | None = None,
        variant_index: int = 0,
    ) -> ShotMatchResult | None:
        """LLM fallback"""
        if used_in_script is None:
            used_in_script = {}
        if reserved_material_ids is None:
            reserved_material_ids = {}
        if excluded_material_ids is None:
            excluded_material_ids = set()

        all_materials = self.repo.get_all(limit=50)
        # 方向过滤（按输出画幅；None=不过滤）
        if orientation_ok_ids is not None:
            all_materials = [m for m in all_materials
                             if m.material_id in orientation_ok_ids]
        available = [
            m for m in all_materials
            if sum(1 for u in recent_usage if u.material_id == m.material_id) < max_usage_in_window
            and m.material_id not in excluded_material_ids
        ]
        if not available:
            available = all_materials[:20]
        if not available:
            return None

        # 优先选：未被其他变体占用 + 未被本脚本用过
        fresh = [m for m in available
                 if m.material_id not in reserved_material_ids
                 and m.material_id not in used_in_script]
        if not fresh:
            # 退一步：只排除本脚本用过的
            fresh = [m for m in available if m.material_id not in used_in_script]
        if not fresh:
            fresh = available

        try:
            # 未配置 LLM key 时直接走复用兜底，不做无谓的云端重试+本地兜底等待
            # （skill 无模型模式：每次空转重试约 10 秒 × 每个缺素材的镜头）
            import os as _os
            if not (config.llm_api_key or _os.environ.get("DASHSCOPE_API_KEY", "")):
                raise RuntimeError("LLM 未配置，跳过创意兜底")
            suggestion = self._call_fallback_llm(shot, fresh)
        except Exception:
            mat = fresh[0]
            reuse_idx = used_in_script.get(mat.material_id, 0)
            start_ms, end_ms = self._pick_segment(
                mat, shot.duration_ms, reuse_index=reuse_idx,
                use_count_total=reserved_material_ids.get(mat.material_id, 0),
                variant_index=variant_index)
            return ShotMatchResult(
                shot_index=shot.shot_index,
                material_id=mat.material_id,
                material_file=mat.file_path,
                start_ms=start_ms,
                end_ms=end_ms,
                match_score=0.2,
            )

        suggested_id = suggestion.get("suggested_material_id", "")
        mat = self.repo.get_by_id(suggested_id) if suggested_id else None
        if not mat:
            mat = fresh[0]
        if not mat:
            return None

        reuse_idx = used_in_script.get(mat.material_id, 0)
        start_ms, end_ms = self._pick_segment(
            mat, shot.duration_ms, reuse_index=reuse_idx,
            use_count_total=reserved_material_ids.get(mat.material_id, 0),
            variant_index=variant_index)
        return ShotMatchResult(
            shot_index=shot.shot_index,
            material_id=mat.material_id,
            material_file=mat.file_path,
            start_ms=start_ms,
            end_ms=end_ms,
            match_score=0.25,
        )

    def _force_match(
        self,
        shot: StoryboardShot,
        used_in_script: dict[str, int],
        existing_results: list[ShotMatchResult],
        reserved_material_ids: dict[str, int] | None = None,
        excluded_material_ids: set[str] | None = None,
        orientation_ok_ids: set[str] | None = None,
    ) -> ShotMatchResult | None:
        """最后兜底：从已有素材复用，限制单素材复用≤3次"""
        if reserved_material_ids is None:
            reserved_material_ids = {}
        if excluded_material_ids is None:
            excluded_material_ids = set()

        if not existing_results:
            all_mats = self.repo.get_all(limit=5)
            if orientation_ok_ids is not None:
                all_mats = [m for m in all_mats
                            if m.material_id in orientation_ok_ids]
            # 优先未被占用的
            for mat in all_mats:
                if (mat.material_id not in reserved_material_ids
                        and mat.material_id not in excluded_material_ids):
                    return ShotMatchResult(
                        shot_index=shot.shot_index,
                        material_id=mat.material_id,
                        material_file=mat.file_path,
                        start_ms=0,
                        end_ms=min(shot.duration_ms, mat.duration_ms),
                        match_score=0.1,
                    )
            if all_mats:
                mat = all_mats[0]
                return ShotMatchResult(
                    shot_index=shot.shot_index,
                    material_id=mat.material_id,
                    material_file=mat.file_path,
                    start_ms=0,
                    end_ms=min(shot.duration_ms, mat.duration_ms),
                    match_score=0.1,
                )
            return None

        # 找复用次数最少且≤3次的
        candidates = [(mid, cnt) for mid, cnt in used_in_script.items() if cnt <= 3]
        if not candidates:
            # 都复用≥4次了，取最少的
            candidates = list(used_in_script.items())
        best_mid = min(candidates, key=lambda x: x[1])[0]
        reuse_idx = used_in_script.get(best_mid, 0)
        mat = self.repo.get_by_id(best_mid)
        if not mat:
            return None

        start_ms, end_ms = self._pick_segment(
            mat, shot.duration_ms, reuse_index=reuse_idx)
        return ShotMatchResult(
            shot_index=shot.shot_index,
            material_id=mat.material_id,
            material_file=mat.file_path,
            start_ms=start_ms,
            end_ms=end_ms,
            match_score=0.1,
        )

    def _call_fallback_llm(
        self, shot: StoryboardShot, candidates: list[MaterialRecord],
    ) -> dict:
        """调用 LLM 做创意替换"""
        from adflow.agents.base_agent import BaseAgent
        agent = BaseAgent(temperature=0.3, task="match")

        candidates_summary = []
        for m in candidates[:15]:
            candidates_summary.append({
                "id": m.material_id,
                "scene": m.scene,
                "shot_type": m.shot_type,
                "emotion": m.emotion,
                "product_visibility": m.product_visibility,
                "tags": m.tags,
                "performance": m.performance_score,
            })

        user_msg = f"""## 分镜要求
- 角色: {shot.role}
- 时长: {shot.duration_ms}ms
- 描述: {shot.description}
- 需要场景: {shot.required_scene}
- 需要情绪: {shot.required_emotion}
- 需要产品露出: {shot.required_product_visibility}

## 候选素材
{__import__('json').dumps(candidates_summary, ensure_ascii=False, indent=2)}

请从候选素材中选择最合适的一个，输出 JSON：
{{"suggested_material_id": "...", "reasoning": "..."}}
"""
        prompt_path = Path(__file__).parent / "prompts" / "match_fallback_prompt.txt"
        with open(prompt_path, "r", encoding="utf-8") as f:
            system_prompt = f.read()

        return agent.call_structured(
            system_prompt=system_prompt,
            user_message=user_msg,
            output_schema={
                "type": "object",
                "properties": {
                    "suggested_material_id": {"type": "string"},
                    "reasoning": {"type": "string"},
                },
                "required": ["suggested_material_id", "reasoning"],
            },
        )

    # ═══════════════════════════════════════
    # 辅助方法
    # ═══════════════════════════════════════

    @staticmethod
    def _visual_fingerprint(mat: MaterialRecord) -> tuple:
        return (
            mat.scene or "",
            mat.shot_type or "",
            mat.camera_movement or "",
            mat.lighting or "",
        )

    @staticmethod
    def _compute_visual_similarity(
        mat_a: MaterialRecord, mat_b: MaterialRecord,
    ) -> float:
        score = 0.0
        fp_a = MatchAgent._visual_fingerprint(mat_a)
        fp_b = MatchAgent._visual_fingerprint(mat_b)

        if fp_a[0] and fp_b[0] and fp_a[0] == fp_b[0]:
            score += 0.50
        elif fp_a[0] and fp_b[0]:
            parts_a = fp_a[0].split("_")
            parts_b = fp_b[0].split("_")
            if parts_a[0] == parts_b[0]:
                score += 0.25

        if fp_a[1] and fp_b[1] and fp_a[1] == fp_b[1]:
            score += 0.35
        if fp_a[2] and fp_b[2] and fp_a[2] == fp_b[2]:
            score += 0.10
        if fp_a[3] and fp_b[3] and fp_a[3] == fp_b[3]:
            score += 0.05

        return min(score, 1.0)

    @staticmethod
    def _semantic_score(mat: MaterialRecord, text: str) -> float:
        """文案-画面语义相似度 0-1（中文 CLIP，失败回退中性 0.5）"""
        try:
            from adflow.engine import semantic_matcher
            img_feat = semantic_matcher.image_feature_from_video(mat.file_path)
            txt_feat = semantic_matcher.encode_text(text)
            if img_feat is None or txt_feat is None:
                return 0.5
            return semantic_matcher.similarity(img_feat, txt_feat)
        except Exception:
            return 0.5

    @staticmethod
    def _compute_tag_similarity(shot: StoryboardShot, mat: MaterialRecord) -> float:
        """计算分镜要求与素材标签的匹配度 (0.0-1.0)"""
        score = 0.0
        checks = 0

        if shot.required_scene:
            checks += 1
            if mat.scene and shot.required_scene in mat.scene:
                score += 1.0
            elif mat.scene and "_" in shot.required_scene and "_" in mat.scene \
                    and shot.required_scene.split("_")[1:] == mat.scene.split("_")[1:]:
                score += 0.5

        if shot.required_emotion:
            checks += 1
            if shot.required_emotion == mat.emotion:
                score += 1.0

        if shot.required_product_visibility:
            checks += 1
            if shot.required_product_visibility == mat.product_visibility:
                score += 1.0

        return score / checks if checks > 0 else 0.5

    @staticmethod
    def _role_match_bonus(role: str, mat: MaterialRecord) -> float:
        """镜头角色→画面特质匹配加分 0-10

        钩子: 视觉冲击力（人脸/动作/高亮度）
        卖点: 产品特写（产品露出/包装展示）
        CTA:  行动引导（高能量/高亮度/紧迫感）
        """
        bonus = 0.0

        if role in ("hook",):
            # 钩子需要抓住注意力：有人脸+2，有动作+1，亮度高+1
            if mat.has_person:
                bonus += 2.0
            if mat.pace in ("fast", "快节奏") or mat.camera_movement in ("handheld", "tracking"):
                bonus += 1.5
            if mat.lighting in ("bright", "亮") or mat.emotion in ("excited", "happy", "激昂"):
                bonus += 1.0

        elif role in ("product_demo", "solution", "b_roll"):
            # 卖点展开需要产品特写：全露+3，包装+2，使用场景+1
            vis = mat.product_visibility or ""
            if vis in ("full", "usage"):
                bonus += 3.0
            elif vis in ("packaging",):
                bonus += 2.0
            elif vis in ("partial",):
                bonus += 1.0
            # 产品镜头也需要好的光线
            if mat.lighting in ("bright", "soft", "亮", "柔"):
                bonus += 0.5

        elif role in ("cta",):
            # CTA需要紧迫感和行动引导：高能量情绪+2，快节奏+1
            if mat.emotion in ("urgent", "excited", "紧迫", "激昂"):
                bonus += 2.5
            if mat.pace in ("fast", "快节奏"):
                bonus += 1.5
            # 有人脸指方向/点屏幕等动作加分
            if mat.has_person:
                bonus += 1.0

        return min(10.0, bonus)

    @staticmethod
    def _pick_segment(mat: MaterialRecord, target_ms: int,
                      reuse_index: int = 0, use_count_total: int = 0,
                      variant_index: int = 0) -> tuple[int, int]:
        """从素材中选择合适的时间段。

        首次使用取中段（质量优先）；复用时改用确定性随机起点
        （seed 含 use_count_total/variant_index/reuse_index），
        同一素材每次被用取到的时间窗都不同，防平台跨视频判重。
        """
        dur = mat.duration_ms
        if dur <= target_ms:
            return (0, dur)

        if use_count_total <= 0 and reuse_index <= 0:
            start = (dur - target_ms) // 2
            start = max(0, start)
            end = min(dur, start + target_ms)
            return (start, end)

        # 复用：随机起点（同 seed 可复现，跨变体/跨视频不同）
        rng = random.Random(
            f"{mat.material_id}|{use_count_total}|{variant_index}|{reuse_index}")
        start = rng.randint(0, dur - target_ms)
        return (start, start + target_ms)

    def _build_clip_window(self, mat: MaterialRecord, target_ms: int,
                           reuse_idx: int, use_total: int,
                           variant_index: int
                           ) -> tuple[int, int, list | None]:
        """决定一个镜头的取景窗口；第 2 次起用子片段重组。

        子片段重组：目标时长拆两半——前半延续本次随机窗口，
        后半在素材里再随机取一段，拼成一个"新镜头"，
        即使同一素材被用多次，成片画面组合也不重样。
        返回 (start_ms, end_ms, sub_ranges|None)。
        """
        start_ms, end_ms = self._pick_segment(
            mat, target_ms, reuse_index=reuse_idx,
            use_count_total=use_total, variant_index=variant_index)
        dur = mat.duration_ms
        # 素材长度余量不足时不拆（拆了容易撞边界）
        if (use_total + reuse_idx) <= 0 or dur < target_ms * 2.5:
            return start_ms, end_ms, None

        half = target_ms // 2
        rng = random.Random(
            f"{mat.material_id}|sub|{use_total}|{variant_index}|{reuse_idx}")
        s1, e1 = start_ms, start_ms + half
        s2 = rng.randint(e1, max(dur - half, e1))
        e2 = min(s2 + half, dur)
        if e2 - s2 >= half * 0.8:  # 后半够长才拼，否则退回单窗口
            return start_ms, end_ms, [(s1, e1), (s2, e2)]
        return start_ms, end_ms, None
