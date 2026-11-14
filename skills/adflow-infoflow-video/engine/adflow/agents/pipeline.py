"""
Pipeline 编排器 — 串联所有 Agent 的执行流程

流程：
  产品信息 → 策略Agent → 脚本Agent → 匹配Agent → 剪辑引擎 → 变体工厂 → 成品
                              ↑                                    ↓
                    优化Agent ←── 投放数据回流 ←── 投放平台API

单次任务流程：
  1. 创建任务 (ProjectTask)
  2. 策略 Agent → CreativeStrategy
  3. 脚本 Agent → list[StoryboardScript]
  4. 匹配 Agent → list[EditTimeline]
  5. 变体工厂 → 批量渲染视频
  6. 合规审查 → 标记每个变体
  7. 保存所有中间产物到数据库
"""

import copy
import json
import logging
import os
from datetime import datetime
from typing import Optional

logger = logging.getLogger("adflow.pipeline")

from adflow.config_loader import config
from adflow.models import (
    ProductProfile, ProjectTask, CreativeStrategy,
    StoryboardScript, StoryboardShot, EditTimeline,
    AdVariant, StyleProfile,
)
from adflow.agents.strategy_agent import StrategyAgent
from adflow.agents.script_agent import ScriptAgent
from adflow.agents.match_agent import MatchAgent
from adflow.engine.variant_factory import VariantFactory, VariantConfig
from adflow.engine.bgm_library import BGMLibrary
from adflow.engine.tts_engine import (
    create_tts_engine, detect_emotion,
)
from adflow.compliance.ad_law_checker import AdLawChecker
from adflow.db.project_repo import ProjectRepo
from adflow.db.material_repo import MaterialRepo

# ── 过滤模型 ──
from adflow.filters.base_filter import Verdict
from adflow.filters.copy_filter import CopyFilter
from adflow.filters.tts_filter import TTSFilter
from adflow.filters.dedup_filter import DedupFilter
from adflow.monitor.budget_tracker import get_budget_tracker


class PipelineCancelled(Exception):
    """用户主动停止出片（协作式取消）"""


class PipelineResult:
    """Pipeline 执行结果"""

    def __init__(self):
        self.task_id: str = ""
        self.strategy: Optional[CreativeStrategy] = None
        self.scripts: list[StoryboardScript] = []
        self.timelines: list[EditTimeline] = []  # 每个脚本一条
        self.variants: list[AdVariant] = []
        self.warnings: list[str] = []
        self.errors: list[str] = []
        self.success: bool = False
        self.creative_scores: list = []  # CreativeScorer 预评分结果
        self.repetition_stats: dict = {}  # 镜头重复度统计 {unique_materials, total_shots, rate, material_total}
        self.cancelled: bool = False  # 是否被用户主动停止

    @property
    def summary(self) -> str:
        return (
            f"Pipeline 执行{'成功' if self.success else '失败'}\n"
            f"  脚本数: {len(self.scripts)}\n"
            f"  变体数: {len(self.variants)}\n"
            f"  警告: {len(self.warnings)} | 错误: {len(self.errors)}"
        )


class AdPipeline:
    """
    信息流广告 Agent 剪辑主流程编排器
    """

    def __init__(self, model: str | None = None):
        self.model = model
        self.strategy_agent = StrategyAgent(model=model)
        self.script_agent = ScriptAgent(model=model)
        self.match_agent = MatchAgent()
        self.variant_factory = VariantFactory()
        self.checker = AdLawChecker()
        self.project_repo = ProjectRepo()
        self.material_repo = MaterialRepo()
        # 过滤模型
        self.copy_filter = CopyFilter()
        self.tts_filter = TTSFilter()
        fs = config.get("filter_system", {})
        self.filter_enabled = fs.get("enabled", True) if isinstance(fs, dict) else True
        self._shot_dur_override = 0  # 审核弹窗设置的镜头时长（0=用 config）
        self._bgm_override = ""      # 审核弹窗指定的 BGM 绝对路径（空=自动轮换）
        self._pause_ms_override = None  # 审核弹窗设置的句间停顿（None=AI 按角色动态）
        self._digital_human = ""     # 审核弹窗指定的数字人形象（""=不选 / "auto"=按配音性别自动）
        self._dh_auto_index: dict[str, int] = {}  # auto 模式按性别轮换计数（gender → 已用数）
        self._should_cancel = None  # Callable[[], bool] | None — 出片取消回调

    def _scripts_from_plain_text(
        self, text: str, task, strategy_id: str,
        target_duration_ms: int, variant_count: int,
        deep_copy_variants: bool,
    ) -> list:
        """纯文案 → StoryboardScript[]（不经 LLM）。

        Phase 1.5 自定义文案和 Phase 3.0 审核弹窗手改文案共用：
        标点断句 → 逐段建镜头（hook/正文/cta）→ 入库；
        deep_copy_variants=True 时按 variant_count 深拷贝 N 份同文案脚本（用爆款=视频数量）。
        """
        from adflow.engine.subtitle_renderer import break_by_punctuation
        segments = break_by_punctuation(text)
        # 过滤镜头描述（以「（」开头或以「）」结尾的段，如「（开场画面」「特写…）」）
        segments = [seg for seg in segments
                    if not (seg.startswith("（") or seg.endswith("）"))]
        shots = []
        total_dur = target_duration_ms
        n_segs = max(len(segments), 1)
        dur_per_shot = max(2000, total_dur // n_segs)
        remaining = total_dur
        for i, seg in enumerate(segments):
            role = "hook" if i == 0 else (
                "cta" if i == len(segments) - 1 else "product_demo")
            # 倒数第1镜拿剩余时长，避免负数
            if i == n_segs - 1:
                shot_dur = max(1000, remaining)
            else:
                shot_dur = max(1000, min(dur_per_shot, remaining - 1000))
            remaining -= shot_dur
            shots.append(StoryboardShot(
                shot_index=i,
                role=role,
                duration_ms=shot_dur,
                description=seg,
                narration_text=seg,
                narration_segments=json.dumps([seg], ensure_ascii=False),
                # 不设 required_emotion/scene，让素材库全部可参与匹配
            ))
        script = StoryboardScript(
            task_id=task.task_id,
            strategy_id=strategy_id,
            shots=shots,
            cta_text=segments[-1] if segments else "",
            total_duration_ms=target_duration_ms,
            variant_index=0,
            created_at=datetime.now().isoformat(),
        )
        script.script_id = self.project_repo.insert_script(script)
        if deep_copy_variants and variant_count > 1:
            scripts = [script]
            for _vi in range(1, variant_count):
                _s = copy.deepcopy(script)
                _s.variant_index = _vi
                # 清空深拷贝来的 script_id，让 insert_script 重新生成独立 id（否则与视频 0 撞 UNIQUE 约束）
                _s.script_id = ""
                _s.script_id = self.project_repo.insert_script(_s)
                scripts.append(_s)
            return scripts
        return [script]

    def run(
        self,
        product: ProductProfile,
        platform: str = "ocean_engine",
        account_id: str = "",
        target_duration_ms: int = 0,       # 0=自动(30秒黄金线，配音为主)
        variant_count: int = 5,
        recent_performance: dict | None = None,
        bgm_files: list[str] | None = None,
        progress_callback=None,
        style_name: str = "",
        ref_hit_ids: list[str] | None = None,
        # ── 自定义输入（AI出片→风格模板→上次txt文案/配音）──
        custom_text: str = "",              # 用户自写文案（跳过策略+脚本Agent）
        custom_audio: str = "",             # 用户上传配音文件路径
        name_prefix: str = "",              # 视频命名前缀（""=默认日期命名；非空=前缀+序号，如「视频01」）
        aspect_ratio: str = "portrait",     # 输出画幅 portrait竖屏 / landscape横屏
        low_quality_rules=None,             # 低质镜头过滤规则 LowQualityRules（None=不过滤）
        voice_override: str = "",           # 指定配音音色（空=按配置自动选）
        speech_rate_override: float = 0.0,  # 语速倍率（0=用引擎默认，>0=强制倍率）
        pause_ms_override: int = 0,         # 固定句间停顿ms（0=AI自动；无审核回调时由此传入）
        shot_duration_override: int = 0,    # 固定镜头时长ms（0=用config）
        bgm_file_override: str = "",        # 指定BGM文件（空=自动轮换）
        review_callback=None,               # 出片前审核回调 fn(script_text) → bool
        should_cancel=None,                 # 协作式取消回调 fn() -> bool（True=停止），在阶段边界检查
    ) -> PipelineResult:
        """执行完整的广告生产流程

        custom_text: 用户提供的文案 → 跳过策略+脚本Agent，直接配音+混剪
        custom_audio: 用户提供的配音 → 跳过TTS，直接匹配素材+混剪
        voice_override: 指定配音音色ID，空则按config自动选
        speech_rate_override: 语速倍率，0则用引擎默认，>0=强制倍率
        review_callback: 出片前审核回调，返回True=确认继续，False=需要重写
        """
        result = PipelineResult()
        self._should_cancel = should_cancel

        # 无审核回调的调用方（如配音裂变）直接传弹窗参数；
        # 有回调时审核弹窗的值稍后覆盖这些默认
        self._pause_ms_override = pause_ms_override if pause_ms_override > 0 else None
        self._shot_dur_override = shot_duration_override or 0
        self._bgm_override = bgm_file_override or ""
        self._subtitle_align_map = {}   # script_id → (字幕文本列表, 语音段列表)

        # 加载风格上下文
        style_context = ""
        if style_name:
            try:
                root = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
                style_path = os.path.join(root, "styles", f"{style_name}.json")
                if os.path.exists(style_path):
                    with open(style_path, "r", encoding="utf-8") as f:
                        style_data = json.load(f)
                    profile = StyleProfile.from_dict(style_data)
                    style_context = profile.build_prompt_context()
            except Exception:
                pass

        try:
            # 视频命名前缀（""=默认日期命名；非空=前缀+序号，如「视频01」）
            self.variant_factory.name_prefix = name_prefix
            # ---- Phase 0: 确保产品已入库 ----
            if not product.product_id or not self.project_repo.get_product(product.product_id):
                product.product_id = self.project_repo.insert_product(product)
                self._report(progress_callback, f"产品已入库: {product.name}")

            # ---- Phase 1: 创建任务 ----
            self._report(progress_callback, "创建任务...")
            task = ProjectTask(
                product_id=product.product_id,
                platform=platform,
                account_id=account_id,
                target_duration_ms=target_duration_ms,
                variant_count=variant_count,
                status="running",
                created_at=datetime.now().isoformat(),
            )
            task.task_id = self.project_repo.insert_task(task)
            result.task_id = task.task_id

            # ── 智能时长: 30秒黄金线，配音为主时钟 ──
            if target_duration_ms <= 0:
                from adflow.engine.smart_duration import suggest_duration
                dur_info = suggest_duration(
                    product_category=product.category,
                    custom_target_ms=0,
                )
                target_duration_ms = dur_info["target_ms"]
                self._report(progress_callback,
                             f"智能时长: {target_duration_ms/1000:.0f}秒 "
                             f"({dur_info['note']})")
            task.target_duration_ms = target_duration_ms

            # ── 预算追踪 ──
            budget = get_budget_tracker()
            budget.start_task(task.task_id)

            # 成本估算
            tts_cfg = config.tts_config
            estimate = budget.estimate(
                variant_count=variant_count,
                tts_backend=(tts_cfg if isinstance(tts_cfg, dict) else {}).get("backend", "volcano"),
                llm_model=config.llm_model,
            )
            self._report(progress_callback,
                         f"预估成本: ¥{estimate.total_cost:.3f} "
                         f"(LLM ¥{estimate.llm_cost:.3f} + TTS ¥{estimate.tts_cost:.3f})")

            # ---- Phase 1.5: 自定义输入处理（AI出片→风格模板→文案/配音） ----
            custom_mode = bool(custom_text or custom_audio)

            if custom_text:
                self._report(progress_callback, "使用自定义文案，跳过策略+脚本Agent...")
                # 用爆款/自写文案：原文直接用（微改/仿写已删，2026-10-17 小白化）
                final_text = custom_text

                # 快速创建脚本（绕过LLM）
                fake_strategy = CreativeStrategy(
                    strategy_id=f"custom_text_{task.task_id[:8]}",
                    task_id=task.task_id,
                    narrative_type="用户提供",
                    hook_type="自定义",
                    pace_style="medium",
                    tone="口语",
                    key_message=final_text[:50],
                    target_emotion="中性",
                    reasoning="用户自写文案",
                    created_at=datetime.now().isoformat(),
                )
                fake_strategy.strategy_id = self.project_repo.insert_strategy(
                    fake_strategy)
                self.project_repo.update_task_strategy(
                    task.task_id, fake_strategy.strategy_id)

                # 用爆款原文：文案固定、无「文案变体」，此处 variant_count 语义 = 视频数量。
                # 深拷贝 N 份同文案 script 即 N 个视频，
                # 差异 = 配音(男女交替) × 画面(跨视频去重)；variant_index 在此为「视频序号」。
                scripts = self._scripts_from_plain_text(
                        final_text, task, fake_strategy.strategy_id,
                    target_duration_ms, variant_count, True)
                result.strategy = fake_strategy
                result.scripts = scripts
                from adflow.engine.subtitle_renderer import break_by_punctuation
                _segs = break_by_punctuation(final_text)
                self._report(progress_callback,
                             f"自定义文案: {len(_segs)}段 → 直接进入配音")

            elif custom_audio:
                self._report(progress_callback, "使用自定义配音，跳过TTS...")
                # 仍然需要策略+脚本Agent做素材匹配
                # Fall through to normal pipeline but skip TTS later

            # ── Copy Mode Gate：根据输入类型判断生成模式 ──
            copy_mode = "product_only"
            mode_context = ""
            try:
                from adflow.agents.mode_gate import ModeGate
                copy_mode = ModeGate.detect(
                    custom_text=custom_text,
                    custom_audio=custom_audio,
                    ref_hit_ids=ref_hit_ids,
                )
                mode_context = ModeGate.build_mode_context(copy_mode, ref_hit_ids)
                if copy_mode != "product_only":
                    self._report(progress_callback, f"生成模式: {copy_mode}")
            except Exception:
                pass

            # ── 创意角度预选 ──
            selected_angles = []
            angle_context = ""
            if not custom_text:
                try:
                    from adflow.engine.creative_matrix import CreativeMatrix
                    selling_points = []
                    raw = product.key_selling_points or ""
                    if raw.startswith("["):
                        selling_points = json.loads(raw)
                    else:
                        selling_points = [s.strip() for s in raw.split("\n") if s.strip()]
                    if not selling_points:
                        selling_points = [product.name]

                    matrix = CreativeMatrix(product.name, product.category)
                    matrix.generate(selling_points)
                    selected_angles = matrix.select(
                        n=variant_count, product_id=product.product_id)
                    if selected_angles:
                        angle_context = CreativeMatrix.build_prompt_context(
                            selected_angles)
                        self._report(progress_callback,
                                     f"创意角度: {len(selected_angles)}个已分配(历史降权生效)")
                except Exception:
                    pass

            if not custom_text:
                # ---- Phase 2: 策略 Agent ----
                self._report(progress_callback, "策略 Agent 分析中...")

            # 注入爆款参考上下文
            hit_context = ""
            if ref_hit_ids:
                try:
                    from adflow.analytics.hit_library import hit_library
                    hit_context = hit_library.build_reference_context(ref_hit_ids)
                    if hit_context:
                        self._report(progress_callback,
                                     f"已注入 {len(ref_hit_ids)} 条爆款参考")
                except Exception as e:
                    logger.warning("爆款参考注入失败: %s", e)

            # ── 参考视频分析（对标 OpenMontage 的 reference-driven creation）──
            ref_analysis_context = ""
            if ref_hit_ids:
                try:
                    from adflow.analytics.hit_library import hit_library
                    from adflow.analytics.reference_analyzer import ReferenceAnalyzer
                    analyzer = ReferenceAnalyzer()
                    for hit_id in ref_hit_ids[:2]:  # 最多分析2个参考视频
                        video_path = hit_library.get_video_path(hit_id)
                        if video_path and os.path.exists(video_path):
                            ref_result = analyzer.analyze(video_path, source_type="hit_library")
                            if ref_result and ref_result.confidence >= 0.5:
                                ctx = analyzer.build_strategy_context(
                                    ref_result, product.category)
                                ref_analysis_context += ctx + "\n\n"
                                self._report(
                                    progress_callback,
                                    f"参考视频分析: hook={ref_result.hook_type} "
                                    f"节奏={ref_result.shot_pace} ({ref_result.confidence:.0%})")
                except Exception as e:
                    logger.warning("参考视频分析失败: %s", e)

            full_style_context = style_context
            if mode_context:
                full_style_context = mode_context + "\n\n" + (full_style_context or "")
            if ref_analysis_context:
                full_style_context = ref_analysis_context + "\n\n" + (full_style_context or "")
            elif hit_context:
                full_style_context = hit_context + "\n\n" + (full_style_context or "")

            # ── 爆款因子洞察注入（从历史投放数据学习）──
            factor_context = ""
            try:
                from adflow.analytics.aesthetic_model import AestheticModel
                from adflow.analytics.factor_analyzer import FactorAnalyzer
                model = AestheticModel()
                if hasattr(model, 'load') and model.load():
                    analyzer = FactorAnalyzer()
                    report = analyzer.analyze(model=model)
                    if report and getattr(report, 'top_factors', []):
                        lines = ["## 历史爆款因子洞察（基于投放数据）",
                                  ""]
                        for bm in report.top_factors[:5]:
                            lines.append(
                                f"- {bm.name}: 爆款区间[{bm.hit_min:.2f},"
                                f"{bm.hit_max:.2f}] 重要性{bm.importance:.2f}")
                        factor_context = "\n".join(lines)
                        self._report(progress_callback, "爆款因子洞察已注入")
            except Exception:
                pass

            if not custom_text:
                strategy = self.strategy_agent.generate(
                    product=product,
                    platform=platform,
                    recent_performance=recent_performance,
                    iteration_round=0,
                    style_context=(full_style_context + "\n\n" + angle_context
                                   + "\n\n" + factor_context)
                    if (angle_context or factor_context)
                    else full_style_context,
                )
                strategy.task_id = task.task_id
                strategy.strategy_id = self.project_repo.insert_strategy(strategy)
                self.project_repo.update_task_strategy(task.task_id, strategy.strategy_id)
                result.strategy = strategy

            if not custom_text:
                # ---- Phase 3: 脚本 Agent ----
                self._report(progress_callback, f"脚本 Agent 生成 {variant_count} 个变体脚本...")
                scripts = self.script_agent.generate(
                    strategy=strategy,
                    product=product,
                    target_duration_ms=target_duration_ms,
                    variant_count=variant_count,
                    platform=platform,
                    selected_angles=selected_angles or None,
                )
                # 保存脚本到数据库
                for script in scripts:
                    script.task_id = task.task_id
                    script.strategy_id = strategy.strategy_id
                    script.script_id = self.project_repo.insert_script(script)
                result.scripts = scripts

            # ── 标记使用的角度（下次自动降权）──
            if selected_angles and scripts:
                try:
                    from adflow.engine.angle_history import AngleHistory
                    hist = AngleHistory(product.product_id, product.name)
                    for a in selected_angles:
                        hist.mark_used(a["angle_key"], a.get("selling_point", ""),
                                       a.get("audience", ""))
                except Exception:
                    pass

            # ---- Phase 3.0: 出片前审核（人工确认文案文字，不含镜头/分镜） ----
            if review_callback and scripts:
                self._report(progress_callback, "等待人工审核文案...")
                # 构建文案预览：按口播断句逐句换行（与成片字幕同源：narration_segments → 标点断句）
                from adflow.engine.resynth import collect_narration_segments
                variant_segs = [collect_narration_segments(s)[0] for s in scripts]
                # 多变体且文案相同（用爆款原文深拷贝）→ 只显示一份 + 标注视频数，避免 N 份重复刷屏
                if len(scripts) > 1 and variant_segs and all(segs == variant_segs[0] for segs in variant_segs):
                    preview = f"【共 {len(scripts)} 个视频 · 文案相同】\n" + "\n".join(variant_segs[0])
                else:
                    preview = "\n\n".join(
                        f"【变体{s.variant_index}】\n" + "\n".join(segs)
                        for s, segs in zip(scripts, variant_segs)
                    )
                # 校验：全部变体均无有效口播 → 不弹空审核框（静默失败）
                if not any(variant_segs):
                    raise RuntimeError(
                        "LLM 未生成有效口播文案（narration 为空），请检查云端/本地模型输出")
                approved = review_callback(preview)
                # 读取审核弹窗设置的镜头时长/BGM/数字人（覆盖 config）
                _rv = getattr(review_callback, 'params', {}) or {}
                self._shot_dur_override = _rv.get('shot_duration_ms', 0) or 0
                self._bgm_override = _rv.get('bgm_file', '') or ""
                self._digital_human = _rv.get('digital_human', '') or ""
                _pause = _rv.get('pause_ms', 0) or 0
                self._pause_ms_override = _pause if _pause > 0 else None
                # 音色/语速在审核弹窗里选的值优先于调用时传参
                # （worker 在弹窗弹出前求值会传空，修复音色/语速传不进当次运行）
                _voice = _rv.get('voice_id') or ""
                if _voice:
                    voice_override = _voice
                _srate = _rv.get('speech_rate') or 0.0
                if _srate:
                    speech_rate_override = _srate
                # 手改文案（仅同文案多变体场景，如用爆款）：按新文案重建脚本，
                # 配音/字幕用新文案；多文案变体（创造模式）暂不支持弹窗改稿
                _edited_raw = (_rv.get('edited_text') or "").strip()
                if _edited_raw and scripts:
                    _edited_lines = [ln.strip() for ln in _edited_raw.splitlines()
                                     if ln.strip() and not ln.strip().startswith("【")]
                    _same_text = len(variant_segs) > 1 and all(
                        segs == variant_segs[0] for segs in variant_segs)
                    if _edited_lines and _same_text and _edited_lines != variant_segs[0]:
                        _strategy_id = (result.strategy.strategy_id
                                        if result.strategy else "")
                        scripts = self._scripts_from_plain_text(
                            "\n".join(_edited_lines), task, _strategy_id,
                            target_duration_ms, len(scripts), True)
                        result.scripts = scripts
                        self._report(progress_callback,
                                     f"文案已手动修改: {len(_edited_lines)}段，按新文案配音")
                    elif _edited_lines and not _same_text:
                        result.warnings.append(
                            "多文案变体模式暂不支持审核弹窗改文案，修改已忽略")
                if not approved:
                    self._report(progress_callback, "审核未通过，文案已驳回")
                    result.warnings.append("用户审核驳回")
                    return result

            # ---- Phase 3.1: 文案过滤 + 去重检测 ----
            qualified_scripts = []
            dedup_filter = DedupFilter()
            if self.filter_enabled and not custom_text:
                self._report(progress_callback, "文案质量过滤中...")
                for i, script in enumerate(scripts):
                    other_scripts = [s for j, s in enumerate(scripts) if j != i]
                    ctx = {
                        "other_scripts": other_scripts,
                        "category": product.category,
                        "variant_index": i,
                    }
                    copy_result = self.copy_filter.evaluate(script, ctx)
                    status = "✅" if copy_result.is_ok else "❌"

                    # ── 去重检测 ──
                    dedup_result = None
                    if qualified_scripts:
                        dedup_filter.existing_scripts = qualified_scripts
                        dedup_result = dedup_filter.evaluate(script, {})
                        if not dedup_result.is_ok:
                            status = "❌ DUP"

                    self._report(
                        progress_callback,
                        f"  变体{i}: {status} {copy_result.score:.1f}/10 "
                        f"(hook={copy_result.sub_scores.get('hook_strength',0):.0f} "
                        f"口语={copy_result.sub_scores.get('oral_quality',0):.0f} "
                        f"CTA={copy_result.sub_scores.get('cta_strength',0):.0f})"
                    )
                    # 准入：文案 + 去重双门禁，REJECT/FATAL 一律不放行
                    dedup_ok = (dedup_result is None) or dedup_result.is_ok
                    if copy_result.is_ok and dedup_ok:
                        qualified_scripts.append(script)
                    else:
                        for issue in copy_result.issues:
                            result.warnings.append(f"[文案过滤/变体{i}] {issue}")
                        if dedup_result is not None and not dedup_result.is_ok:
                            result.warnings.append(f"[去重/变体{i}] 与已通过变体相似度过高，已丢弃")
                scripts = qualified_scripts
                if not scripts:
                    raise RuntimeError(
                        "文案质量过滤后无变体通过（全部被门禁拦截），请降低过滤阈值或检查文案质量")
                self._report(
                    progress_callback,
                    f"文案过滤完成: {len(scripts)}/{len(result.scripts)} 通过"
                )

            # ── CreativeScorer CTR 预评分（出片前预估表现）──
            try:
                from adflow.analytics.creative_scorer import CreativeScorer, build_score_summary
                scorer = CreativeScorer(
                    category=product.category, platform=platform)
                creative_scores = scorer.score_batch(scripts)
                if creative_scores:
                    summary = build_score_summary(creative_scores)
                    best = creative_scores[0]
                    self._report(
                        progress_callback,
                        f"创意预评分: 最优变体#{best.variant_index} "
                        f"综合{best.total_score:.1f}/10 "
                        f"预估CTR {best.ctr_estimate*100:.2f}%")
                    result.creative_scores = creative_scores
                    logger.info("CreativeScorer 完成: %d个变体", len(creative_scores))
                    # ── 前3秒预检门禁 ──
                    for script in scripts:
                        try:
                            from adflow.analytics.rule_scorer import HookGate
                            hook_result = HookGate.validate(script)
                            if not hook_result["passed"]:
                                result.warnings.append(
                                    f"⚠ 变体{script.variant_index} 前3秒风险: "
                                    + "; ".join(hook_result["issues"]))
                        except Exception:
                            pass
            except Exception as e:
                logger.debug("CreativeScorer 跳过: %s", e)

            # ---- Phase 3.5: TTS 配音（音色+情绪多样化） ----
            narration_map, segment_timing_map, narration_gender_map, tts = self._synthesize_narration(
                scripts=scripts,
                result=result,
                product=product,
                custom_audio=custom_audio,
                voice_override=voice_override,
                speech_rate_override=speech_rate_override,
                target_duration_ms=target_duration_ms,
                progress_callback=progress_callback,
            )

            # ---- 低质镜头过滤：出片时排除低质（软排除，不删库）----
            excluded_material_ids: set[str] = set()
            if low_quality_rules:
                from adflow.engine.low_quality_filter import classify
                kept_ids, lq_stats = classify(self.material_repo, low_quality_rules)
                all_ids = {m.material_id for m in
                           self.material_repo.get_all(limit=self.material_repo.count() or 1)}
                excluded_material_ids = all_ids - kept_ids
                self._report(progress_callback,
                             f"低质过滤: {lq_stats.get('total', 0)}条素材"
                             f"排除{len(excluded_material_ids)}条，保留{lq_stats.get('kept', 0)}条")

            # ---- Phase 4: 匹配 Agent ----
            self._report(progress_callback, "素材匹配中...")
            timelines = []
            shot_targets_map: dict[str, list] = {}  # script_id → 镜头目标（供 Phase 5 渲染）
            # material_id → 已使用次数：从 DB 永久使用次数读起，任务内再累加（跨任务去重）
            all_used_material_ids: dict[str, int] = self.material_repo.get_used_counts()
            bgm_library = BGMLibrary()
            for i, script in enumerate(scripts):
                self._report(progress_callback, f"  匹配脚本 {i + 1}/{len(scripts)}...")
                # 配音后按时间轴切分镜头（镜头数=配音/镜头时长），role 从口播句加权映射
                shot_targets = self._build_shot_targets(
                    script, segment_timing_map.get(script.script_id))
                shot_targets_map[script.script_id] = shot_targets
                matched_shots, warnings = self.match_agent.match_script(
                    shot_targets, account_id,
                    reserved_material_ids=all_used_material_ids,
                    excluded_material_ids=excluded_material_ids,
                    aspect=aspect_ratio,
                    variant_index=i,
                )
                for w in warnings:
                    result.warnings.append(f"[脚本{i}] {w}")

                if not matched_shots:
                    result.errors.append(f"脚本 {i} 没有匹配到任何素材，跳过")
                    continue

                # 记录本变体使用的素材ID与次数，后续变体按 0>1>2>... 分层竞争
                for shot in matched_shots:
                    if shot.material_id:
                        all_used_material_ids[shot.material_id] = (
                            all_used_material_ids.get(shot.material_id, 0) + 1)

                # ── BGM 选择：审核指定 > 显式传入 > 库内顺序轮换 > 无BGM ──
                bgm_file = ""
                if self._bgm_override:
                    bgm_file = self._bgm_override
                elif bgm_files:
                    bgm_file = bgm_files[i % len(bgm_files)]
                elif config.get("bgm.enabled", True):
                    bgm_file = bgm_library.rotate(i)
                    if bgm_file:
                        self._report(progress_callback,
                                     f"轮换选BGM: {os.path.basename(bgm_file)}")

                timeline = EditTimeline(
                    script_id=script.script_id,
                    shots=matched_shots,
                    bgm_file=bgm_file,
                )
                # 持久化重渲染所需：配音文件 + 分段时长（供出片后编辑重渲染）
                _nar = narration_map.get(script.script_id, "")
                _seg, _pause = [], []
                _timing = segment_timing_map.get(script.script_id)
                if _timing:
                    _seg, _pause = _timing[1], _timing[2]
                timeline.variant_metadata = json.dumps({
                    "narration_file": _nar,
                    "segment_durations": _seg,
                    "pause_durations": _pause,
                }, ensure_ascii=False)
                timeline.timeline_id = self.project_repo.insert_timeline(timeline)
                timelines.append(timeline)

            result.timelines = timelines

            # ── 镜头重复度统计 ──
            all_shot_materials = []
            for t in timelines:
                for s in t.shots:
                    if s.material_id:
                        all_shot_materials.append(s.material_id)
            unique_mats = len(set(all_shot_materials))
            total_shots = len(all_shot_materials)
            mat_total = self.material_repo.count()
            result.repetition_stats = {
                "unique_materials": unique_mats,
                "total_shots": total_shots,
                "rate": round(unique_mats / max(total_shots, 1) * 100, 1),
                "material_total": mat_total,
                "reused": total_shots - unique_mats,
            }
            if total_shots > 0 and unique_mats < total_shots:
                result.warnings.append(
                    f"镜头重复度: {unique_mats}/{total_shots} 唯一 "
                    f"({result.repetition_stats['rate']}%), "
                    f"素材库共{mat_total}个, {total_shots - unique_mats}个被复用")

            # ---- Phase 5: 变体工厂 + 合规审查 ----
            timeline_map = {t.script_id: t for t in timelines}
            all_variants = self._render_variants(
                task=task,
                result=result,
                scripts=scripts,
                timelines=timelines,
                timeline_map=timeline_map,
                narration_map=narration_map,
                segment_timing_map=segment_timing_map,
                narration_gender_map=narration_gender_map,
                shot_targets_map=shot_targets_map,
                variant_count=variant_count,
                bgm_files=bgm_files,
                account_id=account_id,
                platform=platform,
                progress_callback=progress_callback,
                aspect_ratio=aspect_ratio,
            )
            result.variants = all_variants

            # ---- Phase 5.5: 因子快照（产出后自动提取，供后续爆款分析） ----
            try:
                from adflow.analytics.factor_extractor import FactorExtractor
                from adflow.db.analytics_repo import AnalyticsRepo

                _tts_obj = tts
                # 按 variant 反查其对应脚本/时间线（禁止用渲染循环泄漏的末个 script/timeline）
                script_map = {s.script_id: s for s in scripts}
                for variant in all_variants[:1]:  # 首个变体即可，因子大同小异
                    video_path = variant.output_file or ""
                    _v_script = script_map.get(variant.script_id)
                    _v_timeline = timeline_map.get(variant.script_id)
                    if not (video_path and _v_script and _v_timeline):
                        continue
                    if not os.path.exists(video_path):
                        continue
                    factors = FactorExtractor.extract(
                        video_path=video_path,
                        script=_v_script,
                        edit_timeline=_v_timeline,
                        tts_voice=getattr(_tts_obj, 'voice', '') if _tts_obj else '',
                    )
                    # 不关联标注（标注由用户后续手动添加），仅保存快照
                    a_repo = AnalyticsRepo()
                    factors.source_type = "adflow_output"
                    factors.source_task_id = task.task_id
                    a_repo.insert_factors(
                        hit_label_id=None,  # None=AdFlow自动快照,尚未人工标注
                        factors=factors,
                    )
                    self._report(progress_callback,
                                 f"因子快照已保存: {len(factors.to_vector())}维")
            except Exception as e:
                logger.warning(f"因子提取跳过: {e}")

            # ---- Phase 5.9: 项目持久化（参考 video-use project.md）----
            try:
                project_json_path = _save_project_json(
                    task=task, product=product, strategy=result.strategy,
                    scripts=scripts, variants=all_variants,
                )
            except Exception as e:
                logger.warning("项目持久化失败: %s", e)
                project_json_path = ""

            # ---- Phase 5.10: 预算结算 ----
            budget.record_phase("渲染完成")
            budget_record = budget.finish_task()
            if budget_record:
                self._report(progress_callback,
                             f"实际成本: ¥{budget_record.total_cost:.4f} "
                             f"(LLM ¥{budget_record.llm_cost:.4f} + "
                             f"TTS ¥{budget_record.tts_cost:.4f})")

            # ---- Phase 6: 标记任务完成 ----
            self.project_repo.update_task_status(task.task_id, "done")
            result.success = len(all_variants) > 0

        except PipelineCancelled:
            result.cancelled = True
            if result.task_id:
                self.project_repo.update_task_status(result.task_id, "cancelled")
            return result

        except Exception as e:
            import traceback
            tb = traceback.format_exc()
            logger.error("Pipeline异常:\n%s", tb)
            result.errors.append(f"{e}\n{tb[-500:]}")
            if result.task_id:
                self.project_repo.update_task_status(result.task_id, "failed")
            result.success = False

        self._report(progress_callback, result.summary.replace("\n", " | "))
        return result

    def _synthesize_narration(self, scripts, result, product, custom_audio,
                              voice_override, speech_rate_override,
                              target_duration_ms, progress_callback):
        """Phase 3.5: TTS 配音（音色+情绪多样化）

        返回 (narration_map, segment_timing_map, tts)。
        副作用：回写 script.total_duration_ms（以配音为最终时钟）、append result.warnings（配音过滤）。
        """
        narration_map: dict[str, str] = {}  # script_id → narration_mp3_path
        segment_timing_map: dict[str, tuple[list[str], list[int], list[int]]] = {}
        narration_gender_map: dict[str, str] = {}  # script_id → "female"|"male"|""
        tts = None

        if custom_audio and os.path.exists(custom_audio):
            # ── 使用用户上传的配音（爆款原声）──
            # 字幕 0 延迟：静音检测出 N 个语音段 → 文案断成恰好 N 句 1:1 映射，
            # 字幕文本=用户原文（不错字），时间戳=真实语音段起点（零漂移）
            self._report(progress_callback, "使用自定义配音...")
            from adflow.engine.subtitle_renderer import (
                detect_speech_segments, refine_speech_segments, split_text_to_n)
            from adflow.engine.resynth import collect_narration_segments
            speech = refine_speech_segments(detect_speech_segments(
                custom_audio, silence_threshold=-30, min_silence=0.2))
            for script in scripts:
                narration_map[script.script_id] = custom_audio
                # 收集字幕文案（与 _build_subtitles 同源）
                all_segments, _ = collect_narration_segments(script)
                full_text = "".join(all_segments)
                if speech and full_text:
                    texts = split_text_to_n(full_text, len(speech))
                    seg_durs = []
                    pause_durs = []
                    for i, (s_start, s_end) in enumerate(speech):
                        pause = 0
                        if i < len(speech) - 1:
                            pause = speech[i + 1][0] - s_end
                        seg_durs.append(s_end - s_start + pause)
                        pause_durs.append(pause)
                    segment_timing_map[script.script_id] = (
                        texts, seg_durs, pause_durs)
                    self._subtitle_align_map[script.script_id] = (texts, speech)
                    self._report(progress_callback,
                                 f"自定义配音: 语音段对齐 {len(texts)}段（字幕=原文+真实停顿）")
                else:
                    # 回退：平均分配（无语音段或无文案）
                    try:
                        from moviepy import AudioFileClip
                        ac = AudioFileClip(custom_audio)
                        audio_ms = int(ac.duration * 1000)
                        ac.close()
                    except Exception:
                        audio_ms = target_duration_ms
                    dur_per = max(500, audio_ms // max(len(all_segments), 1))
                    seg_durs = [dur_per] * len(all_segments)
                    segment_timing_map[script.script_id] = (
                        all_segments, seg_durs, [0] * len(seg_durs))
                    self._report(progress_callback, "自定义配音: 未检出语音段，回退平均分配")

        # ── 正常 TTS ──
        try:
            self._report(progress_callback, "AI 配音合成中...")
            tts_cfg = config.tts_config or {}
            emotion_cfg = tts_cfg.get("emotion", {})
            auto_emotion = emotion_cfg.get("auto_detect", True)
            voice_div_cfg = tts_cfg.get("voice_diversity", {})
            _backend = tts_cfg.get("backend", "volcano")

            # 创建引擎（数字人性别锁定 > 用户指定音色 > 音色多样性轮换 > 默认音色）
            lock_gender = ""
            if self._digital_human and self._digital_human != "auto":
                from adflow.engine.digital_human import get_digital_human
                _dh = get_digital_human(self._digital_human)
                if _dh:
                    lock_gender = _dh.gender  # 固定性别数字人：女脸配女声

            tts_voice = voice_override or ""
            if lock_gender and tts_voice:
                logger.warning("[数字人] 已选固定性别数字人(%s)，忽略手动音色 %s",
                               lock_gender, tts_voice)
                tts_voice = ""
            if tts_voice:
                tts = create_tts_engine(voice=tts_voice)
            elif voice_div_cfg.get("enabled", True) or lock_gender:
                # 音色多样性：按后端创建 VoicePool，多脚本自动轮换音色
                from adflow.engine.tts_engine import (
                    VoicePool, get_voice_dict_for_backend)
                strategy = ("round_robin" if lock_gender
                            else voice_div_cfg.get("strategy", "round_robin"))
                gender = lock_gender or voice_div_cfg.get("gender", "any")
                pool = VoicePool(
                    strategy=strategy,
                    gender=gender,
                    voice_dict=get_voice_dict_for_backend(_backend))
                tts = create_tts_engine(voice_pool=pool)
            else:
                tts = create_tts_engine(
                    voice=tts_cfg.get("voice", "BV001_streaming"))

            voice_used = []
            for script in scripts:
                if script.script_id in narration_map:
                    continue  # custom_audio 已填配音，跳过 TTS 合成
                from adflow.engine.resynth import collect_narration_segments
                all_segments, segment_roles = collect_narration_segments(script)

                if all_segments:
                    out_path = os.path.join(
                        config.output_dir, "_narration",
                        f"{script.script_id}.mp3",
                    )
                    emotion = ""
                    full_text = "".join(all_segments)
                    if auto_emotion:
                        emotion = detect_emotion(full_text)
                        if emotion == "中性":
                            emotion = emotion_cfg.get("default", "中性")

                    # ── 分段合成: 逐段TTS → FFmpeg拼接 → 精确时间戳（零漂移）──
                    seg_durs = []
                    pause_durs = []
                    try:
                        mp3_path, seg_durs, pause_durs = tts.synthesize_segments(
                            all_segments, out_path, emotion=emotion,
                            # 审核弹窗选了固定停顿则用固定值，None=引擎按角色动态
                            pause_ms=self._pause_ms_override,
                            segment_roles=segment_roles,
                            speech_rate=speech_rate_override)
                        narration_map[script.script_id] = mp3_path
                        drift_total = sum(seg_durs)
                        self._report(progress_callback,
                                     f"分段合成: {len(all_segments)}段, "
                                     f"总时长{drift_total}ms (零漂移)")
                    except Exception as e:
                        logger.warning("分段合成失败: %s, 回退全文合成", e)
                        mp3_path = tts.synthesize(full_text, out_path, emotion=emotion)
                        narration_map[script.script_id] = mp3_path
                        # 回退: 静音检测对齐（音波「静音-语音-静音」），段数不匹配才字数估算
                        try:
                            from adflow.engine.subtitle_renderer import detect_speech_segments
                            speech = detect_speech_segments(mp3_path)
                        except Exception:
                            speech = []
                        if speech and len(speech) == len(all_segments):
                            seg_durs = []
                            pause_durs = []
                            for i, (s_start, s_end) in enumerate(speech):
                                dur = s_end - s_start
                                pause = (speech[i + 1][0] - s_end
                                         if i < len(speech) - 1 else 0)
                                seg_durs.append(dur + pause)
                                pause_durs.append(pause)
                        else:
                            # 静音段数不匹配，回退字数估算
                            total = sum(len(s) for s in all_segments)
                            try:
                                from moviepy import AudioFileClip
                                nac = AudioFileClip(mp3_path)
                                audio_ms = int(nac.duration * 1000)
                                nac.close()
                                seg_durs = [max(int(len(s)/max(total,1)*audio_ms), 300)
                                            for s in all_segments]
                            except Exception:
                                seg_durs = [max(len(s)*200, 500) for s in all_segments]
                            pause_durs = [0] * len(seg_durs)

                    segment_timing_map[script.script_id] = (all_segments, seg_durs, pause_durs)

                    info = f"{tts.current_voice_name}"
                    if emotion and emotion != "中性":
                        info += f"({emotion})"
                    voice_used.append(info)
                    from adflow.engine.tts_engine import resolve_voice_gender
                    narration_gender_map[script.script_id] = \
                        resolve_voice_gender(getattr(tts, 'voice', ''), _backend)
                    tts.next_voice()

            voice_summary = " → ".join(voice_used) if voice_used else "无"
            self._report(progress_callback,
                         f"配音完成: {len(narration_map)} 脚本 "
                         f"[{tts.backend_name}] | 音色: {voice_summary}")

            # ── 以配音为最终时钟 ──
            from adflow.engine.smart_duration import fit_to_narration
            for script in scripts:
                if script.script_id in narration_map:
                    try:
                        from moviepy import AudioFileClip
                        ac = AudioFileClip(narration_map[script.script_id])
                        nar_ms = int(ac.duration * 1000)
                        ac.close()
                        final_ms = fit_to_narration(
                            nar_ms, target_duration_ms, is_suggestion=True)
                        if final_ms != script.total_duration_ms:
                            self._report(progress_callback,
                                         f"时长: 配音{nar_ms/1000:.1f}秒, "
                                         f"最终{final_ms/1000:.0f}秒 "
                                         f"(30秒黄金线参考)")
                            script.total_duration_ms = final_ms
                    except Exception:
                        pass

            # ── 配音过滤 ──
            if self.filter_enabled and narration_map:
                tts_filter_results = []
                for script in scripts:
                    if script.script_id in narration_map:
                        audio_path = narration_map[script.script_id]
                        tts_ctx = {
                            "voice_name": getattr(tts, 'current_voice_name', ''),
                            "category": product.category,
                            "alignment_method": "segment_tts",
                        }
                        tts_result = self.tts_filter.evaluate(
                            (audio_path, script), tts_ctx)
                        tts_filter_results.append(
                            (script.script_id, tts_result))
                        if not tts_result.is_ok:
                            for issue in tts_result.issues:
                                result.warnings.append(
                                    f"[配音过滤] {issue}")
                if tts_filter_results:
                    avg_score = sum(r.score for _, r in tts_filter_results) / len(tts_filter_results)
                    self._report(progress_callback,
                                 f"配音过滤完成: 均分{avg_score:.1f}/10")

        except Exception as e:
            # 配音失败 = 任务失败，不产出无配音视频（文案决定配音，配音是硬依赖）
            raise RuntimeError(f"配音失败: {e}") from e

        return narration_map, segment_timing_map, narration_gender_map, tts

    def _render_variants(self, task, result, scripts, timelines, timeline_map,
                         narration_map, segment_timing_map, narration_gender_map,
                         shot_targets_map,
                         variant_count, bgm_files, account_id, platform,
                         progress_callback, aspect_ratio="portrait"):
        """Phase 5: 变体工厂 + 合规审查 → 返回 all_variants（副作用：append result.warnings）"""
        self._report(progress_callback, "渲染变体视频...")
        all_variants = []

        if len(timelines) < len(scripts):
            result.warnings.append(
                f"时间线不足: {len(scripts)}脚本但仅{len(timelines)}条时间线，"
                f"匹配失败的脚本将被跳过")
        for i, script in enumerate(scripts):
            timeline = timeline_map.get(script.script_id)
            if timeline is None:
                continue
            self._report(progress_callback, f"  渲染变体组 {i + 1}/{len(scripts)}...")

            # 生成变体组合
            hook_materials = []
            for shot in timeline.shots:
                if shot.shot_index == 0:  # 钩子镜头
                    mat = self.material_repo.get_by_id(shot.material_id)
                    if mat:
                        hook_materials.append(mat)
                    break

            variant_configs = self.variant_factory.generate_combinations(
                hook_materials=hook_materials,
                bgm_files=bgm_files or [],
                max_variants=variant_count,  # 按用户设定的变体数
            )

            # 如果没有变体配置，至少生成一个默认变体
            if not variant_configs:
                variant_configs = [VariantConfig(variant_index=0)]

            # 数字人画中画：逐 script 生成一次，多变体复用（失败降级为无数字人）
            dh_video = self._resolve_digital_human_video(
                script=script,
                narration_file=narration_map.get(script.script_id, ""),
                narration_gender=narration_gender_map.get(script.script_id, ""),
                result=result,
            )

            # 渲染
            ad_variants = self.variant_factory.produce(
                script=script,
                base_timeline=timeline,
                variants=variant_configs,
                task_id=task.task_id,
                account_id=account_id,
                narration_file=narration_map.get(script.script_id, ""),
                segment_durations=segment_timing_map.get(script.script_id, ([], [], []))[1],
                pause_durations=segment_timing_map.get(script.script_id, ([], [], []))[2],
                shot_targets=shot_targets_map.get(script.script_id),
                digital_human_video=dh_video,
                aspect_ratio=aspect_ratio,
                subtitle_alignment=self._subtitle_align_map.get(script.script_id),
            )

            # 合规审查
            for av in ad_variants:
                # 检查所有字幕和 CTA
                texts = {}
                for j, shot in enumerate(script.shots):
                    texts[f"shot_{j}_narration"] = shot.narration_text
                texts["cta"] = script.cta_text

                cr = self.checker.check_multiple(texts, platform)
                av.compliance_check_passed = cr.passed
                if not cr.passed:
                    av.status = "rejected"
                    for v in cr.violations:
                        result.warnings.append(
                            f"违规: [{v.get('category', '')}] {v.get('word', '')}"
                        )

                # 保存变体到数据库
                av.variant_id = self.project_repo.insert_variant(av)
                all_variants.append(av)

        return all_variants

    def _resolve_digital_human_video(self, script, narration_file,
                                     narration_gender, result) -> str:
        """选数字人形象 + 生成对口型视频；失败返回空串（降级为无数字人，仅告警）。

        digital_human 三态：
          ""           → 不选（全链路 no-op）
          "auto"       → 按配音性别选默认形象（女配女/男配男，性别未知跳过）
          具体 avatar_id → 锁定形象（配音阶段已锁定性别）
        """
        if not self._digital_human or not narration_file:
            return ""
        from adflow.engine.digital_human import (
            get_digital_human, avatars_for_gender, generate_talking_video)
        if self._digital_human == "auto":
            candidates = avatars_for_gender(narration_gender)
            if not candidates:
                result.warnings.append(
                    f"[数字人] 脚本 {script.script_id} 配音性别 "
                    f"'{narration_gender or '未知'}' 无可用形象，跳过画中画")
                return ""
            # 同性别多形象轮换：按性别记已用数，逐脚本取下一个，不总用第一个
            idx = self._dh_auto_index.get(narration_gender, 0) % len(candidates)
            avatar = candidates[idx]
            self._dh_auto_index[narration_gender] = idx + 1
        else:
            avatar = get_digital_human(self._digital_human)
            if avatar is None:
                result.warnings.append(
                    f"[数字人] 未知形象 '{self._digital_human}'，脚本 {script.script_id} 跳过画中画")
                return ""
        narration_key = os.path.splitext(os.path.basename(narration_file))[0]
        out = os.path.join(
            config.output_dir, "_digital_human",
            f"{narration_key}_{avatar.avatar_id}.mp4")
        video = generate_talking_video(avatar.image_path, narration_file, out)
        if not video:
            result.warnings.append(
                f"[数字人] 生成失败（形象 {avatar.avatar_id}），脚本 {script.script_id} 降级为无画中画")
        return video

    def _report(self, callback, msg: str) -> None:
        """进度报告（阶段边界检查协作式取消）"""
        if self._should_cancel and self._should_cancel():
            raise PipelineCancelled()
        if callback:
            callback(msg)
        else:
            logger.info(f"[Pipeline] {msg}")

    def _build_shot_targets(self, script, timing) -> list:
        """配音后按时间轴切分镜头：镜头数=配音/镜头时长，role 用「切片内占时长最多的口播句」加权映射

        口播句（script.shots）完整保留（供字幕），这里只生成「画面镜头目标」。
        """
        if not timing:
            return list(script.shots)
        _all_segments, seg_durs, _pause_durs = timing
        if not seg_durs:
            return list(script.shots)

        shot_dur = self._shot_dur_override or config.get("editing.shot_duration_ms", 2500)
        nar_ms = sum(seg_durs)
        n = max(1, round(nar_ms / shot_dur))

        # 每段口播的时间区间（含停顿）
        seg_ranges = []
        t = 0
        for dur in seg_durs:
            seg_ranges.append((t, t + dur))
            t += dur

        # 段 → shot 归属
        from adflow.engine.resynth import collect_segment_shot_indices
        seg_shot = collect_segment_shot_indices(script)

        targets = []
        for i in range(n):
            start = i * shot_dur
            end = min((i + 1) * shot_dur, nar_ms)
            src = script.shots[AdPipeline._dominant_shot(start, end, seg_ranges, seg_shot)]
            targets.append(StoryboardShot(
                shot_index=i,
                role=src.role,
                required_scene=src.required_scene,
                required_emotion=src.required_emotion,
                required_product_visibility=src.required_product_visibility,
                duration_ms=end - start,
                narration_text=src.narration_text,
            ))
        return targets

    @staticmethod
    def _dominant_shot(start: int, end: int, seg_ranges: list,
                       seg_shot: list) -> int:
        """切片 [start, end] 内占时长最多的口播段所属 shot 索引"""
        shot_time: dict[int, int] = {}
        for i, (s, e) in enumerate(seg_ranges):
            overlap = min(e, end) - max(s, start)
            if overlap > 0:
                si = seg_shot[i] if i < len(seg_shot) else 0
                shot_time[si] = shot_time.get(si, 0) + overlap
        if not shot_time:
            return 0
        return max(shot_time, key=shot_time.get)




# ═══════════════════════════════════════
# 项目持久化 — project.json（参考 video-use project.md）
# ═══════════════════════════════════════

def _save_project_json(task, product, strategy, scripts, variants) -> str:
    """保存完整项目状态到 project.json

    包含: 任务参数、产品、策略、脚本、变体清单、过滤结果、
          素材使用记录 → 支持跨会话恢复和审计
    """
    output_dir = config.output_dir
    task_subdir = os.path.join(output_dir, datetime.now().strftime("%m%d"),
                               task.task_id[:8] if task.task_id else "unknown")
    os.makedirs(task_subdir, exist_ok=True)

    project = {
        "version": "1.0",
        "generated_at": datetime.now().isoformat(),
        "task": {
            "task_id": task.task_id,
            "product_id": task.product_id,
            "platform": task.platform,
            "account_id": task.account_id,
            "target_duration_ms": task.target_duration_ms,
            "variant_count": task.variant_count,
            "status": task.status,
            "created_at": task.created_at,
        },
        "product": {
            "name": product.name,
            "category": product.category,
            "key_selling_points": product.key_selling_points,
            "target_audience": product.target_audience,
            "pain_points": product.pain_points,
            "brand_tone": product.brand_tone,
        },
        "strategy": {
            "strategy_id": strategy.strategy_id,
            "narrative_type": strategy.narrative_type,
            "hook_type": strategy.hook_type,
            "pace_style": strategy.pace_style,
            "tone": strategy.tone,
            "key_message": strategy.key_message,
            "target_emotion": strategy.target_emotion,
        },
        "scripts": [],
        "variants": [],
    }

    # 脚本摘要
    for script in scripts:
        script_entry = {
            "script_id": script.script_id,
            "variant_index": script.variant_index,
            "cta_text": script.cta_text,
            "total_duration_ms": script.total_duration_ms,
            "shot_count": len(script.shots),
            "narration_preview": "".join(
                s.narration_text or "" for s in script.shots)[:100],
        }
        project["scripts"].append(script_entry)

    # 变体清单
    for variant in variants:
        variant_entry = {
            "variant_id": variant.variant_id,
            "script_id": variant.script_id,
            "output_file": variant.output_file,
            "edl_file": variant.output_file.replace(".mp4", "_edl.json")
            if variant.output_file else "",
            "status": variant.status,
            "compliance_passed": variant.compliance_check_passed,
            "created_at": variant.created_at,
        }
        project["variants"].append(variant_entry)

    # 写入文件
    project_path = os.path.join(task_subdir, "project.json")
    with open(project_path, "w", encoding="utf-8") as f:
        json.dump(project, f, ensure_ascii=False, indent=2)

    logger.info("项目状态已保存: %s", project_path)
    return project_path
