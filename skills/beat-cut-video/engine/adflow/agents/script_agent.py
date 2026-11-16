"""
脚本 Agent — 创意策略 → 分镜脚本
- 根据策略生成多个变体分镜脚本
- 每个变体在 hook 素材和旁白文案上有差异
- 输出 list[StoryboardScript]
"""

import json
from pathlib import Path
from datetime import datetime

from adflow.agents.base_agent import BaseAgent, cloud_unavailable
from adflow.models import (
    CreativeStrategy, ProductProfile, StoryboardScript, StoryboardShot,
)


class ScriptAgent:
    """分镜脚本 Agent"""

    def __init__(self, model: str | None = None):
        # 支持 LoRA adapter: 仅在 copy_optimization.lora_enabled 时才切换模型
        # （llm.local.enabled 现在是"云端失败兜底本地"语义，两者不能混用）
        if model is None:
            try:
                from adflow.config_loader import config
                copy_cfg = config.get("copy_optimization", {}) or {}
                if copy_cfg.get("lora_enabled", False):
                    from adflow.trainer.model_manager import get_model_manager
                    manager = get_model_manager()
                    model = manager.get_model_for_task()
            except Exception:
                pass
        self.agent = BaseAgent(model=model, temperature=0.75, max_tokens=16384, task="script")  # 5变体×10镜头×8字段，本地模型输出更长
        self._system_prompt = self._load_prompt()

    def generate(
        self,
        strategy: CreativeStrategy,
        product: ProductProfile,
        target_duration_ms: int = 30000,
        variant_count: int = 5,
        platform: str = "ocean_engine",
        selected_angles: list[dict] | None = None,
    ) -> list[StoryboardScript]:
        """
        生成分镜脚本
        - strategy: 创意策略
        - product: 产品信息
        - target_duration_ms: 目标视频时长
        - variant_count: 生成几个变体
        - platform: 投放平台
        """
        # 本地兜底（云端已确认不可用 / 已降级本地 / 云端 key 未配置）时把变体数降到 1：
        # 本地弱模型（8b）生成多变体 JSON 既慢又不稳定（多变体易崩成 Markdown/空字段）；云端正常保留 variant_count
        if (cloud_unavailable()
                or getattr(self.agent, '_used_local_fallback', False)
                or not getattr(self.agent, 'api_key', '')):
            variant_count = 1
        user_msg = self._build_user_message(
            strategy, product, target_duration_ms, variant_count, platform,
            selected_angles=selected_angles,
        )

        # 定义 shot schema
        shot_schema = {
            "type": "object",
            "properties": {
                "role": {"type": "string"},
                "duration_ms": {"type": "integer"},
                "description": {"type": "string"},
                "narration_text": {
                    "type": "string",
                    "description": "旁白完整文案，必须带标点（逗号/句号按呼吸节奏断句）",
                },
                "narration_segments": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": "旁白按口语短句分段，每段8-20字，一个完整呼吸单元（必填）",
                },
                "required_scene": {"type": "string"},
                "required_emotion": {"type": "string"},
                "required_product_visibility": {"type": "string"},
            },
            "required": ["role", "duration_ms", "description", "narration_segments"],
        }

        schema = {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "variant_index": {"type": "integer"},
                    "cta_text": {"type": "string"},
                    "shots": {"type": "array", "items": shot_schema},
                },
                "required": ["variant_index", "cta_text", "shots"],
            },
        }

        try:
            result = self.agent.call_structured(
                system_prompt=self._system_prompt,
                user_message=user_msg,
                output_schema=schema,
                temperature=0.8,
            )
            scripts = self._parse_scripts(result)
        except Exception as e:
            import logging
            logging.getLogger("adflow.script").warning(
                "脚本生成 JSON 解析失败: %s", e)
            scripts = []

        # 本地兜底模型弱，降级后只保留 1 变体（多变体 JSON 不稳定、质量被稀释）
        if getattr(self.agent, '_used_local_fallback', False) and len(scripts) > 1:
            scripts = scripts[:1]

        # ── 多样性竞价算法：结构签名 + 竞价评分 + 定向重试 ──
        from adflow.engine.diversity_scorer import DiversityScorer
        scorer = DiversityScorer(category=product.category or "通用")
        # 实际已降级本地时减少重试（本地模型慢且不稳定），云端保持 3 次
        max_retries = 1 if getattr(self.agent, '_used_local_fallback', False) else 3
        for retry in range(max_retries):
            result = scorer.score_batch(scripts)
            if result["passed"]:
                scorer.add_to_history(scripts)
                break
            import logging
            logger = logging.getLogger("adflow.script")
            logger.warning(
                "%d/%d 多样性不足(评分%.0f) → 定向重试",
                retry + 1, max_retries, result["score"])
            feedback = (
                "## ❌ 上一轮5个变体太像了！这次必须写出不同的感觉：\n\n"
                "**问题**：每个变体用了几乎一样的句子、一样的节奏——只换关键词，像同一篇的换词版。\n\n"
                "**要求**：\n"
                "1. 同一套爆款风格可以共用，但说法、字眼、节奏要有变化\n"
                "   比如'我其实是一个挺爱吃零食的人'可以换成：\n"
                "   '我这个人嘴巴比较刁' / '说真的我对零食要求挺高' /\n"
                "   '你们看我囤了多少零食就知道了' / '能入我眼的不多'\n"
                "2. 每个变体针对不同人群，语气要不同：\n"
                "   便秘→肠道健康，控糖→血糖友好，白领→方便便携，健身→营养补充\n"
                "3. 句子长短要有变化，至少3个变体换开场节奏——不要都是'我...但是我...'\n"
                "4. 学爆款的表达方式，但不要每个变体用同样的句子模板\n"
            )
            try:
                result_raw = self.agent.call_structured(
                    system_prompt=self._system_prompt + "\n\n" + feedback,
                    user_message=user_msg,
                    output_schema=schema,
                    temperature=1.0 + retry * 0.1,
                )
                scripts = self._parse_scripts(result_raw)
            except Exception as e:
                logger.warning("多样性重试 JSON 解析失败: %s，保留旧脚本", e)
                break

        # ── 质量自检+自动重写 ──
        from adflow.filters.copy_filter import CopyFilter
        quality_checker = CopyFilter()
        # 本地弱模型（8b）重写不会更好反而更差，降级后跳过质量自检重写
        q_retries = 0 if getattr(self.agent, '_used_local_fallback', False) else 2
        for q_retry in range(q_retries):
            low_scripts = []
            for script in scripts:
                score = quality_checker.evaluate(script, {}).score
                if score < 5.5:
                    low_scripts.append(script)
            if not low_scripts:
                break
            import logging
            logger = logging.getLogger("adflow.script")
            logger.warning(
                "质量自检: %d/%d个变体低于5.5分 → 自动重写",
                len(low_scripts), len(scripts))
            # 带字数+场景化反馈重写
            feedback = (
                f"上一次{len(low_scripts)}个变体质量不达标(低于5.5分)。"
                f"主要问题: 文案太短(需要120-150字)、缺乏场景化描述、情绪平淡。"
                f"请每个镜头写满'场景→使用→效果'三件套，情绪要有起伏。"
            )
            try:
                result_raw = self.agent.call_structured(
                    system_prompt=self._system_prompt
                    + f"\n\n## ⚠️ 质量反馈\n{feedback}",
                    user_message=user_msg,
                    output_schema=schema,
                    temperature=0.9,
                )
                scripts = self._parse_scripts(result_raw)
            except Exception as e:
                logger.warning("质量重写 JSON 解析失败: %s，保留旧脚本", e)
                break

        # 本地弱模型（8b）面对多变体易崩成非 JSON（scripts 为空）；
        # 已降级本地时用 1 变体重试一次（8b 在 1 变体下能稳定输出结构）
        if (not scripts
                and getattr(self.agent, '_used_local_fallback', False)
                and variant_count > 1):
            import logging
            logging.getLogger("adflow.script").warning(
                "本地弱模型多变体输出为空，降为 1 变体重试")
            user_msg_1 = self._build_user_message(
                strategy, product, target_duration_ms, 1, platform,
                selected_angles=selected_angles)
            try:
                result_raw = self.agent.call_structured(
                    system_prompt=self._system_prompt,
                    user_message=user_msg_1,
                    output_schema=schema,
                    temperature=0.8,
                )
                scripts = self._parse_scripts(result_raw)
            except Exception as e:
                logging.getLogger("adflow.script").warning(
                    "1 变体重试仍失败: %s", e)
                scripts = []

        if not scripts:
            raise RuntimeError(
                "LLM 未返回有效脚本（口播文案为空），请检查云端/本地模型输出质量")
        return scripts[:variant_count]

    def _parse_scripts(self, result) -> list[StoryboardScript]:
        """解析LLM返回的脚本列表。

        云端 qwen-max 严格遵循 schema（[{"variant_index","shots"}...]），
        本地弱模型（8b）常输出 {"product":..., "script":[...]} 或直接输出 shot 数组，
        这里先做结构归一化再解析。
        """
        result = self._normalize_result(result)
        if not isinstance(result, list):
            return []
        scripts = []
        for variant_data in result:
            if not isinstance(variant_data, dict):
                if isinstance(variant_data, str):
                    import logging
                    logging.getLogger("adflow.script").warning(
                        "LLM返回字符串而非对象，跳过: %s", variant_data[:50])
                continue
            shots = []
            for s in variant_data.get("shots", []):
                if not isinstance(s, dict):
                    continue
                narration_text = s.get("narration_text", "") or ""
                segments = s.get("narration_segments", [])
                if isinstance(segments, str):
                    segments = [segments]
                # 旁白兜底：narration_text 空时从分段拼接
                if not narration_text:
                    narration_text = "".join(segments)
                # 过滤纯 schema 空壳（无旁白也无描述）
                if not narration_text and not s.get("description"):
                    continue
                shots.append(StoryboardShot(
                    shot_index=len(shots),
                    role=s.get("role", "b_roll"),
                    duration_ms=s.get("duration_ms", 3000),
                    description=s.get("description", ""),
                    narration_text=narration_text,
                    narration_segments=json.dumps(segments, ensure_ascii=False),
                    required_scene=s.get("required_scene", ""),
                    required_emotion=s.get("required_emotion", ""),
                    required_product_visibility=s.get("required_product_visibility", ""),
                ))

            if not shots:
                continue  # 该变体无可用的镜头（如纯 schema 空壳），跳过

            total_dur = sum(s.duration_ms for s in shots)

            scripts.append(StoryboardScript(
                task_id="",
                strategy_id="",
                shots=shots,
                cta_text=variant_data.get("cta_text", ""),
                total_duration_ms=total_dur,
                variant_index=variant_data.get("variant_index", 0),
                created_at=datetime.now().isoformat(),
            ))

        return scripts

    @staticmethod
    def _normalize_result(result):
        """把弱模型的结构偏差归一化成 [variant, ...] 列表。

        云端严格遵循 schema，本地 8b 常输出：
        - {"product":..., "script":[...]} 单对象包裹
        - 直接输出 shot 数组（无 variant 外壳）
        """
        # 1. 单对象包裹：{"script":[...]} / {"shots":[...]} / {"variants":[...]}
        #    8b 还常把 schema 外壳带出来：{"type":"array","items":[...]}
        if isinstance(result, dict):
            for key in ("shots", "script", "variants", "items"):
                inner = result.get(key)
                if isinstance(inner, list):
                    result = inner
                    break
            else:
                result = [result]
        if not isinstance(result, list):
            return []
        # 2. 直接输出 shot 数组（无 variant 外壳）：整个列表当一个变体
        if result and all(isinstance(x, dict) and "shots" not in x for x in result):
            return [{"variant_index": 0, "cta_text": "", "shots": result}]
        return result

    def _build_user_message(
        self,
        strategy: CreativeStrategy,
        product: ProductProfile,
        target_duration_ms: int,
        variant_count: int,
        platform: str,
        selected_angles: list[dict] | None = None,
    ) -> str:
        target_sec = target_duration_ms / 1000

        # 变体角度分配：优先用传入的 selected_angles
        if selected_angles:
            variant_hooks = []
            for i, a in enumerate(selected_angles):
                variant_hooks.append(
                    f"变体{i}: 卖点=[{a['selling_point']}] x 人群=[{a['audience']}] "
                    f"— 严格围绕这个组合写，不要用其他变体的卖点或人群")
        else:
            # 优先消费策略层的差异化意图（strategy_agent 生成的 differentiation_hints）；
            # 无则回退硬编码角度提示
            hints = self._parse_diff_hints(strategy)
            if hints:
                variant_hooks = [
                    f"变体{i}: {hint}" for i, hint in enumerate(hints[:variant_count])
                ]
            else:
                variant_hooks = [
                    '变体0: 从产品优势切入',
                    '变体1: 完全换人群/场景——变体0写过的词一个都不要用',
                    '变体2: 完全换需求/对比——变体0和1用过的词全部禁止',
                    '变体3: 再次换角度——和前面3个完全不同',
                    '变体4: 最后一个角度——必须和前面4个没有重叠词',
                ]
        diff_hints = "\n".join(variant_hooks[:variant_count])

        # ── 文案框架注入 ──
        framework_context = ""
        try:
            from adflow.agents.prompts.copy_frameworks import build_framework_prompt_context
            framework_context = build_framework_prompt_context(
                hook_type=strategy.hook_type,
                category=product.category,
                max_count=3,
            )
        except Exception:
            pass

        framework_section = f"\n\n{framework_context}" if framework_context else ""

        # ── 卖点翻译预处理 ──
        translated_ctx = ""
        try:
            from adflow.agents.selling_point_translator import SellingPointTranslator
            raw_points = json.loads(product.key_selling_points) if product.key_selling_points else []
            if isinstance(raw_points, str):
                raw_points = [raw_points]
            if raw_points:
                translated = SellingPointTranslator.translate(
                    raw_points, product.category)
                translated_ctx = SellingPointTranslator.build_context(translated)
        except Exception:
            pass

        translated_section = f"\n\n{translated_ctx}" if translated_ctx else ""

        # ── 俗套拒绝注入 ──
        stock_refused_context = ""
        try:
            signals = json.loads(strategy.source_signals) if strategy.source_signals else {}
            stock_refused = signals.get("stock_refused", "")
            if stock_refused:
                stock_refused_context = f"""
## ⚠️ 本次明确不用的俗套（来自策略Agent）
{stock_refused}

请用具体的替代方案，不要复用被拒绝的套路。
"""
        except Exception:
            pass

        # ── 分镜连续性感知 ──
        continuity_hint = ""
        try:
            from adflow.engine.continuity_awareness import ContinuityAwareness
            continuity_hint = ContinuityAwareness.build_context(
                shot_count=variant_count, pace_style=strategy.pace_style)
        except Exception:
            pass
        continuity_section = f"\n\n{continuity_hint}" if continuity_hint else ""

        # ── 平台风格注入 ──
        platform_style_context = ""
        try:
            from adflow.engine.platform_style import PlatformStyle
            platform_style_context = PlatformStyle.build_prompt_context(platform)
        except Exception:
            pass
        platform_section = f"\n\n{platform_style_context}" if platform_style_context else ""

        return f"""## 策略方向
- 风格: {strategy.tone} | 节奏: {strategy.pace_style}
- 情绪: {getattr(strategy, 'emotion_arc', strategy.target_emotion)}
- 角度: {getattr(strategy, 'specific_angle', '') or strategy.key_message}
- 场景: {getattr(strategy, 'target_scenario', '') or ''}

## 产品信息（种子池）
- 名称: {product.name}（固定）
- 优势: {product.key_selling_points}
- 人群/场景: {product.target_audience or '不限'}
- 参考文案: {product.pain_points or '无'} ← 重点学它的写法

> 种子池用来扩散，不是限制。除了产品名/产地/折扣不能改，其他自由发挥。优先学参考文案的风格。

## 要求
- 平台: {platform} 竖屏短视频
- 时长: ~{target_sec:.0f}秒
- 变体: {variant_count}个，不同角度
- 文案口语化，像真人说话
- 每个镜头narration_text 15-40字，描写完整
{diff_hints}

请输出 {variant_count} 个分镜脚本变体。每个变体从完全不同的卖点/场景/人群切入。
""" + translated_section + framework_section + stock_refused_context + continuity_section + platform_section

    @staticmethod
    def _parse_diff_hints(strategy) -> list[str]:
        """解析策略层的变体差异化提示（differentiation_hints 为 JSON 数组字符串）"""
        raw = getattr(strategy, 'differentiation_hints', '')
        if not raw:
            return []
        try:
            hints = json.loads(raw)
            if isinstance(hints, list):
                return [h for h in hints if isinstance(h, str) and h.strip()]
        except (json.JSONDecodeError, TypeError):
            return []
        return []

    @staticmethod
    def _load_prompt() -> str:
        # 支持 prompt 版本切换（config.yaml: copy_optimization.prompt_version）
        try:
            from adflow.config_loader import config
            copy_cfg = config.get("copy_optimization", {}) or {}
            version = copy_cfg.get("prompt_version", "v1")
        except Exception:
            version = "v1"

        if version == "v2":
            prompt_file = "script_prompt_v2.txt"
        else:
            prompt_file = "script_prompt.txt"

        prompt_path = Path(__file__).parent / "prompts" / prompt_file
        if not prompt_path.exists():
            prompt_path = Path(__file__).parent / "prompts" / "script_prompt.txt"
        with open(prompt_path, "r", encoding="utf-8") as f:
            prompt = f.read()

        # ── 注入屏蔽词 ──
        try:
            from adflow.gui.blocked_words_panel import load_blocked_words_context
            blocked_ctx = load_blocked_words_context()
            if blocked_ctx:
                prompt += "\n\n" + blocked_ctx
        except Exception:
            pass

        return prompt
