"""
策略 Agent — 产品信息 → 创意策略
- 分析产品、平台、目标人群
- 可选：参考历史投放数据优化策略
- 输出 CreativeStrategy
"""

import json
from pathlib import Path
from datetime import datetime

from adflow.agents.base_agent import BaseAgent
from adflow.models import CreativeStrategy, ProductProfile


class StrategyAgent:
    """创意策略 Agent"""

    def __init__(self, model: str | None = None):
        self.agent = BaseAgent(model=model, temperature=0.7, task="strategy")
        self._system_prompt = self._load_prompt()

    def generate(
        self,
        product: ProductProfile,
        platform: str = "ocean_engine",
        recent_performance: dict | None = None,
        iteration_round: int = 0,
        style_context: str = "",
    ) -> CreativeStrategy:
        """
        生成创意策略
        - product: 产品信息
        - platform: 投放平台
        - recent_performance: 近7天表现数据（可选）
        - iteration_round: 当前第几轮优化
        - style_context: 选中的风格规则+案例上下文（可选）
        """
        # 构建用户消息
        user_msg = self._build_user_message(
            product, platform, recent_performance, iteration_round, style_context,
        )

        # 定义输出 schema
        output_schema = {
            "type": "object",
            "properties": {
                "narrative_type": {"type": "string"},
                "hook_type": {"type": "string"},
                "pace_style": {"type": "string"},
                "tone": {"type": "string"},
                "key_message": {"type": "string"},
                "target_emotion": {"type": "string"},
                "reasoning": {"type": "string"},
                "specific_angle": {"type": "string", "description": "具体切入角度，如'便秘人群的下午茶替代场景'"},
                "target_scenario": {"type": "string", "description": "核心使用场景，如'办公室下午3点嘴馋'"},
                "opening_style": {"type": "string", "description": "开场风格，如'第一人称安利'/'场景代入'/'数据冲击'"},
                "emotion_arc": {"type": "string", "description": "情绪弧线，如'好奇→共鸣→惊喜→紧迫'"},
                "differentiation_hints": {"type": "array", "items": {"type": "string"}, "description": "不同变体的切入角度提示"},
                "stock_refused": {"type": "string", "description": "本次明确不用的俗套及替代方案"},
            },
            "required": [
                "narrative_type", "hook_type", "pace_style",
                "tone", "key_message", "target_emotion", "reasoning",
                "specific_angle", "target_scenario",
            ],
        }

        # 调用 LLM
        result = self.agent.call_structured(
            system_prompt=self._system_prompt,
            user_message=user_msg,
            output_schema=output_schema,
            temperature=0.7,
        )

        # 构建策略对象
        signals = recent_performance or {}
        if isinstance(signals, dict):
            signals = dict(signals)
        signals["stock_refused"] = result.get("stock_refused", "")
        # 差异化字段：写入 source_signals 持久化（避免 DB schema 迁移），同时入 dataclass 供 script_agent 使用
        specific_angle = result.get("specific_angle", "")
        target_scenario = result.get("target_scenario", "")
        opening_style = result.get("opening_style", "")
        emotion_arc = result.get("emotion_arc", "")
        differentiation_hints = result.get("differentiation_hints", [])
        signals["specific_angle"] = specific_angle
        signals["target_scenario"] = target_scenario
        signals["opening_style"] = opening_style
        signals["emotion_arc"] = emotion_arc
        signals["differentiation_hints"] = differentiation_hints

        strategy = CreativeStrategy(
            task_id="",
            narrative_type=result.get("narrative_type", "问题解决型"),
            hook_type=result.get("hook_type", "痛点提问"),
            pace_style=result.get("pace_style", "中速叙事"),
            tone=result.get("tone", "亲切口语"),
            key_message=result.get("key_message", ""),
            target_emotion=result.get("target_emotion", "curious"),
            reasoning=result.get("reasoning", ""),
            specific_angle=specific_angle,
            target_scenario=target_scenario,
            opening_style=opening_style,
            emotion_arc=emotion_arc,
            differentiation_hints=json.dumps(differentiation_hints, ensure_ascii=False),
            source_signals=json.dumps(signals, ensure_ascii=False),
            created_at=datetime.now().isoformat(),
        )

        return strategy

    def _build_user_message(
        self,
        product: ProductProfile,
        platform: str,
        recent_performance: dict | None,
        iteration_round: int,
        style_context: str = "",
    ) -> str:
        """构建传给 LLM 的用户消息"""
        selling_points = product.key_selling_points
        pain_points = product.pain_points

        # 注入本地记忆上下文
        from adflow.memory_store import memory
        memory_context = memory.build_context()

        msg = ""
        if memory_context.strip():
            msg += f"""## 📝 本地积累的规则与偏好
{memory_context}

---

"""

        # 注入选中风格上下文（含规则+案例）
        if style_context:
            msg += f"""{style_context}

---

"""

        msg += f"""## 产品信息
- 名称: {product.name}
- 品类: {product.category}
- 核心卖点: {selling_points}
- 目标人群: {product.target_audience}
- 用户痛点: {pain_points}
- 品牌调性: {product.brand_tone}
- 价格区间: {product.avg_price_range}

## 投放平台
{platform}（竖屏短视频，9:16比例，建议时长15-60秒）

## 迭代轮次
第 {iteration_round + 1} 轮
"""

        if recent_performance:
            msg += f"""
## 历史投放数据（近7天）
{json.dumps(recent_performance, ensure_ascii=False, indent=2)}

⚠️ 请参考以上数据：表现好的策略方向继续强化，表现差的方向尽量避开。
同一产品最近3轮的 hook_type 不要重复。
"""
        else:
            msg += """
## 注意
这是首次投放，没有历史数据参考。请根据产品特点和平台特性选择最优策略。
"""

        return msg

    @staticmethod
    def _load_prompt() -> str:
        prompt_path = Path(__file__).parent / "prompts" / "strategy_prompt.txt"
        with open(prompt_path, "r", encoding="utf-8") as f:
            return f.read()
