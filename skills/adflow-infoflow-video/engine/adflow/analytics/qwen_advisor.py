# -*- coding: utf-8 -*-
"""千问剪辑顾问 — 在编辑时基于因子分析给出自然语言建议

用法:
    advisor = QwenAdvisor()
    advice = advisor.advise(current_factors, reference_hits)
"""

import json
from typing import Optional

from adflow.agents.base_agent import BaseAgent
from adflow.analytics.factor_types import VideoFactors, FactorReport
from adflow.config_loader import config


SYSTEM_PROMPT = """你是一个专业的短视频广告剪辑顾问。你的任务是基于视频因子分析数据，
给剪辑师提供具体、可操作的优化建议。

## 你的风格
- 每条建议引用具体数据（如"爆款平均钩子占比22%，你的只有15%"）
- 建议要具体到秒、百分比、镜头序号
- 先肯定优点，再指出问题，最后给出修改方案
- 用 ✓ ⚠ ✗ 标记优劣程度
- 保持简洁，每条建议不超过2行

## 可用因子维度
1. 剪辑节奏: avg_shot_duration(平均镜头时长秒), shot_count(镜头数),
   shot_duration_variance(时长方差), cut_speed(切换密度次/秒)
2. 情绪曲线: peak_emotion_position(峰值位置0-1), emotion_volatility(波动率),
   emotion_energy(能量1-10)
3. 视觉冲击: brightness_mean(亮度), brightness_variance(亮度变化),
   scene_change_rate(场景切换率)
4. 文案密度: words_per_second(语速字/秒), keyword_density(行动词密度),
   cta_position_ratio(CTA位置)
5. 音色匹配: voice_gender(性别), voice_speed(语速),
   bgm_energy(BGM能量), voice_bgm_match(协调度0-1)
6. 结构比例: hook_ratio(钩子占比), product_intro_time(产品时机),
   cta_duration(CTA时长), total_duration(总时长)

## 输出格式
请用纯文本输出，不要用JSON。按以下结构组织：

[优点]
✓ ...

[问题]
⚠ ...
✗ ...

[建议]
1. ...
2. ...
"""


class QwenAdvisor:
    """千问剪辑顾问"""

    def __init__(self):
        cfg = config.get("analytics.qwen_advisor", {}) or {}
        self.enabled = cfg.get("enabled", True)
        self.model_name = cfg.get("model", "qwen-max")
        self.temperature = cfg.get("temperature", 0.3)

    def advise(
        self,
        current_factors: VideoFactors,
        report: Optional[FactorReport] = None,
        product_name: str = "",
    ) -> str:
        """基于当前脚本因子 + 爆款基准给出剪辑建议。

        Args:
            current_factors: 当前脚本的因子快照
            report: 因子分析报告（含爆款基准，可选）
            product_name: 产品名（可选）

        Returns:
            自然语言建议文本
        """
        if not self.enabled:
            return "千问顾问未启用"

        # 构建对比上下文
        context_parts = ["## 当前脚本因子"]
        fd = current_factors.to_dict()
        context_parts.append(json.dumps(fd, ensure_ascii=False, indent=2))

        if report and report.benchmarks:
            context_parts.append("\n## 爆款因子基准（重要因子Top10）")
            for bm in report.benchmarks[:10]:
                context_parts.append(
                    f"- {bm.name}: 爆款均值{bm.hit_mean:.4f}±{bm.hit_std:.4f} "
                    f"区间[{bm.hit_min:.4f}, {bm.hit_max:.4f}] "
                    f"重要性{bm.importance:.1f} | {bm.recommendation}"
                )

        if product_name:
            context_parts.insert(0, f"## 产品: {product_name}")

        user_msg = "\n".join(context_parts)

        try:
            agent = BaseAgent(
                model=self.model_name,
                temperature=self.temperature,
            )
            response = agent.call(SYSTEM_PROMPT, user_msg)
            return response
        except Exception as e:
            return f"千问顾问调用失败: {e}"
