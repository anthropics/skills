from typing import List, Dict, Any
from ..schema.models import KLinePoint

def get_forecast_adjustment_instructions(ticker: str, news_context: str, model_forecast: List[KLinePoint]):
    """
    生成 LLM 预测调整指令
    """
    forecast_str = "\n".join([f"- {p.date}: O:{p.open}, C:{p.close}" for p in model_forecast])
    
    return f"""你是一位资深的量化策略分析师。
你的任务是：根据给定的【Kronos 模型预测结果】和【最新的基本面/新闻背景】，对模型预测进行“主观/逻辑调整”。

股票代码: {ticker}

【Kronos 模型原始预测 (OHLC)】:
{forecast_str}

【最新情报背景】:
{news_context}

调整原则:
1. 原始预测是基于历史的技术面推演。
2. 情报背景中可能包含【Kronos模型定量修正预测】，这是基于历史新闻训练的专用模型计算出的量化结果。
3. 如果存在“定量修正预测”，请**高度参考**该数值作为基础，除非你有非常确凿的逻辑认为该量化模型失效（例如遇到模型未见过的极端黑天鹅）。
4. 你的核心任务是：结合定性分析（新闻及其逻辑）来验证或微调这些数字，并给出合理的解释（Rationale）。
5. 如果没有“定量修正预测”，则你需要根据新闻信号手动大幅调整趋势。

输出要求 (严格 JSON 格式):
```json
{{
  "adjusted_forecast": [
    {{
      "date": "YYYY-MM-DD",
      "open": float,
      "high": float,
      "low": float,
      "close": float,
      "volume": float
    }},
    ...
  ],
  "rationale": "详细说明调整的逻辑依据，例如：考虑到[事件A]，预期短线将突破压力位..."
}}
```
注意：必须输出与原始预测相同数量的数据点，且日期一一对应。
"""

def get_forecast_task():
    return "请根据以上背景和模型预测，给出调整后的 K 线数据并说明理由。"
