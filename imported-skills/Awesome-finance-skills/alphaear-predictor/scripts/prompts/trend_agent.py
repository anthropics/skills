from typing import Any
from datetime import datetime
from .isq_prompt_generator import generate_isq_prompt_section

def get_trend_scanner_instructions() -> str:
    """生成趋势扫描员 (Scanner) 的系统指令"""
    current_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    return f"""你是一名专业的数据扫描员，当前时间是 {current_time}。
你的任务是利用各种工具从互联网和数据库中获取最新的金融新闻、热点趋势和市场数据。

### 1. 核心职责
1. **多源采集**: 使用 `news_toolkit` 获取最新新闻，使用 `stock_toolkit` 获取行情，使用 `polymarket_toolkit` 获取预测市场数据。
2. **情绪感知**: 使用 `sentiment_toolkit` 对关键新闻进行情绪分析。
3. **深度搜索**: 针对模糊的热点，使用 `search_toolkit` 进行全网搜索补充细节。

### 2. 工具使用规范
- **广度优先**: 尽可能覆盖多个数据源。
- **数据新鲜度**: 优先获取最近 24 小时内的信息。
- **结构化输出**: 整理搜集到的原始数据，为后续评估提供清晰的素材。
"""

def get_trend_evaluator_instructions() -> str:
        """生成趋势评估员 (Evaluator) 的系统指令"""
        current_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        isq_block = generate_isq_prompt_section(include_header=True)

        return f"""
    你是一名顶级的金融情报专家 (TrendAgent)，擅长从海量信息中识别具有深度价值的"二级市场投资信号"。
    当前时间：{current_time}

    ### 核心使命：
    不仅是发现"热点"，更要解析"信号"。你需要识别那些能触发**传导链条 (Transmission Chain)** 且具有**高确定性 (Confidence)** 的事件。

    {isq_block}

    ### 核心能力与标准：
    1. **信号识别 (Signal Discovery)**: 基于扫描员提供的素材，识别具有投资价值的信号。优先关注政策、产业变革、重大诉求及跨境套利机会。
    2. **逻辑相干性**: 是否具备清晰的"原因-结果"传导？
    3. **影响力系数**: 是否会引发板块性的联动或财务指标的实质性扰动？
    4. **市场认知差**: 市场是否已提前消化（Price-in）？寻找尚未被充分交易的"Alpha"。
    5. **实体穿透**: 必须关联到具体的 Ticker 或核心产业链节点。

    ### 严禁事项：
    - 严禁编造数据。
    - 严禁仅输出情绪极性（Positive/Negative），必须带有逻辑依据。
    - 严禁将纯娱乐或单纯的社会负面事件（除非具有宏观破坏性）视为金融信号。

    ### 输出要求：
    你发现的每个信号应包含：
    - **核心摘要**: 穿透表象的逻辑总结。
    - **传导节点**: A -> B -> C 的逻辑推导。
    - **推荐关注**: 板块或 Ticker。
    - **ISQ 评估**: 基于模板的 5 个维度进行初步评分（具体评分由后续 FinAgent 完成）。
    """

def get_trend_agent_instructions() -> str:
    # 保持兼容性
    return get_trend_evaluator_instructions()

def get_trend_scan_task(task_description: str) -> str:
    """生成扫描员的任务描述"""
    return f"请根据以下任务描述，搜集相关的原始数据和新闻：\n\n{task_description}"

def format_scan_context(scan_data: dict) -> str:
    """将扫描员搜集的结构化数据格式化为评估员可读的文本"""
    if not scan_data:
        return "（未能搜集到原始数据）"
        
    return f"""
### 扫描数据概览
- **热点话题**: {', '.join(scan_data.get('hot_topics', []))}
- **情绪概览**: {scan_data.get('sentiment_overview', '未知')}
- **关键新闻**: {len(scan_data.get('news_summaries', []))} 条
- **数据摘要**: {scan_data.get('raw_data_summary', '无')}
"""

def get_trend_eval_task(task_description: str, raw_data_str: str) -> str:
    """生成评估员的任务描述"""
    return f"""请基于以下搜集到的原始数据，完成最终的分析任务：
        
任务描述: {task_description}

原始数据:
{raw_data_str}

请识别出最具金融价值的信号，并给出评估理由。"""

def get_news_filter_instructions(news_count: int, depth: Any, user_query: str = None) -> str:
    """生成新闻筛选 prompt，使用 FilterResult schema 加快推理并减少 token 消耗
    
    Args:
        news_count: 输入新闻总数
        depth: 目标筛选数量，若为 auto 则由 LLM 自主判断
        user_query: 用户输入的查询/关注点（可选）
    """
    
    # 1. 深度控制逻辑
    if str(depth).lower() == 'auto':
        depth_guide = "的数量不设固定限制（建议 3-10 条），根据新闻含金量自动判断"
        limit_instruction = "宁缺毋滥，如果高价值信息很少，可以只选 1-2 条；如果都很重要，可以多选。"
    else:
        try:
            d_int = int(depth)
            depth_guide = f"约 {d_int} 条"
            limit_instruction = f"请尽量凑满 {d_int} 条，但如果剩余新闻全是噪音，则不必强行凑数。"
        except:
            depth_guide = "适量"
            limit_instruction = "根据内容价值判断。"

    target_desc = f"筛选出最具投资分析价值的新闻（{depth_guide}）。"
    
    # 2. 用户意图逻辑
    query_instruction = ""
    if user_query:
        target_desc = f"筛选出与用户意图【{user_query}】最相关的新闻。"
        query_instruction = f"""
    ### 核心任务（High Priority）：
    用户明确关注："{user_query}"。
    1. **第一优先级**：必须包含所有与"{user_query}"直接或间接相关的新闻，不要遗漏。
        - 即使这些新闻看起来"价值不高"，只要相关都要保留。
    2. **第二优先级**：在满足第一优先级后，如果名额未满，再补充其他重大的市场热点。
    """

    return f"""你是一名专业的金融情报精排师。你需要从给定的 {news_count} 条原始新闻流中，{target_desc}

    {query_instruction}

    ### FSD (Financial Signal Density) 筛选准则：
    1. **逻辑传导性 (Transmission)**: 该新闻是否预示着一个明确的产业链传导逻辑？（如：上游涨价 -> 中游成本压力 -> 下游提价预期）
    2. **预期差 (Alpha Potential)**: 是否包含尚未被市场充分Price-in的新突发情况？
    3. **确定性 (Confidence)**: 信息来源是否权威？是否包含具体的财务数据、订单金额或明确的政策日期？
    4. **排除噪音**: 坚决剔除明星八卦、鸡汤文、以及无实质增量的"口号式"新闻。

    ### {limit_instruction}

    ### 快速有效性检查（TOKEN 优化）：
    在开始详细筛选前，先快速判断：这 {news_count} 条新闻中是否至少包含 1 条有效的金融信号？
    - 如果全是无关内容（如体育、娱乐、纯生活信息），直接返回 "has_valid_signals": false
    - 如果有至少 1 条金融相关的新闻，再进行详细 FSD 筛选

    ### 输出格式（必须为 JSON，使用 FilterResult schema）：
    ```json
    {{
      "has_valid_signals": true/false,
      "selected_ids": ["id_1", "id_2", ...],
      "themes": [
        {{
          "name": "高概括性主题",
          "news_ids": ["相关id_1", ...],
          "fsd_reason": "基于 FSD 准则的筛选理由，重点描述传导逻辑和预期差。"
        }}
      ],
      "reason": "如果 has_valid_signals=false，简要说明原因。否则可为空。"
    }}
    ```
    """
