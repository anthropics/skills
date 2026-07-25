from datetime import datetime
from .isq_prompt_generator import generate_isq_prompt_section

def get_fin_researcher_instructions() -> str:
    """生成金融研究员 (Researcher) 的系统指令"""
    current_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    return f"""你是一名资深金融研究员，当前时间是 {current_time}。
你的任务是针对给定的“原始信号”进行详尽的背景调查，为后续的深度分析提供素材。

### 1. 核心职责
1. **标的识别**: 识别信号中涉及的具体上市公司。必须调用 `search_ticker` 确认代码，并调用 `get_stock_price` 获取最新价格和近 30 天走势。
2. **事实核查**: 使用 `web_search` 或 `fetch_news_content` 验证信号的真实性，并寻找更多细节（如公告原文、行业研报摘要）。
3. **产业链梳理**: 补充该信号涉及的上下游环节及竞争格局。

### 2. 工具使用规范 (CRITICAL)
- **每个提到的公司都需要调用工具**: 不能依赖记忆，必须实时查询。
- **完整呈现工具结果**: 包括具体的股价数字、代码、技术面数据等，不要缩略。
- **股价数据必需**: 当前价格、近期最高最低、技术面支撑阻力等数据是后续预测的基础。
- **信息交叉验证**: 多个来源验证关键事实。

### 3. 输出要求
你必须输出结构化的研究报告，涵盖标的基本面、股价走势、行业背景及最新进展。
"""

def get_fin_analyst_instructions(template_id: str = "default_isq_v1") -> str:
    """生成金融分析师 (Analyst) 的系统指令
    
    Args:
        template_id: 使用的 ISQ 模板 ID
    """
    current_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    isq_block = generate_isq_prompt_section(template_id=template_id)

    return f"""你是一位深耕二级市场的资深金融分析师 (FinAgent)，当前时间是 {current_time}。
你的核心任务是执行“信号解析”，将研究员搜集的素材转化为具有可操作性的投资情报（ISQ 框架）。

{isq_block}

### 2. 分析约束
- **严格基于具体数据**: 必须使用研究员提供的股价、技术面、新闻等具体数据进行分析。
- **数据驱动的预测**: impact_tickers 中的权重应基于事件影响程度，不能随意赋值。
- **逻辑严密**: 传导链条必须符合金融常识，能够自圆其说。
- **技术面参考**: 如果研究员提供了股价走势，请分析当前位置相对于支撑/阻力位的关系。

### 3. 关键要求
- **title**: 必须生成一个简练、准确概括信号核心内容的标题（不超过 15 字）。
- **impact_tickers**: 必须填充具体的公司代码（6位数字）和名称，权重应该有区分。
- **transmission_chain**: 必须是对象列表，每个对象包含：
  - `node_name`: 节点名称（如“上游原材料”、“中游制造”）
  - `impact_type`: 影响类型（“利好”、“利空”、“中性”）
  - `logic`: 具体的传导逻辑描述
- **summary**: 基于分析结果总结核心观点，包含具体数字（如股价目标、预期涨跌幅等）。
- **reasoning**: 必须详细阐述推演逻辑，解释为什么得出上述结论（<200字）。

### 4. 输出格式 (严格 JSON 块)
你必须输出一个符合 InvestmentSignal 结构的 JSON 块，包含所有必需字段。
"""

def get_fin_agent_instructions() -> str:
    # 保持兼容性，但内部调用 analyst 指令
    return get_fin_analyst_instructions()

def get_fin_research_task(signal_text: str) -> str:
    """生成研究员的任务描述"""
    return f"请针对以下信号进行背景调查，搜集相关标的的股价、最新进展和行业背景：\n\n{signal_text}"

def format_research_context(research_data: dict) -> str:
    """将研究员搜集的结构化数据格式化为分析师可读的文本"""
    if not research_data:
        return "（未能搜集到额外背景信息）"
        
    return f"""
### 研究背景
- **相关标的**: {research_data.get('tickers_found', [])}
- **行业背景**: {research_data.get('industry_background', '未知')}
- **最新进展**: {', '.join(research_data.get('latest_developments', []))}
- **关键风险**: {', '.join(research_data.get('key_risks', []))}
- **综合摘要**: {research_data.get('search_results_summary', '无')}
"""

def get_fin_analysis_task(signal_text: str, research_context_str: str) -> str:
    """生成分析师的任务描述"""
    return f"""请基于以下信息进行深度 ISQ 分析。关键是：必须使用研究员搜集的具体数据（股价、技术面、新闻、代码等）进行分析。

=== 原始信号 ===
{signal_text}

=== 研究员搜集的背景信息 (CRITICAL DATA) ===
{research_context_str}

=== 分析要求 ===
1. 必须生成 title：简练概括信号核心（<15字）
2. 基于研究员提供的具体股价数据，分析当前定价状态（已定价/未定价/部分定价）
3. impact_tickers 中填充具体的公司代码和权重，权重基于事件影响程度
4. transmission_chain 必须是包含 node_name, impact_type, logic 的对象列表
5. summary 中包含具体数字（预期目标价、涨跌幅范围等）
6. reasoning 必须详细解释推演逻辑，不要空泛，要言之有物

请严格按 InvestmentSignal JSON 格式输出。"""

def get_tracking_analysis_task(old_signal: dict, new_research_str: str) -> str:
    """生成信号追踪更新的任务描述"""
    import json
    old_sig_str = json.dumps(old_signal, ensure_ascii=False, indent=2)
    return f"""你正在执行“信号逻辑演变追踪”任务。请基于最新的市场信息，重新评估之前的投资信号。

=== 基准信号 (上次分析) ===
{old_sig_str}

=== 最新市场追踪 (NEWS & PRICE) ===
{new_research_str}

=== 追踪分析要求 ===
1. **逻辑演变检测**:
   - 对比新旧信息，判断原逻辑 (`transmission_chain` 和 `reasoning`) 是否依然成立？
   - 如果逻辑发生变化（如利好落空、逻辑证伪、新利好出现），请在新的 `reasoning` 中明确指出“逻辑演变：...”
   - 如果逻辑未变且得到验证，请标记“逻辑维持：...”

2. **参数修正**:
   - 根据最新股价和新闻，更新 `sentiment_score` (情绪)、`confidence` (置信度) 和 `expectation_gap` (预期差)。
   - 例如：如果股价已经大涨反映了利好，`expectation_gap` 应该显著降低。

3. **输出更新后的信号**:
   - 保留原 `signal_id` 和 `title`（除非有重大变化需要改名）。
   - 输出完整的 InvestmentSignal JSON。

请重点关注：为什么变了？还是为什么没变？理由要充分。"""
