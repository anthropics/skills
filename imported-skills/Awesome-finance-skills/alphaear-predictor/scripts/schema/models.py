from pydantic import BaseModel, Field
from typing import List, Optional, Dict, Any
from datetime import datetime

class TransmissionNode(BaseModel):
    node_name: str = Field(..., description="产业链节点名称")
    impact_type: str = Field(..., description="利好/利空/中性")
    logic: str = Field(..., description="该节点的传导逻辑")

class IntentAnalysis(BaseModel):
    keywords: List[str] = Field(..., description="核心实体、事件或概念关键词")
    search_queries: List[str] = Field(..., description="优化后的搜索引擎查询词")
    is_specific_event: bool = Field(..., description="是否查询特定突发事件")
    time_range: str = Field(..., description="时间范围 (recent/all/specific_date)")
    intent_summary: str = Field(..., description="一句话意图描述")

class FilterResult(BaseModel):
    """LLM 筛选结果 - 快速判断是否有有效信号"""
    has_valid_signals: bool = Field(..., description="列表中是否包含有效的金融信号")
    selected_ids: List[int] = Field(default_factory=list, description="筛选出的有效信号 ID 列表")
    themes: List[str] = Field(default_factory=list, description="信号涉及的主题")
    reason: Optional[str] = Field(default=None, description="如果无有效信号，说明原因")

class InvestmentSignal(BaseModel):
    # 核心元数据
    signal_id: str = Field(default="unknown_sig", description="唯一信号 ID")
    title: str = Field(..., description="信号标题")
    summary: str = Field(default="暂无摘要分析", description="100 字核心观点快报")
    reasoning: str = Field(default="", description="详细的推演逻辑和理由")
    
    # 逻辑传导 (ISQ Key 1)
    transmission_chain: List[TransmissionNode] = Field(default_factory=list, description="产业链传导逻辑链条")
    
    # 信号质量 (ISQ Key 2) - 来自 isq_template.DEFAULT_ISQ_TEMPLATE
    # 参考: src/schema/isq_template.py 的 DEFAULT_ISQ_TEMPLATE 定义
    sentiment_score: float = Field(default=0.0, description="[ISQ] 情绪/走势 (-1.0=极度看空 ~ 0.0=中性 ~ 1.0=极度看多)")
    confidence: float = Field(default=0.5, description="[ISQ] 确定性 (0.0=不可信 ~ 1.0=完全确定)")
    intensity: int = Field(default=3, description="[ISQ] 强度/影响量级 (1=微弱 ~ 5=极强)")
    expectation_gap: float = Field(default=0.5, description="[ISQ] 预期差/博弈空间 (0.0=充分定价 ~ 1.0=巨大预期差)")
    timeliness: float = Field(default=0.8, description="[ISQ] 时效性 (0.0=长期 ~ 1.0=超短期)")
    
    # 预测与博弈 (ISQ Key 3)
    expected_horizon: str = Field(default="T+N", description="预期的反应时窗 (如: T+0, T+3, Long-term)")
    price_in_status: str = Field(default="未知", description="市场预期消化程度 (未定价/部分定价/充分定价)")
    
    # 关联实体
    impact_tickers: List[Dict[str, Any]] = Field(default_factory=list, description="受影响的代码列表及其权重")
    industry_tags: List[str] = Field(default_factory=list, description="关联行业标签")
    
    # 溯源
    sources: List[Dict[str, str]] = Field(default_factory=list, description="来源详情 (包含 title, url, source_name)")

class ResearchContext(BaseModel):
    """研究员搜集的背景信息结构"""
    raw_signal: str = Field(..., description="原始信号内容")
    tickers_found: List[Dict[str, Any]] = Field(default_factory=list, description="找到的相关标的及其基本面/股价信息")
    industry_background: str = Field(..., description="行业背景及产业链现状")
    latest_developments: List[str] = Field(default_factory=list, description="相关事件的最新进展")
    key_risks: List[str] = Field(default_factory=list, description="潜在风险点")
    search_results_summary: str = Field(..., description="搜索结果的综合摘要")

class ScanContext(BaseModel):
    """扫描员搜集的原始数据结构"""
    hot_topics: List[str] = Field(..., description="当前市场热点话题")
    news_summaries: List[Dict[str, Any]] = Field(..., description="关键新闻摘要列表")
    market_data: Dict[str, Any] = Field(default_factory=dict, description="相关的市场行情数据")
    sentiment_overview: str = Field(..., description="整体市场情绪概览")
    raw_data_summary: str = Field(..., description="原始数据的综合摘要")

class SignalCluster(BaseModel):
    theme_title: str = Field(..., description="主题名称")
    signal_ids: List[int] = Field(..., description="包含的信号 ID 列表")
    rationale: str = Field(..., description="聚类理由")

class ClusterContext(BaseModel):
    """信号聚类结果结构"""
    clusters: List[SignalCluster] = Field(..., description="聚类列表")

class KLinePoint(BaseModel):
    date: str = Field(..., description="日期")
    open: float = Field(..., description="开盘价")
    high: float = Field(..., description="最高价")
    low: float = Field(..., description="最低价")
    close: float = Field(..., description="收盘价")
    volume: float = Field(..., description="成交量")

class ForecastResult(BaseModel):
    ticker: str = Field(..., description="股票代码")
    base_forecast: List[KLinePoint] = Field(default_factory=list, description="Kronos 模型原始预测")
    adjusted_forecast: List[KLinePoint] = Field(default_factory=list, description="LLM 调整后的预测")
    rationale: str = Field(default="", description="预测调整理由及逻辑说明")
    timestamp: str = Field(default_factory=lambda: datetime.now().strftime("%Y-%m-%d %H:%M:%S"), description="生成时间")

class InvestmentReport(BaseModel):
    overall_sentiment: str = Field(..., description="整体市场情绪评价")
    market_entropy: float = Field(..., description="市场分歧度 (0-1, 1代表极高分歧)")
    signals: List[InvestmentSignal] = Field(..., description="深度解析的投资信号列表")
    forecasts: List[ForecastResult] = Field(default_factory=list, description="相关标的的预测结果")
    timestamp: str = Field(..., description="报告生成时间")
    meta_info: Optional[Dict[str, Any]] = Field(default_factory=dict, description="其他元数据")
