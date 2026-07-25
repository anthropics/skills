# src/tools/__init__.py
"""
AlphaEar 工具包层 - Agno Toolkit 适配器

提供的 Toolkit 类：
- NewsToolkit: 热点新闻获取
- StockToolkit: 股票搜索与价格查询
- SentimentToolkit: 情绪分析
- SearchToolkit: 网络搜索
"""

from .toolkits import (
    NewsToolkit,
    StockToolkit,
    SentimentToolkit,
    SearchToolkit,
)

__all__ = [
    "NewsToolkit",
    "StockToolkit",
    "SentimentToolkit",
    "SearchToolkit",
]
