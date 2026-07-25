import json
from typing import List, Optional, Dict, Any
from datetime import datetime
from loguru import logger
import pandas as pd

from .kronos_predictor import KronosPredictorUtility
from .utils.database_manager import DatabaseManager
from .schema.models import ForecastResult, KLinePoint, InvestmentSignal

class ForecastUtils:
    """
    预测辅助工具 (ForecastUtils)
    提供数据准备、基础模型预测等功能。
    LLM 调整逻辑已移交 Agent 执行 (参考 scripts/prompts/PROMPTS.md)。
    """
    
    def __init__(self, db: DatabaseManager):
        self.db = db
        self.predictor_util = KronosPredictorUtility() # Singleton

    def get_base_forecast(
        self,
        ticker: str,
        signals: List[Dict] = None,
        lookback: int = 20,
        pred_len: int = 5,
    ) -> Optional[List[KLinePoint]]:
        """
        获取基础预测数据 (技术面 + 新闻模型定量修正)。
        Agent 应随后使用 PROMPTS.md 中的指令进行定性调整。
        """
        logger.info(f"🔮 Generating base forecast for {ticker}...")
        
        # 1. 获取历史数据
        from .stock_tools import StockTools
        stock_tools = StockTools(self.db, auto_update=False)
        
        end_date = datetime.now().strftime("%Y-%m-%d")
        # 宽放一点时间以确保有足够的交易日
        start_date = (datetime.now() - pd.Timedelta(days=max(lookback * 4, 90))).strftime("%Y-%m-%d")
        df = stock_tools.get_stock_price(ticker, start_date=start_date, end_date=end_date)

        if df.empty or len(df) < lookback:
            # Try force sync
            df = stock_tools.get_stock_price(ticker, start_date=start_date, end_date=end_date, force_sync=True)

        if df.empty:
            logger.warning(f"⚠️ No history data for {ticker}")
            return None

        effective_lookback = lookback
        if len(df) < lookback:
            if len(df) < 10:
                logger.warning(f"⚠️ Insufficient history for {ticker}")
                return None
            effective_lookback = len(df)

        # 2. 准备信号上下文
        signal_lines = []
        for s in (signals or []):
            try:
                title = s.get('title', '') if isinstance(s, dict) else getattr(s, 'title', '')
                summary = s.get('summary', '') if isinstance(s, dict) else getattr(s, 'summary', '')
                if title or summary:
                    signal_lines.append(f"- {title}: {summary}")
            except Exception:
                continue

        signals_context = "\n".join(signal_lines).strip()
        
        # 3. 模型预测 (News-Adjusted if context exists)
        if signals_context:
            return self.predictor_util.get_base_forecast(df, lookback=effective_lookback, pred_len=pred_len, news_text=signals_context)
        else:
            return self.predictor_util.get_base_forecast(df, lookback=effective_lookback, pred_len=pred_len, news_text=None)
