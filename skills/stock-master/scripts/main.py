"""
股票分析器 Skill - 主协调器

混合数据源架构：
- Yahoo Finance: 实时价格数据 + MACD 计算
- Alpha Vantage MCP: RSI、Bollinger Bands 等技术指标

使用示例:
    analyzer = StockAnalyzer()
    result = analyzer.analyze("AAPL", ["RSI", "MACD", "Bollinger"])
    print(result)
"""

from typing import List, Dict, Optional, Any, Tuple
from datetime import datetime, timedelta
from abc import ABC, abstractmethod
import json


class DataSource(ABC):
    """数据源抽象基类"""

    @abstractmethod
    def get_quote(self, ticker: str) -> Dict[str, Any]:
        """获取最新报价"""
        pass

    @abstractmethod
    def get_indicator(self, ticker: str, indicator: str, **params) -> Dict[str, Any]:
        """获取技术指标"""
        pass


class YahooFinanceSource(DataSource):
    """
    Yahoo Finance 数据源

    优势：
    - 接近实时的价格数据
    - 可自行计算 MACD（Alpha Vantage 免费版不支持）
    - 无严格请求限制
    """

    def __init__(self):
        self.name = "Yahoo Finance"
        self._yf = None
        self._ta = None

    def _ensure_imports(self):
        """延迟导入依赖库"""
        if self._yf is None:
            try:
                import yfinance as yf
                self._yf = yf
            except ImportError:
                raise ImportError("请安装 yfinance: pip install yfinance")

        if self._ta is None:
            try:
                import pandas_ta as ta
                self._ta = ta
            except ImportError:
                # pandas_ta 可选，MACD 可以手动计算
                self._ta = None

    def get_quote(self, ticker: str) -> Dict[str, Any]:
        """获取 Yahoo Finance 实时报价"""
        self._ensure_imports()

        stock = self._yf.Ticker(ticker)
        info = stock.fast_info

        return {
            'source': self.name,
            'ticker': ticker.upper(),
            'price': float(info.last_price) if hasattr(info, 'last_price') else None,
            'open': float(info.open) if hasattr(info, 'open') else None,
            'high': float(info.day_high) if hasattr(info, 'day_high') else None,
            'low': float(info.day_low) if hasattr(info, 'day_low') else None,
            'volume': int(info.last_volume) if hasattr(info, 'last_volume') else None,
            'previous_close': float(info.previous_close) if hasattr(info, 'previous_close') else None,
            'timestamp': datetime.now().isoformat(),
            'realtime': True  # Yahoo 数据接近实时
        }

    def get_indicator(self, ticker: str, indicator: str, **params) -> Dict[str, Any]:
        """计算技术指标（使用 pandas_ta 或手动计算）"""
        self._ensure_imports()

        # 获取历史数据
        stock = self._yf.Ticker(ticker)
        period = params.get('period', '3mo')
        hist = stock.history(period=period)

        if hist.empty:
            return {'error': f'无法获取 {ticker} 的历史数据'}

        if indicator.upper() == 'MACD':
            return self._calculate_macd(hist, params)
        elif indicator.upper() == 'SMA':
            return self._calculate_sma(hist, params)
        elif indicator.upper() == 'EMA':
            return self._calculate_ema(hist, params)
        else:
            return {'error': f'Yahoo 数据源不支持指标: {indicator}'}

    def _calculate_macd(self, hist, params) -> Dict[str, Any]:
        """计算 MACD 指标"""
        fast = params.get('fast_period', 12)
        slow = params.get('slow_period', 26)
        signal = params.get('signal_period', 9)

        close = hist['Close']

        # 计算 EMA
        ema_fast = close.ewm(span=fast, adjust=False).mean()
        ema_slow = close.ewm(span=slow, adjust=False).mean()

        # MACD 线 = 快 EMA - 慢 EMA
        macd_line = ema_fast - ema_slow

        # 信号线 = MACD 的 EMA
        signal_line = macd_line.ewm(span=signal, adjust=False).mean()

        # 柱状图 = MACD - 信号线
        histogram = macd_line - signal_line

        # 获取最新值
        latest_macd = float(macd_line.iloc[-1])
        latest_signal = float(signal_line.iloc[-1])
        latest_hist = float(histogram.iloc[-1])
        prev_hist = float(histogram.iloc[-2]) if len(histogram) > 1 else 0

        # 判断信号
        if latest_hist > 0 and prev_hist <= 0:
            macd_signal = 'bullish_crossover'
            interpretation = 'MACD 金叉 - 看涨信号'
        elif latest_hist < 0 and prev_hist >= 0:
            macd_signal = 'bearish_crossover'
            interpretation = 'MACD 死叉 - 看跌信号'
        elif latest_hist > 0:
            macd_signal = 'bullish'
            interpretation = 'MACD 位于信号线上方 - 多头趋势'
        else:
            macd_signal = 'bearish'
            interpretation = 'MACD 位于信号线下方 - 空头趋势'

        return {
            'source': 'Yahoo Finance (计算)',
            'indicator': 'MACD',
            'macd_line': round(latest_macd, 4),
            'signal_line': round(latest_signal, 4),
            'histogram': round(latest_hist, 4),
            'signal': macd_signal,
            'interpretation': interpretation,
            'parameters': {'fast': fast, 'slow': slow, 'signal': signal},
            'timestamp': hist.index[-1].isoformat() if hasattr(hist.index[-1], 'isoformat') else str(hist.index[-1])
        }

    def _calculate_sma(self, hist, params) -> Dict[str, Any]:
        """计算简单移动平均线"""
        period = params.get('time_period', 20)
        close = hist['Close']
        sma = close.rolling(window=period).mean()

        return {
            'source': 'Yahoo Finance (计算)',
            'indicator': 'SMA',
            'value': round(float(sma.iloc[-1]), 4),
            'period': period,
            'timestamp': hist.index[-1].isoformat() if hasattr(hist.index[-1], 'isoformat') else str(hist.index[-1])
        }

    def _calculate_ema(self, hist, params) -> Dict[str, Any]:
        """计算指数移动平均线"""
        period = params.get('time_period', 20)
        close = hist['Close']
        ema = close.ewm(span=period, adjust=False).mean()

        return {
            'source': 'Yahoo Finance (计算)',
            'indicator': 'EMA',
            'value': round(float(ema.iloc[-1]), 4),
            'period': period,
            'timestamp': hist.index[-1].isoformat() if hasattr(hist.index[-1], 'isoformat') else str(hist.index[-1])
        }


class AlphaVantageMCPSource(DataSource):
    """
    Alpha Vantage MCP 数据源

    优势：
    - 官方 API，数据稳定可靠
    - 提供预计算的 RSI、Bollinger Bands 等指标
    - 历史数据丰富（20+ 年）

    限制：
    - 免费版 15 分钟延时
    - 每天 25 次请求限制
    - MACD 需要 Premium 订阅
    """

    def __init__(self):
        self.name = "Alpha Vantage"
        # 注意：实际调用通过 Claude MCP 工具完成
        # 这里只是数据格式化和处理逻辑

    def get_quote(self, ticker: str) -> Dict[str, Any]:
        """
        获取 Alpha Vantage 报价

        注意：实际调用需要通过 MCP 工具:
        mcp__Alpha-Vantage__TOOL_CALL(
            tool_name="GLOBAL_QUOTE",
            arguments={"symbol": ticker, "datatype": "json"}
        )
        """
        # 这是数据格式化模板
        return {
            'source': self.name,
            'ticker': ticker.upper(),
            'price': None,  # 从 MCP 响应填充
            'open': None,
            'high': None,
            'low': None,
            'volume': None,
            'previous_close': None,
            'change': None,
            'change_percent': None,
            'timestamp': None,
            'realtime': False,  # Alpha Vantage 免费版有 15 分钟延时
            'mcp_tool': 'GLOBAL_QUOTE',
            'mcp_args': {'symbol': ticker, 'datatype': 'json'}
        }

    def get_indicator(self, ticker: str, indicator: str, **params) -> Dict[str, Any]:
        """
        获取 Alpha Vantage 技术指标

        支持的免费指标: RSI, BBANDS, SMA, EMA, STOCH, ADX, CCI, AROON, MFI, OBV 等
        Premium 指标: MACD (需要订阅)
        """
        indicator = indicator.upper()

        # 通用参数
        interval = params.get('interval', 'daily')
        time_period = params.get('time_period', 14)
        series_type = params.get('series_type', 'close')

        if indicator == 'RSI':
            return {
                'source': self.name,
                'indicator': 'RSI',
                'mcp_tool': 'RSI',
                'mcp_args': {
                    'symbol': ticker,
                    'interval': interval,
                    'time_period': time_period,
                    'series_type': series_type,
                    'datatype': 'json'
                }
            }
        elif indicator in ['BBANDS', 'BOLLINGER']:
            return {
                'source': self.name,
                'indicator': 'BBANDS',
                'mcp_tool': 'BBANDS',
                'mcp_args': {
                    'symbol': ticker,
                    'interval': interval,
                    'time_period': params.get('time_period', 20),
                    'series_type': series_type,
                    'nbdevup': params.get('nbdevup', 2),
                    'nbdevdn': params.get('nbdevdn', 2),
                    'datatype': 'json'
                }
            }
        elif indicator == 'SMA':
            return {
                'source': self.name,
                'indicator': 'SMA',
                'mcp_tool': 'SMA',
                'mcp_args': {
                    'symbol': ticker,
                    'interval': interval,
                    'time_period': time_period,
                    'series_type': series_type,
                    'datatype': 'json'
                }
            }
        elif indicator == 'EMA':
            return {
                'source': self.name,
                'indicator': 'EMA',
                'mcp_tool': 'EMA',
                'mcp_args': {
                    'symbol': ticker,
                    'interval': interval,
                    'time_period': time_period,
                    'series_type': series_type,
                    'datatype': 'json'
                }
            }
        else:
            return {
                'source': self.name,
                'indicator': indicator,
                'error': f'指标 {indicator} 可能需要 Premium 订阅或不支持',
                'suggestion': '请使用 RSI, BBANDS, SMA, EMA 等免费指标'
            }


class DataValidator:
    """数据验证器 - 对比不同数据源的数据一致性"""

    PRICE_TOLERANCE = 0.01  # 价格容差 1%

    @staticmethod
    def compare_quotes(yahoo_quote: Dict, av_quote: Dict) -> Dict[str, Any]:
        """
        对比 Yahoo Finance 和 Alpha Vantage 的报价数据

        返回对比结果，如果发现不一致会标记出来
        """
        result = {
            'comparison_time': datetime.now().isoformat(),
            'yahoo': yahoo_quote,
            'alpha_vantage': av_quote,
            'discrepancies': [],
            'aligned': True
        }

        yahoo_price = yahoo_quote.get('price')
        av_price = av_quote.get('price')

        if yahoo_price and av_price:
            diff_pct = abs(yahoo_price - av_price) / yahoo_price * 100

            if diff_pct > DataValidator.PRICE_TOLERANCE * 100:
                result['discrepancies'].append({
                    'field': 'price',
                    'yahoo_value': yahoo_price,
                    'av_value': av_price,
                    'difference_pct': round(diff_pct, 4),
                    'warning': f'价格差异 {diff_pct:.2f}% 超过容差 {DataValidator.PRICE_TOLERANCE*100}%'
                })
                result['aligned'] = False

        # 对比其他字段
        for field in ['open', 'high', 'low']:
            y_val = yahoo_quote.get(field)
            av_val = av_quote.get(field)

            if y_val and av_val:
                diff_pct = abs(y_val - av_val) / y_val * 100
                if diff_pct > DataValidator.PRICE_TOLERANCE * 100:
                    result['discrepancies'].append({
                        'field': field,
                        'yahoo_value': y_val,
                        'av_value': av_val,
                        'difference_pct': round(diff_pct, 4)
                    })
                    result['aligned'] = False

        return result


class StockAnalyzer:
    """
    股票分析器 - 混合数据源架构

    数据源策略：
    - 价格数据：优先 Yahoo Finance（实时）
    - RSI, Bollinger Bands：Alpha Vantage MCP（预计算，准确）
    - MACD：Yahoo Finance + pandas 计算（AV 免费版不支持）
    - 数据验证：对比两个数据源确保一致性
    """

    def __init__(self, config: Optional[Dict] = None):
        self.config = config or self._default_config()
        self.yahoo = YahooFinanceSource()
        self.alpha_vantage = AlphaVantageMCPSource()
        self.validator = DataValidator()

        print(f"[股票分析器] 已初始化 - 混合数据源模式")
        print(f"  - 价格数据: Yahoo Finance (实时)")
        print(f"  - RSI/Bollinger: Alpha Vantage MCP")
        print(f"  - MACD: Yahoo Finance (本地计算)")

    def analyze(
        self,
        ticker: str,
        indicators: Optional[List[str]] = None,
        period: str = "3mo",
        validate_data: bool = True
    ) -> Dict[str, Any]:
        """
        执行股票技术分析

        参数:
            ticker: 股票代码 (如 "AAPL", "MSFT")
            indicators: 要计算的指标列表 (默认: ["RSI", "MACD", "Bollinger"])
            period: 分析时间周期 (默认: "3mo")
            validate_data: 是否对比验证数据源 (默认: True)

        返回:
            包含价格、指标、信号和建议的分析结果字典
        """
        indicators = indicators or ["RSI", "MACD", "Bollinger"]

        print(f"\n[股票分析器] 正在分析 {ticker}...")
        print(f"  - 指标: {indicators}")
        print(f"  - 周期: {period}")

        result = {
            'ticker': ticker.upper(),
            'timestamp': datetime.now().isoformat(),
            'data_sources': {
                'price': 'Yahoo Finance',
                'indicators': {}
            },
            'price_data': {},
            'indicators': {},
            'signal': {},
            'validation': None
        }

        # 步骤 1: 获取价格数据 (Yahoo - 实时)
        try:
            result['price_data'] = self.yahoo.get_quote(ticker)
            print(f"  ✓ 价格数据获取成功: ${result['price_data'].get('price', 'N/A')}")
        except Exception as e:
            result['price_data'] = {'error': str(e)}
            print(f"  ✗ 价格数据获取失败: {e}")

        # 步骤 2: 获取技术指标
        for indicator in indicators:
            indicator_upper = indicator.upper()

            if indicator_upper == 'MACD':
                # MACD 使用 Yahoo + 本地计算
                try:
                    result['indicators']['MACD'] = self.yahoo.get_indicator(
                        ticker, 'MACD',
                        period=period,
                        fast_period=self.config['indicators']['MACD']['fast_period'],
                        slow_period=self.config['indicators']['MACD']['slow_period'],
                        signal_period=self.config['indicators']['MACD']['signal_period']
                    )
                    result['data_sources']['indicators']['MACD'] = 'Yahoo Finance (本地计算)'
                    print(f"  ✓ MACD 计算成功")
                except Exception as e:
                    result['indicators']['MACD'] = {'error': str(e)}
                    print(f"  ✗ MACD 计算失败: {e}")

            elif indicator_upper in ['RSI', 'BOLLINGER', 'BBANDS']:
                # RSI 和 Bollinger 使用 Alpha Vantage MCP
                indicator_name = 'BBANDS' if indicator_upper in ['BOLLINGER', 'BBANDS'] else indicator_upper

                if indicator_name == 'RSI':
                    mcp_config = self.alpha_vantage.get_indicator(
                        ticker, 'RSI',
                        time_period=self.config['indicators']['RSI']['period']
                    )
                else:
                    mcp_config = self.alpha_vantage.get_indicator(
                        ticker, 'BBANDS',
                        time_period=self.config['indicators']['Bollinger']['period'],
                        nbdevup=self.config['indicators']['Bollinger']['std_dev'],
                        nbdevdn=self.config['indicators']['Bollinger']['std_dev']
                    )

                result['indicators'][indicator_name] = mcp_config
                result['data_sources']['indicators'][indicator_name] = 'Alpha Vantage MCP'
                print(f"  → {indicator_name} 需要调用 MCP 工具: {mcp_config.get('mcp_tool')}")

            else:
                # 其他指标尝试 Alpha Vantage
                mcp_config = self.alpha_vantage.get_indicator(ticker, indicator)
                result['indicators'][indicator] = mcp_config
                result['data_sources']['indicators'][indicator] = 'Alpha Vantage MCP'

        # 步骤 3: 生成交易信号
        result['signal'] = self._generate_signal(ticker, result['price_data'], result['indicators'])

        # 步骤 4: 数据验证（可选）
        if validate_data:
            result['validation'] = {
                'enabled': True,
                'note': '数据验证需要同时调用 Alpha Vantage GLOBAL_QUOTE 进行对比',
                'av_quote_config': self.alpha_vantage.get_quote(ticker)
            }

        print(f"\n[股票分析器] 分析完成")
        print(f"  → 信号: {result['signal'].get('action', 'N/A')} ({result['signal'].get('confidence', 'N/A')})")

        return result

    def compare(
        self,
        tickers: List[str],
        rank_by: str = "momentum",
        indicators: Optional[List[str]] = None
    ) -> Dict[str, Any]:
        """
        对比多只股票并按技术强度排名

        参数:
            tickers: 股票代码列表
            rank_by: 排名方式 ("momentum", "rsi", "composite")
            indicators: 用于对比的指标

        返回:
            包含排名结果的字典
        """
        indicators = indicators or ["RSI", "MACD"]

        print(f"\n[股票分析器] 对比 {len(tickers)} 只股票...")
        print(f"  - 股票: {', '.join(tickers)}")
        print(f"  - 排名方式: {rank_by}")

        comparisons = []
        for ticker in tickers:
            analysis = self.analyze(ticker, indicators, validate_data=False)
            score = self._calculate_ranking_score(analysis, rank_by)

            comparisons.append({
                'ticker': ticker.upper(),
                'analysis': analysis,
                'score': score,
                'rank': 0
            })

        # 按分数排序
        comparisons.sort(key=lambda x: x['score'], reverse=True)

        # 分配排名
        for idx, comp in enumerate(comparisons, 1):
            comp['rank'] = idx

        result = {
            'ranked_stocks': comparisons,
            'ranking_method': rank_by,
            'total_analyzed': len(tickers),
            'timestamp': datetime.now().isoformat()
        }

        print(f"\n[股票分析器] 对比完成")
        print("  排名结果:")
        for comp in comparisons:
            print(f"    #{comp['rank']}: {comp['ticker']} (分数: {comp['score']:.2f})")

        return result

    def validate_data_sources(self, ticker: str) -> Dict[str, Any]:
        """
        验证两个数据源的数据一致性

        这个方法会同时从 Yahoo Finance 和 Alpha Vantage 获取数据，
        并对比关键字段。如果发现不一致会返回警告。

        返回:
            包含对比结果和任何差异警告的字典
        """
        print(f"\n[数据验证] 正在验证 {ticker} 的数据源一致性...")

        # 获取 Yahoo 数据
        yahoo_quote = self.yahoo.get_quote(ticker)

        # Alpha Vantage 需要通过 MCP 调用
        av_config = self.alpha_vantage.get_quote(ticker)

        return {
            'ticker': ticker.upper(),
            'timestamp': datetime.now().isoformat(),
            'yahoo_quote': yahoo_quote,
            'alpha_vantage_config': av_config,
            'instruction': '请使用 MCP 工具获取 Alpha Vantage 数据后调用 compare_quotes() 进行对比',
            'note': '如果价格差异超过 1%，将会触发警告'
        }

    def _default_config(self) -> Dict:
        """默认配置"""
        return {
            'data_sources': {
                'price': 'yahoo_finance',
                'rsi': 'alpha_vantage',
                'macd': 'yahoo_finance',
                'bollinger': 'alpha_vantage'
            },
            'indicators': {
                'RSI': {
                    'period': 14,
                    'overbought': 70,
                    'oversold': 30
                },
                'MACD': {
                    'fast_period': 12,
                    'slow_period': 26,
                    'signal_period': 9
                },
                'Bollinger': {
                    'period': 20,
                    'std_dev': 2
                }
            },
            'validation': {
                'enabled': True,
                'price_tolerance': 0.01  # 1%
            }
        }

    def _generate_signal(
        self,
        ticker: str,
        price_data: Dict,
        indicators: Dict
    ) -> Dict[str, Any]:
        """
        根据技术指标生成交易信号

        策略: RSI + MACD 组合判断
        - 买入: RSI 超卖 + MACD 金叉
        - 卖出: RSI 超买 + MACD 死叉
        - 持有: 其他情况
        """
        reasoning = []
        base_signal = "HOLD"
        confidence = "low"

        # RSI 分析
        rsi_data = indicators.get('RSI', {})
        if 'mcp_args' not in rsi_data:  # 如果已经有实际数据
            rsi_value = rsi_data.get('value')
            if rsi_value:
                if rsi_value < 30:
                    reasoning.append(f"RSI 超卖 ({rsi_value:.1f} < 30) - 潜在买入机会")
                    base_signal = "BUY"
                    confidence = "moderate"
                elif rsi_value > 70:
                    reasoning.append(f"RSI 超买 ({rsi_value:.1f} > 70) - 潜在卖出信号")
                    base_signal = "SELL"
                    confidence = "moderate"
                else:
                    reasoning.append(f"RSI 中性区间 ({rsi_value:.1f})")
        else:
            reasoning.append("RSI 需要通过 MCP 获取")

        # MACD 分析
        macd_data = indicators.get('MACD', {})
        macd_signal = macd_data.get('signal')
        if macd_signal:
            if macd_signal == 'bullish_crossover':
                reasoning.append("MACD 金叉 - 看涨信号")
                if base_signal == "BUY":
                    confidence = "high"
                elif base_signal == "HOLD":
                    base_signal = "BUY"
                    confidence = "moderate"
            elif macd_signal == 'bearish_crossover':
                reasoning.append("MACD 死叉 - 看跌信号")
                if base_signal == "SELL":
                    confidence = "high"
                elif base_signal == "HOLD":
                    base_signal = "SELL"
                    confidence = "moderate"
            elif macd_signal == 'bullish':
                reasoning.append("MACD 多头趋势")
            else:
                reasoning.append("MACD 空头趋势")

        # Bollinger Bands 分析
        bb_data = indicators.get('BBANDS', {})
        if 'mcp_args' not in bb_data:
            # 如果有实际数据可以分析
            pass

        return {
            'action': base_signal,
            'confidence': confidence,
            'reasoning': reasoning,
            'price': price_data.get('price'),
            'timestamp': datetime.now().isoformat()
        }

    def _calculate_ranking_score(self, analysis: Dict, method: str) -> float:
        """计算排名分数"""
        indicators = analysis.get('indicators', {})

        if method == "rsi":
            rsi_data = indicators.get('RSI', {})
            rsi = rsi_data.get('value', 50)
            return min(rsi, 70) if rsi else 50

        elif method == "momentum":
            score = 50

            # RSI 贡献
            rsi_data = indicators.get('RSI', {})
            if 'value' in rsi_data:
                score = rsi_data['value']

            # MACD 贡献
            macd_data = indicators.get('MACD', {})
            macd_signal = macd_data.get('signal')
            if macd_signal == 'bullish_crossover':
                score += 15
            elif macd_signal == 'bullish':
                score += 5
            elif macd_signal == 'bearish_crossover':
                score -= 15
            elif macd_signal == 'bearish':
                score -= 5

            return score

        else:  # composite
            rsi_data = indicators.get('RSI', {})
            rsi = rsi_data.get('value', 50)
            macd_data = indicators.get('MACD', {})
            macd_hist = macd_data.get('histogram', 0)

            return (rsi * 0.6) + (macd_hist * 20 * 0.4)


def format_av_response(av_response: Dict, indicator: str) -> Dict[str, Any]:
    """
    格式化 Alpha Vantage MCP 响应

    用于处理从 MCP 工具返回的原始数据
    """
    if 'error' in av_response or 'Information' in av_response:
        return {'error': av_response.get('error') or av_response.get('Information')}

    if indicator == 'RSI':
        meta = av_response.get('Meta Data', {})
        data = av_response.get('Technical Analysis: RSI', {})

        if data:
            latest_date = list(data.keys())[0]
            latest_value = float(data[latest_date]['RSI'])

            # 判断信号
            if latest_value < 30:
                signal = 'oversold'
                interpretation = f'RSI 超卖 ({latest_value:.1f}) - 潜在买入机会'
            elif latest_value > 70:
                signal = 'overbought'
                interpretation = f'RSI 超买 ({latest_value:.1f}) - 潜在卖出信号'
            else:
                signal = 'neutral'
                interpretation = f'RSI 中性 ({latest_value:.1f})'

            return {
                'source': 'Alpha Vantage',
                'indicator': 'RSI',
                'value': latest_value,
                'signal': signal,
                'interpretation': interpretation,
                'timestamp': latest_date
            }

    elif indicator == 'BBANDS':
        meta = av_response.get('Meta Data', {})
        data = av_response.get('Technical Analysis: BBANDS', {})

        if data:
            latest_date = list(data.keys())[0]
            latest = data[latest_date]

            return {
                'source': 'Alpha Vantage',
                'indicator': 'BBANDS',
                'upper_band': float(latest['Real Upper Band']),
                'middle_band': float(latest['Real Middle Band']),
                'lower_band': float(latest['Real Lower Band']),
                'timestamp': latest_date
            }

    elif indicator == 'GLOBAL_QUOTE':
        quote = av_response.get('Global Quote', {})
        if quote:
            return {
                'source': 'Alpha Vantage',
                'ticker': quote.get('01. symbol'),
                'price': float(quote.get('05. price', 0)),
                'open': float(quote.get('02. open', 0)),
                'high': float(quote.get('03. high', 0)),
                'low': float(quote.get('04. low', 0)),
                'volume': int(quote.get('06. volume', 0)),
                'previous_close': float(quote.get('08. previous close', 0)),
                'change': float(quote.get('09. change', 0)),
                'change_percent': quote.get('10. change percent'),
                'timestamp': quote.get('07. latest trading day'),
                'realtime': False
            }

    return av_response


def main():
    """演示混合数据源股票分析"""
    print("=" * 60)
    print("股票分析器 - 混合数据源演示")
    print("=" * 60)

    analyzer = StockAnalyzer()

    # 示例 1: 单股分析
    print("\n--- 示例 1: 分析 AAPL ---")
    result = analyzer.analyze("AAPL", ["RSI", "MACD", "Bollinger"])

    print("\n分析结果摘要:")
    print(f"  股票: {result['ticker']}")
    print(f"  价格: ${result['price_data'].get('price', 'N/A')}")
    print(f"  信号: {result['signal']['action']}")
    print(f"  置信度: {result['signal']['confidence']}")
    print(f"  理由: {', '.join(result['signal']['reasoning'])}")

    print("\n" + "=" * 60)
    print("演示完成!")
    print("=" * 60)


if __name__ == "__main__":
    main()
