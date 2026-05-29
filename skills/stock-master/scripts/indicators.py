"""
技术指标本地计算模块 v3.4

功能：
- 本地计算 RSI、布林带、ATR、均线等
- 支持港股（当 Alpha Vantage 不可用时）
- 提供优雅降级能力

v3.4 新增:
- K线形态识别（锤子线、吞没、十字星、早晨之星等）
- 趋势形态识别（双底、双顶、头肩顶、三角形等）

v3.3:
- KDJ 随机指标
- MACD/RSI 背离检测
- 增强版支撑阻力位（斐波那契）
- OBV 量能指标
- 威廉指标 Williams %R
- 乖离率 BIAS
"""

from typing import Dict, List, Optional, Any, Tuple
import numpy as np
from datetime import datetime


def is_hk_stock(ticker: str) -> bool:
    """判断是否是港股"""
    return ticker.upper().endswith('.HK')


def is_cn_stock(ticker: str) -> bool:
    """判断是否是A股"""
    return ticker.upper().endswith('.SS') or ticker.upper().endswith('.SZ')


def get_stock_data(ticker: str, period: str = '3mo') -> Dict[str, Any]:
    """
    获取股票历史数据

    返回:
        包含 close, high, low, volume 等数组的字典
    """
    try:
        import yfinance as yf
        stock = yf.Ticker(ticker)
        hist = stock.history(period=period)

        if hist.empty:
            return {'error': f'无法获取 {ticker} 的数据'}

        return {
            'ticker': ticker.upper(),
            'close': hist['Close'].values,
            'high': hist['High'].values,
            'low': hist['Low'].values,
            'open': hist['Open'].values,
            'volume': hist['Volume'].values,
            'dates': hist.index.tolist(),
            'current_price': float(hist['Close'].iloc[-1]),
            'source': 'Yahoo Finance'
        }
    except Exception as e:
        return {'error': str(e)}


# ============================================
# RSI 本地计算
# ============================================

def calculate_rsi(prices: np.ndarray, period: int = 14) -> float:
    """
    计算 RSI (相对强弱指数)

    参数:
        prices: 收盘价数组
        period: RSI 周期，默认 14

    返回:
        最新的 RSI 值
    """
    if len(prices) < period + 1:
        return 50.0  # 数据不足时返回中性值

    # 计算价格变动
    deltas = np.diff(prices)

    # 分离涨跌
    gains = np.where(deltas > 0, deltas, 0)
    losses = np.where(deltas < 0, -deltas, 0)

    # 使用 EMA 方式计算平均涨跌（更平滑）
    alpha = 1.0 / period

    avg_gain = gains[0]
    avg_loss = losses[0]

    for i in range(1, len(gains)):
        avg_gain = alpha * gains[i] + (1 - alpha) * avg_gain
        avg_loss = alpha * losses[i] + (1 - alpha) * avg_loss

    if avg_loss == 0:
        return 100.0

    rs = avg_gain / avg_loss
    rsi = 100 - (100 / (1 + rs))

    return round(rsi, 2)


def calculate_rsi_series(prices: np.ndarray, period: int = 14) -> np.ndarray:
    """计算 RSI 序列（用于判断趋势）"""
    if len(prices) < period + 1:
        return np.array([50.0])

    deltas = np.diff(prices)
    gains = np.where(deltas > 0, deltas, 0)
    losses = np.where(deltas < 0, -deltas, 0)

    alpha = 1.0 / period
    rsi_values = []

    avg_gain = np.mean(gains[:period])
    avg_loss = np.mean(losses[:period])

    for i in range(period, len(gains)):
        avg_gain = alpha * gains[i] + (1 - alpha) * avg_gain
        avg_loss = alpha * losses[i] + (1 - alpha) * avg_loss

        if avg_loss == 0:
            rsi_values.append(100.0)
        else:
            rs = avg_gain / avg_loss
            rsi_values.append(100 - (100 / (1 + rs)))

    return np.array(rsi_values)


# ============================================
# 布林带本地计算
# ============================================

def calculate_bollinger_bands(
    prices: np.ndarray,
    period: int = 20,
    std_dev: float = 2.0
) -> Dict[str, float]:
    """
    计算布林带

    参数:
        prices: 收盘价数组
        period: 移动平均周期，默认 20
        std_dev: 标准差倍数，默认 2

    返回:
        包含 upper, middle, lower 的字典
    """
    if len(prices) < period:
        return {'error': '数据不足'}

    # 计算中轨（SMA）
    middle = np.mean(prices[-period:])

    # 计算标准差
    std = np.std(prices[-period:])

    # 计算上下轨
    upper = middle + std_dev * std
    lower = middle - std_dev * std

    return {
        'upper': round(upper, 2),
        'middle': round(middle, 2),
        'lower': round(lower, 2),
        'bandwidth': round((upper - lower) / middle * 100, 2),  # 带宽百分比
        'source': 'Local Calculation'
    }


# ============================================
# ATR (平均真实波幅) 计算
# ============================================

def calculate_atr(
    high: np.ndarray,
    low: np.ndarray,
    close: np.ndarray,
    period: int = 14
) -> float:
    """
    计算 ATR (Average True Range)

    ATR 反映股票的波动性，用于动态止损计算

    参数:
        high: 最高价数组
        low: 最低价数组
        close: 收盘价数组
        period: ATR 周期，默认 14

    返回:
        最新的 ATR 值
    """
    if len(high) < period + 1:
        return 0.0

    # 计算 True Range
    tr_list = []
    for i in range(1, len(high)):
        # TR = max(高-低, |高-昨收|, |低-昨收|)
        tr = max(
            high[i] - low[i],
            abs(high[i] - close[i-1]),
            abs(low[i] - close[i-1])
        )
        tr_list.append(tr)

    tr_array = np.array(tr_list)

    # 使用 EMA 计算 ATR
    alpha = 1.0 / period
    atr = tr_array[0]

    for i in range(1, len(tr_array)):
        atr = alpha * tr_array[i] + (1 - alpha) * atr

    return round(atr, 4)


def calculate_atr_percent(
    high: np.ndarray,
    low: np.ndarray,
    close: np.ndarray,
    period: int = 14
) -> float:
    """计算 ATR 百分比（相对于当前价格）"""
    atr = calculate_atr(high, low, close, period)
    current_price = close[-1]

    if current_price == 0:
        return 0.0

    return round(atr / current_price * 100, 2)


# ============================================
# 均线系统
# ============================================

def calculate_ma(prices: np.ndarray, period: int) -> float:
    """计算简单移动平均线"""
    if len(prices) < period:
        return prices[-1] if len(prices) > 0 else 0
    return round(np.mean(prices[-period:]), 2)


def calculate_ema(prices: np.ndarray, period: int) -> float:
    """计算指数移动平均线"""
    if len(prices) < period:
        return prices[-1] if len(prices) > 0 else 0

    ema = prices[0]
    alpha = 2.0 / (period + 1)

    for price in prices[1:]:
        ema = alpha * price + (1 - alpha) * ema

    return round(ema, 2)


def calculate_ma_system(prices: np.ndarray) -> Dict[str, Any]:
    """
    计算完整的均线系统

    返回:
        MA5, MA10, MA20, MA60 及趋势判断
    """
    ma5 = calculate_ma(prices, 5)
    ma10 = calculate_ma(prices, 10)
    ma20 = calculate_ma(prices, 20)
    ma60 = calculate_ma(prices, 60) if len(prices) >= 60 else None

    current_price = prices[-1]

    # 判断均线排列
    if ma5 > ma10 > ma20:
        arrangement = "多头排列"
        trend = "bullish"
    elif ma5 < ma10 < ma20:
        arrangement = "空头排列"
        trend = "bearish"
    else:
        arrangement = "均线缠绕"
        trend = "neutral"

    # 判断价格与均线关系
    above_ma = []
    below_ma = []

    for name, ma in [('MA5', ma5), ('MA10', ma10), ('MA20', ma20)]:
        if current_price > ma:
            above_ma.append(name)
        else:
            below_ma.append(name)

    return {
        'ma5': ma5,
        'ma10': ma10,
        'ma20': ma20,
        'ma60': ma60,
        'arrangement': arrangement,
        'trend': trend,
        'price_above': above_ma,
        'price_below': below_ma,
        'source': 'Local Calculation'
    }


# ============================================
# 成交量分析
# ============================================

def calculate_volume_analysis(
    volume: np.ndarray,
    close: np.ndarray,
    period: int = 20
) -> Dict[str, Any]:
    """
    成交量分析

    分析量价配合关系
    """
    if len(volume) < period:
        return {'error': '数据不足'}

    # 平均成交量
    avg_volume = np.mean(volume[-period:])
    current_volume = volume[-1]

    # 量比 = 当前成交量 / 平均成交量
    volume_ratio = current_volume / avg_volume if avg_volume > 0 else 1

    # 价格变动
    price_change = (close[-1] - close[-2]) / close[-2] * 100 if len(close) > 1 else 0

    # 量价配合判断
    if volume_ratio > 1.5 and price_change > 1:
        pattern = "放量上涨"
        signal = "bullish"
        explanation = "成交量放大配合价格上涨，买盘积极，上涨动能充足"
    elif volume_ratio > 1.5 and price_change < -1:
        pattern = "放量下跌"
        signal = "bearish"
        explanation = "成交量放大配合价格下跌，卖盘涌出，需要警惕"
    elif volume_ratio < 0.7 and price_change > 1:
        pattern = "缩量上涨"
        signal = "neutral"
        explanation = "上涨但成交量萎缩，上涨动能不足，可能是反弹"
    elif volume_ratio < 0.7 and price_change < -1:
        pattern = "缩量下跌"
        signal = "neutral"
        explanation = "下跌但成交量萎缩，卖压减轻，可能接近底部"
    elif volume_ratio > 1.5:
        pattern = "放量震荡"
        signal = "neutral"
        explanation = "成交量放大但价格变化不大，多空博弈激烈"
    else:
        pattern = "量价平稳"
        signal = "neutral"
        explanation = "成交量和价格都在正常范围波动"

    return {
        'current_volume': int(current_volume),
        'avg_volume': int(avg_volume),
        'volume_ratio': round(volume_ratio, 2),
        'pattern': pattern,
        'signal': signal,
        'explanation': explanation,
        'source': 'Local Calculation'
    }


# ============================================
# MACD 本地计算
# ============================================

def calculate_macd(
    prices: np.ndarray,
    fast_period: int = 12,
    slow_period: int = 26,
    signal_period: int = 9
) -> Dict[str, Any]:
    """
    计算 MACD 指标

    返回:
        MACD 线、信号线、柱状图及信号判断
    """
    if len(prices) < slow_period + signal_period:
        return {'error': '数据不足'}

    # 计算 EMA
    def ema(data, period):
        alpha = 2.0 / (period + 1)
        result = [data[0]]
        for i in range(1, len(data)):
            result.append(alpha * data[i] + (1 - alpha) * result[-1])
        return np.array(result)

    ema_fast = ema(prices, fast_period)
    ema_slow = ema(prices, slow_period)

    # MACD 线
    macd_line = ema_fast - ema_slow

    # 信号线
    signal_line = ema(macd_line, signal_period)

    # 柱状图
    histogram = macd_line - signal_line

    # 获取最新值
    latest_macd = float(macd_line[-1])
    latest_signal = float(signal_line[-1])
    latest_hist = float(histogram[-1])
    prev_hist = float(histogram[-2]) if len(histogram) > 1 else 0

    # 判断信号
    if latest_hist > 0 and prev_hist <= 0:
        signal = 'golden_cross'
        interpretation = 'MACD 金叉 - 买入信号'
    elif latest_hist < 0 and prev_hist >= 0:
        signal = 'death_cross'
        interpretation = 'MACD 死叉 - 卖出信号'
    elif latest_hist > 0:
        signal = 'bullish'
        interpretation = 'MACD 多头趋势'
    else:
        signal = 'bearish'
        interpretation = 'MACD 空头趋势'

    return {
        'macd_line': round(latest_macd, 4),
        'signal_line': round(latest_signal, 4),
        'histogram': round(latest_hist, 4),
        'prev_histogram': round(prev_hist, 4),
        'signal': signal,
        'interpretation': interpretation,
        'source': 'Local Calculation'
    }


# ============================================
# KDJ 随机指标
# ============================================

def calculate_kdj(
    high: np.ndarray,
    low: np.ndarray,
    close: np.ndarray,
    n: int = 9,
    m1: int = 3,
    m2: int = 3
) -> Dict[str, Any]:
    """
    计算 KDJ 随机指标

    KDJ 是国内股民最常用的短线指标，用于判断超买超卖。

    参数:
        high: 最高价数组
        low: 最低价数组
        close: 收盘价数组
        n: RSV 周期，默认 9
        m1: K 值平滑周期，默认 3
        m2: D 值平滑周期，默认 3

    返回:
        K, D, J 值及信号判断
    """
    if len(close) < n:
        return {'error': '数据不足'}

    # 计算 RSV (Raw Stochastic Value)
    rsv_list = []
    for i in range(n - 1, len(close)):
        period_high = np.max(high[i - n + 1:i + 1])
        period_low = np.min(low[i - n + 1:i + 1])

        if period_high == period_low:
            rsv = 50.0
        else:
            rsv = (close[i] - period_low) / (period_high - period_low) * 100
        rsv_list.append(rsv)

    rsv_array = np.array(rsv_list)

    # 计算 K 值 (RSV 的 EMA)
    k_values = [50.0]  # 初始值
    for i in range(len(rsv_array)):
        k = (2 * k_values[-1] + rsv_array[i]) / 3  # 平滑系数 1/m1
        k_values.append(k)
    k_values = k_values[1:]  # 移除初始值

    # 计算 D 值 (K 的 EMA)
    d_values = [50.0]
    for i in range(len(k_values)):
        d = (2 * d_values[-1] + k_values[i]) / 3
        d_values.append(d)
    d_values = d_values[1:]

    # 计算 J 值
    j_values = [3 * k - 2 * d for k, d in zip(k_values, d_values)]

    # 获取最新值
    k = k_values[-1]
    d = d_values[-1]
    j = j_values[-1]

    # 获取前一日值（用于判断金叉死叉）
    prev_k = k_values[-2] if len(k_values) > 1 else k
    prev_d = d_values[-2] if len(d_values) > 1 else d

    # 判断信号
    if k > d and prev_k <= prev_d:
        signal = 'golden_cross'
        interpretation = 'KDJ 金叉 - 买入信号'
    elif k < d and prev_k >= prev_d:
        signal = 'death_cross'
        interpretation = 'KDJ 死叉 - 卖出信号'
    elif j > 100:
        signal = 'overbought'
        interpretation = f'KDJ 超买 (J={j:.1f}>100) - 短期可能回调'
    elif j < 0:
        signal = 'oversold'
        interpretation = f'KDJ 超卖 (J={j:.1f}<0) - 短期可能反弹'
    elif k > 80 and d > 80:
        signal = 'high_zone'
        interpretation = 'KDJ 高位钝化 - 注意回调风险'
    elif k < 20 and d < 20:
        signal = 'low_zone'
        interpretation = 'KDJ 低位钝化 - 关注反弹机会'
    else:
        signal = 'neutral'
        interpretation = 'KDJ 中性区间'

    return {
        'k': round(k, 2),
        'd': round(d, 2),
        'j': round(j, 2),
        'signal': signal,
        'interpretation': interpretation,
        'source': 'Local Calculation'
    }


# ============================================
# 背离检测 (Divergence Detection)
# ============================================

def detect_divergence(
    prices: np.ndarray,
    indicator_values: np.ndarray,
    lookback: int = 20
) -> Dict[str, Any]:
    """
    检测价格与指标之间的背离

    背离是强烈的反转信号：
    - 顶背离：价格创新高，指标未创新高 → 看跌
    - 底背离：价格创新低，指标未创新低 → 看涨

    参数:
        prices: 价格数组
        indicator_values: 指标值数组（如 RSI、MACD）
        lookback: 回溯周期，默认 20

    返回:
        背离类型和强度
    """
    if len(prices) < lookback or len(indicator_values) < lookback:
        return {'divergence': None, 'type': 'none'}

    # 取最近的数据
    recent_prices = prices[-lookback:]
    recent_indicator = indicator_values[-lookback:]

    # 找局部高点和低点
    def find_peaks(arr, is_high=True):
        peaks = []
        for i in range(2, len(arr) - 2):
            if is_high:
                if arr[i] > arr[i-1] and arr[i] > arr[i-2] and arr[i] > arr[i+1] and arr[i] > arr[i+2]:
                    peaks.append((i, arr[i]))
            else:
                if arr[i] < arr[i-1] and arr[i] < arr[i-2] and arr[i] < arr[i+1] and arr[i] < arr[i+2]:
                    peaks.append((i, arr[i]))
        return peaks

    price_highs = find_peaks(recent_prices, is_high=True)
    price_lows = find_peaks(recent_prices, is_high=False)
    ind_highs = find_peaks(recent_indicator, is_high=True)
    ind_lows = find_peaks(recent_indicator, is_high=False)

    divergence_type = 'none'
    interpretation = '无明显背离'
    strength = 0

    # 检测顶背离
    if len(price_highs) >= 2 and len(ind_highs) >= 2:
        # 价格新高创新高
        if price_highs[-1][1] > price_highs[-2][1]:
            # 但指标未创新高
            if ind_highs[-1][1] < ind_highs[-2][1]:
                divergence_type = 'bearish'
                strength = abs(ind_highs[-2][1] - ind_highs[-1][1])
                interpretation = '顶背离 - 价格创新高但动能减弱，警惕回调'

    # 检测底背离
    if len(price_lows) >= 2 and len(ind_lows) >= 2:
        # 价格创新低
        if price_lows[-1][1] < price_lows[-2][1]:
            # 但指标未创新低
            if ind_lows[-1][1] > ind_lows[-2][1]:
                divergence_type = 'bullish'
                strength = abs(ind_lows[-1][1] - ind_lows[-2][1])
                interpretation = '底背离 - 价格创新低但动能增强，关注反弹'

    return {
        'divergence': divergence_type,
        'strength': round(strength, 2),
        'interpretation': interpretation,
        'source': 'Local Calculation'
    }


def detect_macd_divergence(
    prices: np.ndarray,
    fast_period: int = 12,
    slow_period: int = 26,
    signal_period: int = 9,
    lookback: int = 30
) -> Dict[str, Any]:
    """检测 MACD 背离"""
    macd_result = calculate_macd(prices, fast_period, slow_period, signal_period)
    if 'error' in macd_result:
        return macd_result

    # 重新计算完整的 MACD 序列
    def ema(data, period):
        alpha = 2.0 / (period + 1)
        result = [data[0]]
        for i in range(1, len(data)):
            result.append(alpha * data[i] + (1 - alpha) * result[-1])
        return np.array(result)

    ema_fast = ema(prices, fast_period)
    ema_slow = ema(prices, slow_period)
    macd_line = ema_fast - ema_slow

    return detect_divergence(prices, macd_line, lookback)


def detect_rsi_divergence(
    prices: np.ndarray,
    period: int = 14,
    lookback: int = 30
) -> Dict[str, Any]:
    """检测 RSI 背离"""
    rsi_series = calculate_rsi_series(prices, period)

    if len(rsi_series) < lookback:
        return {'divergence': None, 'type': 'none'}

    # 对齐价格和 RSI 序列
    aligned_prices = prices[-(len(rsi_series)):]

    return detect_divergence(aligned_prices, rsi_series, lookback)


# ============================================
# 增强版支撑阻力位（含斐波那契）
# ============================================

def calculate_support_resistance_enhanced(
    high: np.ndarray,
    low: np.ndarray,
    close: np.ndarray,
    lookback: int = 60
) -> Dict[str, Any]:
    """
    计算增强版支撑阻力位

    方法：
    1. 近期高低点
    2. 斐波那契回撤位
    3. 整数关口

    参数:
        high: 最高价数组
        low: 最低价数组
        close: 收盘价数组
        lookback: 回溯周期

    返回:
        多级支撑位和阻力位
    """
    if len(close) < lookback:
        lookback = len(close)

    recent_high = high[-lookback:]
    recent_low = low[-lookback:]
    current_price = close[-1]

    # 1. 近期高低点
    period_high = np.max(recent_high)
    period_low = np.min(recent_low)

    # 2. 斐波那契回撤位
    diff = period_high - period_low
    fib_levels = {
        '0.0%': period_low,
        '23.6%': period_low + diff * 0.236,
        '38.2%': period_low + diff * 0.382,
        '50.0%': period_low + diff * 0.500,
        '61.8%': period_low + diff * 0.618,
        '78.6%': period_low + diff * 0.786,
        '100.0%': period_high,
    }

    # 3. 扩展斐波那契（预测突破后目标）
    fib_extensions = {
        '127.2%': period_high + diff * 0.272,
        '161.8%': period_high + diff * 0.618,
        '200.0%': period_high + diff * 1.0,
    }

    # 4. 整数关口（心理价位）
    def find_round_numbers(price, range_pct=0.1):
        """找到价格附近的整数关口"""
        rounds = []
        base = 10 ** (len(str(int(price))) - 1)  # 确定量级

        for multiplier in [1, 5, 10, 50, 100]:
            step = base / 10 * multiplier
            lower = int(price * (1 - range_pct) / step) * step
            upper = int(price * (1 + range_pct) / step) * step + step

            current = lower
            while current <= upper:
                if abs(current - price) / price < range_pct:
                    rounds.append(current)
                current += step

        return sorted(set(rounds))

    round_numbers = find_round_numbers(current_price)

    # 分类支撑位和阻力位
    supports = []
    resistances = []

    # 添加斐波那契位
    for name, level in fib_levels.items():
        if level < current_price:
            supports.append({'price': round(level, 2), 'type': f'Fib {name}', 'strength': 'medium'})
        elif level > current_price:
            resistances.append({'price': round(level, 2), 'type': f'Fib {name}', 'strength': 'medium'})

    # 添加扩展位作为阻力
    for name, level in fib_extensions.items():
        resistances.append({'price': round(level, 2), 'type': f'Fib Ext {name}', 'strength': 'weak'})

    # 标记关键位
    for s in supports:
        if s['type'] in ['Fib 38.2%', 'Fib 50.0%', 'Fib 61.8%']:
            s['strength'] = 'strong'

    for r in resistances:
        if r['type'] in ['Fib 38.2%', 'Fib 50.0%', 'Fib 61.8%']:
            r['strength'] = 'strong'

    # 排序
    supports = sorted(supports, key=lambda x: x['price'], reverse=True)[:5]
    resistances = sorted(resistances, key=lambda x: x['price'])[:5]

    # 找最近的支撑和阻力
    nearest_support = supports[0] if supports else None
    nearest_resistance = resistances[0] if resistances else None

    return {
        'current_price': round(current_price, 2),
        'period_high': round(period_high, 2),
        'period_low': round(period_low, 2),
        'supports': supports,
        'resistances': resistances,
        'nearest_support': nearest_support,
        'nearest_resistance': nearest_resistance,
        'fibonacci': fib_levels,
        'round_numbers': round_numbers[:5],
        'source': 'Local Calculation'
    }


# ============================================
# OBV 量能指标
# ============================================

def calculate_obv(
    close: np.ndarray,
    volume: np.ndarray
) -> Dict[str, Any]:
    """
    计算 OBV (On-Balance Volume) 能量潮

    原理：
    - 上涨日：OBV += 成交量
    - 下跌日：OBV -= 成交量
    - 平盘日：OBV 不变

    用途：
    - OBV 上升 + 价格上升 = 趋势确认
    - OBV 上升 + 价格下跌 = 底背离，可能反转向上
    - OBV 下降 + 价格上升 = 顶背离，可能反转向下
    """
    if len(close) < 2 or len(volume) < 2:
        return {'error': '数据不足'}

    obv = [0]
    for i in range(1, len(close)):
        if close[i] > close[i-1]:
            obv.append(obv[-1] + volume[i])
        elif close[i] < close[i-1]:
            obv.append(obv[-1] - volume[i])
        else:
            obv.append(obv[-1])

    obv = np.array(obv)

    # 计算 OBV 的移动平均
    obv_ma = np.mean(obv[-20:]) if len(obv) >= 20 else np.mean(obv)

    # 判断趋势
    recent_obv = obv[-5:]
    obv_trend = 'up' if recent_obv[-1] > recent_obv[0] else 'down'

    recent_price = close[-5:]
    price_trend = 'up' if recent_price[-1] > recent_price[0] else 'down'

    # 判断信号
    if obv_trend == 'up' and price_trend == 'up':
        signal = 'confirmed_up'
        interpretation = 'OBV 确认上涨 - 量价配合，趋势健康'
    elif obv_trend == 'down' and price_trend == 'down':
        signal = 'confirmed_down'
        interpretation = 'OBV 确认下跌 - 量价配合，趋势延续'
    elif obv_trend == 'up' and price_trend == 'down':
        signal = 'bullish_divergence'
        interpretation = 'OBV 底背离 - 资金悄悄流入，关注反弹'
    elif obv_trend == 'down' and price_trend == 'up':
        signal = 'bearish_divergence'
        interpretation = 'OBV 顶背离 - 资金悄悄流出，警惕回调'
    else:
        signal = 'neutral'
        interpretation = 'OBV 中性'

    return {
        'obv': int(obv[-1]),
        'obv_ma': int(obv_ma),
        'obv_trend': obv_trend,
        'price_trend': price_trend,
        'signal': signal,
        'interpretation': interpretation,
        'source': 'Local Calculation'
    }


# ============================================
# 威廉指标 Williams %R
# ============================================

def calculate_williams_r(
    high: np.ndarray,
    low: np.ndarray,
    close: np.ndarray,
    period: int = 14
) -> Dict[str, Any]:
    """
    计算威廉指标 Williams %R

    与 KDJ 类似，但取值范围 0 到 -100：
    - 0 到 -20: 超买区
    - -80 到 -100: 超卖区
    """
    if len(close) < period:
        return {'error': '数据不足'}

    highest_high = np.max(high[-period:])
    lowest_low = np.min(low[-period:])
    current_close = close[-1]

    if highest_high == lowest_low:
        wr = -50.0
    else:
        wr = (highest_high - current_close) / (highest_high - lowest_low) * -100

    # 判断信号
    if wr > -20:
        signal = 'overbought'
        interpretation = f'威廉指标超买 ({wr:.1f}) - 短期可能回调'
    elif wr < -80:
        signal = 'oversold'
        interpretation = f'威廉指标超卖 ({wr:.1f}) - 短期可能反弹'
    else:
        signal = 'neutral'
        interpretation = f'威廉指标中性 ({wr:.1f})'

    return {
        'williams_r': round(wr, 2),
        'signal': signal,
        'interpretation': interpretation,
        'source': 'Local Calculation'
    }


# ============================================
# 乖离率 BIAS
# ============================================

def calculate_bias(
    close: np.ndarray,
    periods: List[int] = [6, 12, 24]
) -> Dict[str, Any]:
    """
    计算乖离率 BIAS

    乖离率 = (当前价 - MA) / MA × 100%

    用途：
    - 正乖离过大：股价高于均线太多，可能回调
    - 负乖离过大：股价低于均线太多，可能反弹
    """
    result = {}
    signals = []

    for period in periods:
        if len(close) < period:
            continue

        ma = np.mean(close[-period:])
        bias = (close[-1] - ma) / ma * 100

        result[f'bias{period}'] = round(bias, 2)
        result[f'ma{period}'] = round(ma, 2)

        # 判断信号（一般以 6% 为界）
        if bias > 6:
            signals.append(f'BIAS{period} 正乖离过大 ({bias:.1f}%)')
        elif bias < -6:
            signals.append(f'BIAS{period} 负乖离过大 ({bias:.1f}%)')

    # 综合判断
    if any('正乖离过大' in s for s in signals):
        interpretation = '乖离率偏高 - 股价偏离均线过远，注意回调'
        signal = 'overbought'
    elif any('负乖离过大' in s for s in signals):
        interpretation = '乖离率偏低 - 股价偏离均线过远，关注反弹'
        signal = 'oversold'
    else:
        interpretation = '乖离率正常'
        signal = 'neutral'

    result['signal'] = signal
    result['interpretation'] = interpretation
    result['source'] = 'Local Calculation'

    return result


# ============================================
# K线形态识别 (Candlestick Patterns)
# ============================================

def identify_candlestick_patterns(
    open_prices: np.ndarray,
    high: np.ndarray,
    low: np.ndarray,
    close: np.ndarray
) -> Dict[str, Any]:
    """
    识别K线形态

    支持的形态:
    - 锤子线/吊颈线 (Hammer/Hanging Man)
    - 倒锤子/射击之星 (Inverted Hammer/Shooting Star)
    - 吞没形态 (Engulfing)
    - 十字星 (Doji)
    - 早晨之星/黄昏之星 (Morning Star/Evening Star)
    - 三只乌鸦/三白兵 (Three Crows/Three White Soldiers)
    """
    if len(close) < 5:
        return {'patterns': [], 'signal': 'neutral'}

    patterns = []

    # 计算K线实体和影线
    def candle_info(i):
        body = close[i] - open_prices[i]
        body_size = abs(body)
        upper_shadow = high[i] - max(open_prices[i], close[i])
        lower_shadow = min(open_prices[i], close[i]) - low[i]
        total_range = high[i] - low[i]
        is_bullish = close[i] > open_prices[i]
        return {
            'body': body,
            'body_size': body_size,
            'upper_shadow': upper_shadow,
            'lower_shadow': lower_shadow,
            'total_range': total_range,
            'is_bullish': is_bullish,
            'body_ratio': body_size / total_range if total_range > 0 else 0
        }

    # 获取最近几根K线信息
    c0 = candle_info(-1)  # 最新
    c1 = candle_info(-2)  # 前一根
    c2 = candle_info(-3) if len(close) >= 3 else None

    # 判断近期趋势
    recent_trend = 'up' if close[-1] > close[-5] else 'down'
    avg_body = np.mean([abs(close[i] - open_prices[i]) for i in range(-10, -1)])

    # === 1. 十字星 (Doji) ===
    if c0['body_ratio'] < 0.1 and c0['total_range'] > 0:
        if recent_trend == 'up':
            patterns.append({
                'name': '十字星',
                'name_en': 'Doji',
                'type': 'reversal',
                'signal': 'bearish',
                'strength': 'medium',
                'description': '多空平衡，上涨趋势可能转折'
            })
        else:
            patterns.append({
                'name': '十字星',
                'name_en': 'Doji',
                'type': 'reversal',
                'signal': 'bullish',
                'strength': 'medium',
                'description': '多空平衡，下跌趋势可能转折'
            })

    # === 2. 锤子线/吊颈线 (Hammer/Hanging Man) ===
    # 特征：小实体在上方，长下影线(>=实体2倍)，几乎无上影线
    if (c0['lower_shadow'] >= c0['body_size'] * 2 and
        c0['upper_shadow'] < c0['body_size'] * 0.3 and
        c0['body_size'] > avg_body * 0.3):
        if recent_trend == 'down':
            patterns.append({
                'name': '锤子线',
                'name_en': 'Hammer',
                'type': 'reversal',
                'signal': 'bullish',
                'strength': 'strong',
                'description': '下跌中出现，下影线表示多方抵抗，可能反弹'
            })
        else:
            patterns.append({
                'name': '吊颈线',
                'name_en': 'Hanging Man',
                'type': 'reversal',
                'signal': 'bearish',
                'strength': 'medium',
                'description': '上涨中出现，警示上涨动能减弱'
            })

    # === 3. 倒锤子/射击之星 (Inverted Hammer/Shooting Star) ===
    # 特征：小实体在下方，长上影线，几乎无下影线
    if (c0['upper_shadow'] >= c0['body_size'] * 2 and
        c0['lower_shadow'] < c0['body_size'] * 0.3 and
        c0['body_size'] > avg_body * 0.3):
        if recent_trend == 'down':
            patterns.append({
                'name': '倒锤子',
                'name_en': 'Inverted Hammer',
                'type': 'reversal',
                'signal': 'bullish',
                'strength': 'medium',
                'description': '下跌中出现，上影线表示买方尝试，可能反弹'
            })
        else:
            patterns.append({
                'name': '射击之星',
                'name_en': 'Shooting Star',
                'type': 'reversal',
                'signal': 'bearish',
                'strength': 'strong',
                'description': '上涨中出现，上影线表示卖压，可能回调'
            })

    # === 4. 看涨吞没 (Bullish Engulfing) ===
    if (not c1['is_bullish'] and c0['is_bullish'] and
        c0['body_size'] > c1['body_size'] * 1.2 and
        open_prices[-1] < close[-2] and close[-1] > open_prices[-2]):
        patterns.append({
            'name': '看涨吞没',
            'name_en': 'Bullish Engulfing',
            'type': 'reversal',
            'signal': 'bullish',
            'strength': 'strong',
            'description': '阳线完全吞没前一根阴线，强烈反弹信号'
        })

    # === 5. 看跌吞没 (Bearish Engulfing) ===
    if (c1['is_bullish'] and not c0['is_bullish'] and
        c0['body_size'] > c1['body_size'] * 1.2 and
        open_prices[-1] > close[-2] and close[-1] < open_prices[-2]):
        patterns.append({
            'name': '看跌吞没',
            'name_en': 'Bearish Engulfing',
            'type': 'reversal',
            'signal': 'bearish',
            'strength': 'strong',
            'description': '阴线完全吞没前一根阳线，强烈回调信号'
        })

    # === 6. 早晨之星 (Morning Star) ===
    if c2 and len(close) >= 3:
        # 第一根大阴线，第二根小实体（星），第三根大阳线
        if (not candle_info(-3)['is_bullish'] and
            candle_info(-3)['body_size'] > avg_body * 1.2 and
            candle_info(-2)['body_size'] < avg_body * 0.5 and
            c0['is_bullish'] and
            c0['body_size'] > avg_body * 1.2 and
            close[-1] > (open_prices[-3] + close[-3]) / 2):
            patterns.append({
                'name': '早晨之星',
                'name_en': 'Morning Star',
                'type': 'reversal',
                'signal': 'bullish',
                'strength': 'very_strong',
                'description': '经典底部反转形态，强烈买入信号'
            })

    # === 7. 黄昏之星 (Evening Star) ===
    if c2 and len(close) >= 3:
        if (candle_info(-3)['is_bullish'] and
            candle_info(-3)['body_size'] > avg_body * 1.2 and
            candle_info(-2)['body_size'] < avg_body * 0.5 and
            not c0['is_bullish'] and
            c0['body_size'] > avg_body * 1.2 and
            close[-1] < (open_prices[-3] + close[-3]) / 2):
            patterns.append({
                'name': '黄昏之星',
                'name_en': 'Evening Star',
                'type': 'reversal',
                'signal': 'bearish',
                'strength': 'very_strong',
                'description': '经典顶部反转形态，强烈卖出信号'
            })

    # === 8. 三白兵 (Three White Soldiers) ===
    if len(close) >= 3:
        three_bullish = all(close[-i] > open_prices[-i] for i in range(1, 4))
        ascending = close[-1] > close[-2] > close[-3]
        good_body = all(abs(close[-i] - open_prices[-i]) > avg_body * 0.5 for i in range(1, 4))

        if three_bullish and ascending and good_body:
            patterns.append({
                'name': '三白兵',
                'name_en': 'Three White Soldiers',
                'type': 'continuation',
                'signal': 'bullish',
                'strength': 'very_strong',
                'description': '连续三根上涨阳线，强势上涨信号'
            })

    # === 9. 三只乌鸦 (Three Black Crows) ===
    if len(close) >= 3:
        three_bearish = all(close[-i] < open_prices[-i] for i in range(1, 4))
        descending = close[-1] < close[-2] < close[-3]
        good_body = all(abs(close[-i] - open_prices[-i]) > avg_body * 0.5 for i in range(1, 4))

        if three_bearish and descending and good_body:
            patterns.append({
                'name': '三只乌鸦',
                'name_en': 'Three Black Crows',
                'type': 'continuation',
                'signal': 'bearish',
                'strength': 'very_strong',
                'description': '连续三根下跌阴线，强势下跌信号'
            })

    # 确定综合信号
    bullish_count = sum(1 for p in patterns if p['signal'] == 'bullish')
    bearish_count = sum(1 for p in patterns if p['signal'] == 'bearish')

    if bullish_count > bearish_count:
        overall_signal = 'bullish'
    elif bearish_count > bullish_count:
        overall_signal = 'bearish'
    else:
        overall_signal = 'neutral'

    return {
        'patterns': patterns,
        'signal': overall_signal,
        'bullish_count': bullish_count,
        'bearish_count': bearish_count,
        'source': 'Local Calculation'
    }


# ============================================
# 趋势形态识别 (Chart Patterns)
# ============================================

def identify_chart_patterns(
    high: np.ndarray,
    low: np.ndarray,
    close: np.ndarray,
    lookback: int = 60
) -> Dict[str, Any]:
    """
    识别趋势形态

    支持的形态:
    - 双底 (Double Bottom) / W底
    - 双顶 (Double Top) / M顶
    - 头肩顶 (Head and Shoulders)
    - 头肩底 (Inverse Head and Shoulders)
    - 上升三角形 (Ascending Triangle)
    - 下降三角形 (Descending Triangle)
    - 对称三角形 (Symmetric Triangle)
    """
    if len(close) < lookback:
        lookback = len(close)

    if lookback < 20:
        return {'patterns': [], 'signal': 'neutral'}

    patterns = []
    recent_close = close[-lookback:]
    recent_high = high[-lookback:]
    recent_low = low[-lookback:]

    # 找局部极值点
    def find_local_extrema(data, order=5):
        """找局部高点和低点"""
        highs = []
        lows = []
        for i in range(order, len(data) - order):
            if all(data[i] >= data[i-j] for j in range(1, order+1)) and \
               all(data[i] >= data[i+j] for j in range(1, order+1)):
                highs.append((i, data[i]))
            if all(data[i] <= data[i-j] for j in range(1, order+1)) and \
               all(data[i] <= data[i+j] for j in range(1, order+1)):
                lows.append((i, data[i]))
        return highs, lows

    local_highs, local_lows = find_local_extrema(recent_close, order=3)

    # === 1. 双底 (Double Bottom / W底) ===
    # 特征：两个相近的低点，中间有反弹
    if len(local_lows) >= 2:
        for i in range(len(local_lows) - 1):
            low1_idx, low1_val = local_lows[i]
            low2_idx, low2_val = local_lows[i + 1]

            # 两个低点间隔要够远
            if low2_idx - low1_idx < 10:
                continue

            # 两个低点价格相近（差距<3%）
            diff_pct = abs(low1_val - low2_val) / low1_val * 100
            if diff_pct > 3:
                continue

            # 中间有明显反弹
            middle_high = max(recent_close[low1_idx:low2_idx])
            rebound_pct = (middle_high - low1_val) / low1_val * 100

            if rebound_pct > 5:
                # 判断是否已突破颈线
                neckline = middle_high
                current_price = close[-1]

                if current_price > neckline:
                    patterns.append({
                        'name': '双底突破',
                        'name_en': 'Double Bottom Breakout',
                        'type': 'reversal',
                        'signal': 'bullish',
                        'strength': 'very_strong',
                        'neckline': round(neckline, 2),
                        'target': round(neckline + (neckline - low1_val), 2),
                        'description': f'W底形态已突破颈线 ${neckline:.2f}，目标位 ${neckline + (neckline - low1_val):.2f}'
                    })
                else:
                    patterns.append({
                        'name': '双底形成中',
                        'name_en': 'Double Bottom Forming',
                        'type': 'reversal',
                        'signal': 'bullish',
                        'strength': 'medium',
                        'neckline': round(neckline, 2),
                        'description': f'W底形态形成中，关注颈线 ${neckline:.2f} 突破'
                    })
                break

    # === 2. 双顶 (Double Top / M顶) ===
    if len(local_highs) >= 2:
        for i in range(len(local_highs) - 1):
            high1_idx, high1_val = local_highs[i]
            high2_idx, high2_val = local_highs[i + 1]

            if high2_idx - high1_idx < 10:
                continue

            diff_pct = abs(high1_val - high2_val) / high1_val * 100
            if diff_pct > 3:
                continue

            middle_low = min(recent_close[high1_idx:high2_idx])
            pullback_pct = (high1_val - middle_low) / high1_val * 100

            if pullback_pct > 5:
                neckline = middle_low
                current_price = close[-1]

                if current_price < neckline:
                    patterns.append({
                        'name': '双顶跌破',
                        'name_en': 'Double Top Breakdown',
                        'type': 'reversal',
                        'signal': 'bearish',
                        'strength': 'very_strong',
                        'neckline': round(neckline, 2),
                        'target': round(neckline - (high1_val - neckline), 2),
                        'description': f'M顶形态已跌破颈线 ${neckline:.2f}，目标位 ${neckline - (high1_val - neckline):.2f}'
                    })
                else:
                    patterns.append({
                        'name': '双顶形成中',
                        'name_en': 'Double Top Forming',
                        'type': 'reversal',
                        'signal': 'bearish',
                        'strength': 'medium',
                        'neckline': round(neckline, 2),
                        'description': f'M顶形态形成中，关注颈线 ${neckline:.2f} 跌破'
                    })
                break

    # === 3. 头肩顶 (Head and Shoulders) ===
    if len(local_highs) >= 3:
        for i in range(len(local_highs) - 2):
            left_idx, left_val = local_highs[i]
            head_idx, head_val = local_highs[i + 1]
            right_idx, right_val = local_highs[i + 2]

            # 头部最高，两肩相近
            if head_val > left_val and head_val > right_val:
                shoulder_diff = abs(left_val - right_val) / left_val * 100
                if shoulder_diff < 5:
                    # 找颈线（两肩之间的低点）
                    neckline_left = min(recent_close[left_idx:head_idx])
                    neckline_right = min(recent_close[head_idx:right_idx])
                    neckline = (neckline_left + neckline_right) / 2

                    current_price = close[-1]
                    if current_price < neckline:
                        patterns.append({
                            'name': '头肩顶跌破',
                            'name_en': 'Head and Shoulders Breakdown',
                            'type': 'reversal',
                            'signal': 'bearish',
                            'strength': 'very_strong',
                            'neckline': round(neckline, 2),
                            'target': round(neckline - (head_val - neckline), 2),
                            'description': f'头肩顶已跌破颈线，目标位 ${neckline - (head_val - neckline):.2f}'
                        })
                    else:
                        patterns.append({
                            'name': '头肩顶形成中',
                            'name_en': 'Head and Shoulders Forming',
                            'type': 'reversal',
                            'signal': 'bearish',
                            'strength': 'strong',
                            'neckline': round(neckline, 2),
                            'description': f'头肩顶形成中，关注颈线 ${neckline:.2f}'
                        })
                    break

    # === 4. 头肩底 (Inverse Head and Shoulders) ===
    if len(local_lows) >= 3:
        for i in range(len(local_lows) - 2):
            left_idx, left_val = local_lows[i]
            head_idx, head_val = local_lows[i + 1]
            right_idx, right_val = local_lows[i + 2]

            if head_val < left_val and head_val < right_val:
                shoulder_diff = abs(left_val - right_val) / left_val * 100
                if shoulder_diff < 5:
                    neckline_left = max(recent_close[left_idx:head_idx])
                    neckline_right = max(recent_close[head_idx:right_idx])
                    neckline = (neckline_left + neckline_right) / 2

                    current_price = close[-1]
                    if current_price > neckline:
                        patterns.append({
                            'name': '头肩底突破',
                            'name_en': 'Inverse Head and Shoulders Breakout',
                            'type': 'reversal',
                            'signal': 'bullish',
                            'strength': 'very_strong',
                            'neckline': round(neckline, 2),
                            'target': round(neckline + (neckline - head_val), 2),
                            'description': f'头肩底已突破颈线，目标位 ${neckline + (neckline - head_val):.2f}'
                        })
                    else:
                        patterns.append({
                            'name': '头肩底形成中',
                            'name_en': 'Inverse Head and Shoulders Forming',
                            'type': 'reversal',
                            'signal': 'bullish',
                            'strength': 'strong',
                            'neckline': round(neckline, 2),
                            'description': f'头肩底形成中，关注颈线 ${neckline:.2f}'
                        })
                    break

    # === 5. 三角形整理 ===
    # 使用线性回归判断高点和低点趋势
    if len(local_highs) >= 3 and len(local_lows) >= 3:
        high_indices = [h[0] for h in local_highs[-5:]]
        high_values = [h[1] for h in local_highs[-5:]]
        low_indices = [l[0] for l in local_lows[-5:]]
        low_values = [l[1] for l in local_lows[-5:]]

        if len(high_indices) >= 2 and len(low_indices) >= 2:
            # 简单判断趋势
            high_trend = (high_values[-1] - high_values[0]) / (high_indices[-1] - high_indices[0] + 1)
            low_trend = (low_values[-1] - low_values[0]) / (low_indices[-1] - low_indices[0] + 1)

            # 上升三角形：高点水平，低点上升
            if abs(high_trend) < 0.01 * np.mean(high_values) and low_trend > 0.01 * np.mean(low_values):
                resistance = np.mean(high_values)
                if close[-1] > resistance:
                    patterns.append({
                        'name': '上升三角形突破',
                        'name_en': 'Ascending Triangle Breakout',
                        'type': 'continuation',
                        'signal': 'bullish',
                        'strength': 'strong',
                        'resistance': round(resistance, 2),
                        'description': f'上升三角形已突破阻力位 ${resistance:.2f}'
                    })
                else:
                    patterns.append({
                        'name': '上升三角形',
                        'name_en': 'Ascending Triangle',
                        'type': 'continuation',
                        'signal': 'bullish',
                        'strength': 'medium',
                        'resistance': round(resistance, 2),
                        'description': f'上升三角形整理中，关注 ${resistance:.2f} 突破'
                    })

            # 下降三角形：低点水平，高点下降
            elif abs(low_trend) < 0.01 * np.mean(low_values) and high_trend < -0.01 * np.mean(high_values):
                support = np.mean(low_values)
                if close[-1] < support:
                    patterns.append({
                        'name': '下降三角形跌破',
                        'name_en': 'Descending Triangle Breakdown',
                        'type': 'continuation',
                        'signal': 'bearish',
                        'strength': 'strong',
                        'support': round(support, 2),
                        'description': f'下降三角形已跌破支撑位 ${support:.2f}'
                    })
                else:
                    patterns.append({
                        'name': '下降三角形',
                        'name_en': 'Descending Triangle',
                        'type': 'continuation',
                        'signal': 'bearish',
                        'strength': 'medium',
                        'support': round(support, 2),
                        'description': f'下降三角形整理中，关注 ${support:.2f} 跌破'
                    })

            # 对称三角形
            elif high_trend < 0 and low_trend > 0:
                patterns.append({
                    'name': '对称三角形',
                    'name_en': 'Symmetric Triangle',
                    'type': 'continuation',
                    'signal': 'neutral',
                    'strength': 'medium',
                    'description': '对称三角形收敛中，等待方向选择'
                })

    # 确定综合信号
    bullish_count = sum(1 for p in patterns if p['signal'] == 'bullish')
    bearish_count = sum(1 for p in patterns if p['signal'] == 'bearish')

    # 考虑强度权重
    bullish_strength = sum(
        3 if p['strength'] == 'very_strong' else 2 if p['strength'] == 'strong' else 1
        for p in patterns if p['signal'] == 'bullish'
    )
    bearish_strength = sum(
        3 if p['strength'] == 'very_strong' else 2 if p['strength'] == 'strong' else 1
        for p in patterns if p['signal'] == 'bearish'
    )

    if bullish_strength > bearish_strength:
        overall_signal = 'bullish'
    elif bearish_strength > bullish_strength:
        overall_signal = 'bearish'
    else:
        overall_signal = 'neutral'

    return {
        'patterns': patterns,
        'signal': overall_signal,
        'bullish_count': bullish_count,
        'bearish_count': bearish_count,
        'source': 'Local Calculation'
    }


def analyze_patterns(
    open_prices: np.ndarray,
    high: np.ndarray,
    low: np.ndarray,
    close: np.ndarray
) -> Dict[str, Any]:
    """
    综合分析所有形态（K线 + 趋势）
    """
    candlestick = identify_candlestick_patterns(open_prices, high, low, close)
    chart = identify_chart_patterns(high, low, close)

    all_patterns = candlestick['patterns'] + chart['patterns']

    # 按强度排序
    strength_order = {'very_strong': 0, 'strong': 1, 'medium': 2, 'weak': 3}
    all_patterns.sort(key=lambda x: strength_order.get(x.get('strength', 'weak'), 3))

    # 综合判断
    bullish = sum(1 for p in all_patterns if p['signal'] == 'bullish')
    bearish = sum(1 for p in all_patterns if p['signal'] == 'bearish')

    if bullish > bearish:
        overall = 'bullish'
    elif bearish > bullish:
        overall = 'bearish'
    else:
        overall = 'neutral'

    return {
        'candlestick_patterns': candlestick['patterns'],
        'chart_patterns': chart['patterns'],
        'all_patterns': all_patterns,
        'signal': overall,
        'bullish_count': bullish,
        'bearish_count': bearish,
        'source': 'Local Calculation'
    }


# ============================================
# 动态止损计算
# ============================================

def calculate_dynamic_stop_loss(
    current_price: float,
    atr: float,
    atr_multiplier: float = 2.0,
    action: str = 'BUY'
) -> Dict[str, float]:
    """
    基于 ATR 计算动态止损

    参数:
        current_price: 当前价格
        atr: ATR 值
        atr_multiplier: ATR 倍数（波动大的股票用更大倍数）
        action: 操作方向 (BUY/SELL)

    返回:
        止损价、止盈价、风险收益比
    """
    if action == 'BUY':
        # 买入：止损在下方
        stop_loss = current_price - atr * atr_multiplier
        # 止盈通常是止损距离的 2-3 倍
        take_profit = current_price + atr * atr_multiplier * 2.5
    else:
        # 卖出：止损在上方
        stop_loss = current_price + atr * atr_multiplier
        take_profit = current_price - atr * atr_multiplier * 2.5

    # 计算风险收益比
    risk = abs(current_price - stop_loss)
    reward = abs(take_profit - current_price)
    risk_reward_ratio = reward / risk if risk > 0 else 0

    return {
        'stop_loss': round(stop_loss, 2),
        'take_profit': round(take_profit, 2),
        'atr': round(atr, 4),
        'atr_multiplier': atr_multiplier,
        'risk_amount': round(risk, 2),
        'reward_amount': round(reward, 2),
        'risk_reward_ratio': round(risk_reward_ratio, 2)
    }


# ============================================
# 仓位建议计算
# ============================================

def calculate_position_size(
    total_capital: float,
    current_price: float,
    stop_loss: float,
    risk_percent: float = 2.0
) -> Dict[str, Any]:
    """
    计算建议仓位大小

    基于固定风险百分比法则：
    - 每笔交易最多亏损账户总额的 risk_percent%

    参数:
        total_capital: 账户总资金
        current_price: 当前价格
        stop_loss: 止损价
        risk_percent: 单笔最大风险百分比，默认 2%

    返回:
        建议买入股数、仓位占比、最大亏损金额
    """
    # 单笔最大风险金额
    max_risk_amount = total_capital * (risk_percent / 100)

    # 每股风险 = 买入价 - 止损价
    risk_per_share = abs(current_price - stop_loss)

    if risk_per_share == 0:
        return {'error': '止损价不能等于买入价'}

    # 建议股数 = 最大风险金额 / 每股风险
    suggested_shares = int(max_risk_amount / risk_per_share)

    # 需要资金
    required_capital = suggested_shares * current_price

    # 仓位占比
    position_percent = (required_capital / total_capital) * 100

    return {
        'suggested_shares': suggested_shares,
        'required_capital': round(required_capital, 2),
        'position_percent': round(position_percent, 2),
        'max_loss_amount': round(max_risk_amount, 2),
        'risk_per_share': round(risk_per_share, 2),
        'risk_percent': risk_percent
    }


# ============================================
# 综合分析函数
# ============================================

def analyze_stock_local(ticker: str, period: str = '3mo') -> Dict[str, Any]:
    """
    使用本地计算进行完整的股票分析 (v3.4)

    适用于：
    - 港股（Alpha Vantage 不支持）
    - AV API 限流时的备选方案

    返回:
        包含所有指标的完整分析结果
    """
    # 获取数据
    data = get_stock_data(ticker, period)

    if 'error' in data:
        return data

    close = data['close']
    high = data['high']
    low = data['low']
    open_prices = data['open']
    volume = data['volume']
    current_price = data['current_price']

    # === 基础指标 ===
    rsi = calculate_rsi(close)
    bbands = calculate_bollinger_bands(close)
    macd = calculate_macd(close)
    atr = calculate_atr(high, low, close)
    atr_pct = calculate_atr_percent(high, low, close)
    ma_system = calculate_ma_system(close)
    volume_analysis = calculate_volume_analysis(volume, close)

    # === v3.3 新增指标 ===
    kdj = calculate_kdj(high, low, close)
    obv = calculate_obv(close, volume)
    williams = calculate_williams_r(high, low, close)
    bias = calculate_bias(close)
    support_resistance = calculate_support_resistance_enhanced(high, low, close)

    # === 背离检测 ===
    macd_divergence = detect_macd_divergence(close)
    rsi_divergence = detect_rsi_divergence(close)

    # === v3.4 形态识别 ===
    patterns = analyze_patterns(open_prices, high, low, close)

    # 动态止损
    stop_loss_data = calculate_dynamic_stop_loss(current_price, atr, action='BUY')

    return {
        'ticker': ticker.upper(),
        'current_price': current_price,
        'timestamp': datetime.now().isoformat(),
        'source': 'Local Calculation (Yahoo Finance)',
        'indicators': {
            # 基础指标
            'rsi': rsi,
            'bbands': bbands,
            'macd': macd,
            'atr': atr,
            'atr_percent': atr_pct,
            'ma_system': ma_system,
            'volume': volume_analysis,
            # v3.3 新增
            'kdj': kdj,
            'obv': obv,
            'williams_r': williams,
            'bias': bias,
        },
        'support_resistance': support_resistance,
        'divergence': {
            'macd': macd_divergence,
            'rsi': rsi_divergence
        },
        'patterns': patterns,  # v3.4 形态识别
        'stop_loss': stop_loss_data,
        'prices': {
            'close_1m': close[-20:].tolist() if len(close) >= 20 else close.tolist(),
            'close_3m': close.tolist()
        }
    }


if __name__ == "__main__":
    # 测试
    print("测试本地指标计算...")

    # 测试港股
    result = analyze_stock_local("1810.HK")
    if 'error' not in result:
        print(f"\n小米 (1810.HK) 分析结果:")
        print(f"  当前价格: HK${result['current_price']:.2f}")
        print(f"  RSI: {result['indicators']['rsi']}")
        print(f"  布林带: {result['indicators']['bbands']}")
        print(f"  MACD: {result['indicators']['macd']['interpretation']}")
        print(f"  ATR: {result['indicators']['atr']} ({result['indicators']['atr_percent']}%)")
        print(f"  均线排列: {result['indicators']['ma_system']['arrangement']}")
        print(f"  成交量: {result['indicators']['volume']['pattern']}")
        print(f"  动态止损: ${result['stop_loss']['stop_loss']}")
        print(f"  动态止盈: ${result['stop_loss']['take_profit']}")
    else:
        print(f"  错误: {result['error']}")
