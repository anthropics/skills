# 脚本详细说明 v3.4

## 目录
- [main.py - 主协调器](#mainpy---主协调器)
- [beginner_analyzer.py - 小白分析模块](#beginner_analyzerpy---小白分析模块)
- [indicators.py - 本地指标计算](#indicatorspy---本地指标计算)
- [portfolio.py - 持仓管理](#portfoliopy---持仓管理)

---

## main.py - 主协调器

混合数据源架构的核心协调器。

### 数据源策略
| 数据 | 来源 | 原因 |
|------|------|------|
| 实时价格 | Yahoo Finance | 接近实时，无请求限制 |
| MACD | Yahoo + 本地计算 | AV 免费版不支持 |
| RSI | Alpha Vantage MCP | 官方预计算，准确 |
| 布林带 | Alpha Vantage MCP | 官方预计算，准确 |
| KDJ/OBV/背离/形态 | 本地计算 | AV 不提供 |

---

## beginner_analyzer.py - 小白分析模块

用通俗语言解释技术指标。

### 小白解读函数
| 函数 | 功能 |
|------|------|
| `explain_rsi_simple()` | RSI 通俗解释 |
| `explain_macd_simple()` | MACD 通俗解释 |
| `explain_bollinger_simple()` | 布林带通俗解释 |
| `explain_volume_simple()` | 成交量通俗解释 |
| `explain_ma_simple()` | 均线通俗解释 |
| `explain_atr_simple()` | ATR 波动性解释 |
| `explain_kdj_simple()` | KDJ 通俗解释 |
| `explain_divergence_simple()` | 背离信号解释 |
| `explain_obv_simple()` | OBV 量能解释 |
| `explain_williams_simple()` | 威廉指标解释 |
| `explain_bias_simple()` | 乖离率解释 |
| `explain_support_resistance_simple()` | 支撑阻力位解释 |
| `explain_candlestick_pattern_simple()` | [v3.4] K线形态解释 |
| `explain_chart_pattern_simple()` | [v3.4] 趋势形态解释 |
| `explain_patterns_simple()` | [v3.4] 综合形态解释 |

### 报告生成
| 函数 | 功能 |
|------|------|
| `generate_trading_recommendation()` | 综合交易建议 (含评分) |
| `format_simple_report()` | 简洁版报告 |
| `format_detailed_report()` | 详细版报告 |

### 评分规则 (v3.4)
| 分数范围 | 建议 |
|----------|------|
| ≥6 | 强烈买入 |
| 3-5 | 建议买入 |
| -2~2 | 观望 |
| -3~-5 | 建议卖出 |
| ≤-6 | 强烈卖出 |

### 评分权重
| 信号类型 | 权重 | 说明 |
|----------|------|------|
| 背离信号 | ±4 | 最强信号 |
| 强形态信号 | ±3 | [v3.4] 三只白兵/乌鸦、早晨/黄昏之星、头肩、双底双顶 |
| 金叉/死叉 | ±3 | 强信号 |
| 中等形态 | ±2 | [v3.4] 吞没、三角形 |
| 超买/超卖 | ±2~3 | 中强信号 |
| 弱形态/趋势确认 | ±1~2 | 辅助信号 |

---

## indicators.py - 本地指标计算

支持港股和 API 降级时的本地计算。

### 基础指标函数
| 函数 | 功能 |
|------|------|
| `calculate_rsi()` | 计算 RSI |
| `calculate_bollinger_bands()` | 计算布林带 |
| `calculate_macd()` | 计算 MACD |
| `calculate_atr()` | 计算 ATR |
| `calculate_ma_system()` | 计算均线系统 |
| `calculate_volume_analysis()` | 成交量分析 |

### v3.3 新增指标函数
| 函数 | 功能 |
|------|------|
| `calculate_kdj()` | KDJ 随机指标 |
| `calculate_obv()` | OBV 能量潮 |
| `calculate_williams_r()` | 威廉指标 |
| `calculate_bias()` | 乖离率 |
| `detect_divergence()` | 通用背离检测 |
| `detect_macd_divergence()` | MACD 背离检测 |
| `detect_rsi_divergence()` | RSI 背离检测 |
| `calculate_support_resistance_enhanced()` | 增强版支撑阻力位 |

### v3.4 形态识别函数
| 函数 | 功能 |
|------|------|
| `identify_candlestick_patterns()` | K线形态识别 |
| `identify_chart_patterns()` | 趋势形态识别 |
| `analyze_patterns()` | 综合形态分析 |

### K线形态识别
| 形态 | 信号 | 强度 |
|------|------|------|
| 三只白兵 | 看涨 | 非常强 |
| 三只乌鸦 | 看跌 | 非常强 |
| 早晨之星 | 看涨 | 强 |
| 黄昏之星 | 看跌 | 强 |
| 看涨吞没 | 看涨 | 强 |
| 看跌吞没 | 看跌 | 强 |
| 锤子线 | 看涨 | 中 |
| 上吊线 | 看跌 | 中 |
| 十字星 | 中性 | 弱 |

### 趋势形态识别
| 形态 | 信号 | 说明 |
|------|------|------|
| 双底(W底) | 看涨 | 经典底部反转 |
| 双顶(M头) | 看跌 | 经典顶部反转 |
| 头肩底 | 看涨 | 可靠底部反转 |
| 头肩顶 | 看跌 | 可靠顶部反转 |
| 上升三角形 | 看涨 | 通常向上突破 |
| 下降三角形 | 看跌 | 通常向下突破 |
| 对称三角形 | 中性 | 等待突破方向 |

### 支撑阻力位计算方法
1. **近期高低点** - 60日内最高最低
2. **斐波那契回撤** - 23.6%, 38.2%, 50%, 61.8%, 78.6%
3. **斐波那契扩展** - 127.2%, 161.8%, 200%
4. **整数关口** - 心理价位

### 综合分析
```python
analyze_stock_local(ticker, period='3mo')
```
返回所有指标的完整分析结果，包括：
- 基础指标 (RSI/MACD/布林带/ATR/均线/成交量)
- v3.3 新增 (KDJ/OBV/威廉/乖离率)
- 支撑阻力位 (斐波那契)
- 背离检测 (MACD/RSI)
- v3.4 形态识别 (K线形态/趋势形态)
- 动态止损建议

---

## portfolio.py - 持仓管理

Excel 持仓表管理。

### 核心函数
| 函数 | 功能 |
|------|------|
| `create_portfolio_template()` | 创建 Excel 模板 |
| `read_portfolio()` | 读取持仓数据 |
| `update_portfolio_prices()` | 更新实时价格 |
| `update_trading_recommendations()` | 更新交易建议表 |
| `format_portfolio_summary()` | 格式化持仓汇总 |

### 股票代码格式
- 美股: `AAPL`, `TSLA`, `GOOGL`
- 港股: `0700.HK`, `9988.HK`
- A股: `600519.SS` (上海), `000001.SZ` (深圳)

---

## feishu_sync.py - 飞书多维表格同步 [v3.5]

将分析结果同步到飞书多维表格。

### 核心类
| 类 | 功能 |
|------|------|
| `FeishuBitable` | 飞书多维表格 API 封装 |

### 同步函数
| 函数 | 功能 |
|------|------|
| `sync_stock_signal()` | 同步股票技术信号（覆盖更新） |
| `sync_holding()` | 同步持仓数据（覆盖更新） |
| `sync_trade_record()` | 同步交易记录（追加模式） |
| `batch_sync_signals()` | 批量同步多只股票 |
| `quick_sync_signal()` | 快速同步（一行调用） |
| `test_connection()` | 测试飞书连接 |

### 飞书表结构
| 表名 | Table ID | 用途 |
|------|----------|------|
| 数据表 | tbldtKCoANcpvitS | 技术信号 |
| 持仓管理 | tblHkx30pGT1QzOq | 持仓记录 |
| 交易记录 | tblTnlPDFmr5gmSV | 交易历史 |

### 使用示例
```python
from feishu_sync import FeishuBitable, sync_stock_signal

bitable = FeishuBitable()
sync_stock_signal(bitable, {
    'ticker': 'AAPL',
    'score': 5,
    'action': '建议买入',
    ...
})
```

---

## feishu_init_tables.py - 表结构初始化

一键初始化飞书多维表格结构。

### 函数
| 函数 | 功能 |
|------|------|
| `init_signal_table()` | 初始化技术信号表字段 |
| `create_holdings_table()` | 创建持仓管理表 |
| `create_trades_table()` | 创建交易记录表 |
| `init_all_tables()` | 一键初始化所有表 |
