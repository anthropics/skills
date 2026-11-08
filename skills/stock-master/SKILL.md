---
name: stock-master
description: 综合性股票技术分析工具，小白友好。采用混合数据源（Yahoo Finance + Alpha Vantage MCP），提供通俗易懂的分析报告、买卖点建议、Excel持仓管理。支持港股本地计算、ATR动态止损、KDJ随机指标、MACD/RSI背离检测、OBV量能分析、斐波那契支撑阻力位、K线形态识别（锤子线/吞没/十字星）、趋势形态识别（双底/头肩/三角形）。支持飞书多维表格同步。当用户请求股票分析、技术指标、交易建议、持仓分析时激活。
---
# Stock Master v3.5 - 小白友好版

面向普通投资者的技术分析工具，用日常语言解释指标，给出明确买卖建议。

> **GitHub**: https://github.com/EagleF6432614/stock-master
>
> 如果觉得有用，请给个 Star ⭐

## 快速参考

### 数据源策略
| 数据 | 美股 | 港股/A股 |
|------|------|----------|
| 价格 | Yahoo Finance | Yahoo Finance |
| RSI/布林带 | Alpha Vantage MCP | 本地计算 |
| MACD/KDJ/ATR/均线/OBV/形态 | 本地计算 | 本地计算 |

### 指标小白解读

**RSI** (相对强弱):
- <30 超卖 → "大甩卖，可能捡便宜"
- >70 超买 → "被抢购一空，小心回调"

**MACD**:
- 金叉 → "踩油门加速，买入信号"
- 死叉 → "松油门减速，卖出警告"

**KDJ** (随机指标):
- 金叉/J<0 → "绿灯亮了，短期买入"
- 死叉/J>100 → "红灯亮了，短期卖出"

**布林带**:
- 跌破下轨 → "橡皮筋拉太长，可能反弹"
- 突破上轨 → "涨过头了，可能回落"

**背离信号**:
- 底背离 → "价格创新低但动能减弱，反弹信号"
- 顶背离 → "价格创新高但动能减弱，回调信号"

**K线形态** [v3.4]:
- 锤子线/早晨之星/看涨吞没 → 底部反转信号
- 上吊线/黄昏之星/看跌吞没 → 顶部反转信号
- 三只白兵/三只乌鸦 → 强趋势确认

**趋势形态** [v3.4]:
- 双底(W底)/头肩底 → 底部反转，看涨
- 双顶(M头)/头肩顶 → 顶部反转，看跌
- 上升三角形 → 通常向上突破
- 下降三角形 → 通常向下突破

### 交易建议评分 (v3.4)
| 分数 | 建议 | 仓位 |
|------|------|------|
| ≥6 | 强烈买入 | 30% |
| 3-5 | 建议买入 | 20% |
| -2~2 | 观望 | - |
| -3~-5 | 建议卖出 | - |
| ≤-6 | 强烈卖出 | - |

### 形态信号权重 [v3.4]
| 形态类型 | 权重 |
|----------|------|
| 三只白兵/乌鸦、早晨/黄昏之星、头肩、双底双顶 | ±3 |
| 看涨/看跌吞没、上升/下降三角形 | ±2 |
| 锤子线、十字星等单K线形态 | ±1 |

## 使用流程

### 1. 分析单只股票
```
用户: "分析 TSLA" / "看看苹果" / "0700.HK 能买吗"
```

**执行步骤**:
1. 获取 Yahoo Finance 实时价格和历史数据
2. 美股: 调用 Alpha Vantage MCP 获取 RSI/布林带
3. 港股/A股或API失败: 使用 `scripts/indicators.py` 本地计算
4. 计算全部指标 (RSI/MACD/KDJ/OBV/背离/支撑阻力/形态)
5. 调用 `scripts/beginner_analyzer.py` 生成小白友好报告

### 2. 持仓管理
```
用户: "创建持仓表格" / "分析我的持仓" / "更新持仓价格"
```

**Excel 路径**: 可在 `config.json` 中配置，默认为当前目录下的 `my_portfolio.xlsx`

### 3. 对比多只股票
```
用户: "对比 AAPL 和 GOOGL" / "这几只哪个好: TSLA, NVDA"
```

### 4. 飞书同步 [v3.5]
```
用户: "同步分析结果到飞书" / "更新飞书持仓"
```

**飞书多维表格配置**: 请在 `feishu_config.json` 中配置你的飞书应用凭证和表格 ID。

**同步逻辑**: 本地分析 → 飞书（单向，飞书为主库）

## 配置说明

使用前请创建 `config.json` 文件（参考 `config.example.json`）：

```json
{
  "portfolio_path": "./my_portfolio.xlsx",
  "feishu_config_path": "./feishu_config.json"
}
```

## 风险提示（必须包含）

每份报告必须包含:
1. 仅供参考，不构成投资建议
2. 股市有风险，投资需谨慎
3. 建议分批建仓，设置止损

## 详细文档

- 投资智慧与哲学: [references/investment-wisdom.md](references/investment-wisdom.md)
- Excel 持仓管理: [references/portfolio-guide.md](references/portfolio-guide.md)
- 飞书同步指南: [references/feishu-guide.md](references/feishu-guide.md)
- MCP 工具调用: [references/mcp-tools.md](references/mcp-tools.md)
- 脚本详细说明: [references/scripts-guide.md](references/scripts-guide.md)
- 更新日志: [references/changelog.md](references/changelog.md)

## 许可证

MIT License - 详见 [LICENSE](LICENSE)
