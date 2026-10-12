# Stock Master - 小白友好的股票技术分析工具

[![GitHub stars](https://img.shields.io/github/stars/EagleF6432614/stock-master?style=social)](https://github.com/EagleF6432614/stock-master)
[![GitHub forks](https://img.shields.io/github/forks/EagleF6432614/stock-master?style=social)](https://github.com/EagleF6432614/stock-master/fork)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

面向普通投资者的技术分析工具，用日常语言解释复杂指标，给出明确买卖建议。

## 特性

- **小白友好**: 用通俗语言解释 RSI、MACD、KDJ 等指标
- **混合数据源**: Yahoo Finance (实时) + Alpha Vantage MCP (专业指标)
- **多市场支持**: 美股、港股、A股
- **持仓管理**: Excel 表格管理，自动计算盈亏
- **飞书同步**: 支持同步到飞书多维表格
- **形态识别**: K线形态 + 趋势形态自动识别

## 安装方式

### 方式一：Claude Code Marketplace（推荐）

在 Claude Code 中运行：
```bash
# 1. 添加 marketplace
/plugin marketplace add EagleF6432614/stock-master

# 2. 安装 skill
/plugin install stock-master@stock-master-marketplace
```

安装后直接使用：
```
分析 AAPL 股票
```

### 方式二：手动安装

将仓库克隆到 Claude skills 目录：
```bash
git clone https://github.com/EagleF6432614/stock-master.git ~/.claude/skills/stock-master
```

---

## 快速开始

### 1. 安装依赖

```bash
pip install -r requirements.txt
```

### 2. 配置 Alpha Vantage MCP (可选)

在 Claude Code 中添加 MCP 服务器：

```bash
claude mcp add Alpha-Vantage --transport http --url "https://mcp.alphavantage.co/mcp?apikey=YOUR_API_KEY"
```

> 获取免费 API Key: https://www.alphavantage.co/support/#api-key

### 3. 作为 Claude Skill 使用

将此目录复制到 `~/.claude/skills/stock-master`，然后在 Claude Code 中：

```
用户: 分析 AAPL 股票
用户: 看看特斯拉能买吗
用户: 对比 NVDA 和 AMD
```

## 配置说明

### 基础配置

复制配置模板：

```bash
cp config.example.json config.json
cp feishu_config.example.json feishu_config.json  # 如需飞书同步
```

编辑 `config.json`：

```json
{
  "portfolio_path": "./my_portfolio.xlsx",
  "feishu_config_path": "./feishu_config.json"
}
```

### 飞书配置 (可选)

如需同步到飞书多维表格，编辑 `feishu_config.json`：

```json
{
  "APP_ID": "cli_xxx",
  "APP_SECRET": "xxx",
  "APP_TOKEN": "xxx",
  "TABLE_ID": "tblxxx"
}
```

> 详细配置指南: [飞书开放平台文档](https://open.feishu.cn/document/server-docs/docs/bitable-v1/bitable-overview)

## 支持的指标

| 指标 | 数据源 | 说明 |
|------|--------|------|
| RSI | Alpha Vantage / 本地 | 相对强弱指数 |
| MACD | 本地计算 | 趋势动量指标 |
| KDJ | 本地计算 | 随机指标 |
| 布林带 | Alpha Vantage / 本地 | 波动区间 |
| OBV | 本地计算 | 量能指标 |
| ATR | 本地计算 | 动态止损 |
| 斐波那契 | 本地计算 | 支撑阻力位 |

## 形态识别

### K线形态
- 锤子线、上吊线
- 看涨/看跌吞没
- 早晨之星、黄昏之星
- 三只白兵、三只乌鸦
- 十字星

### 趋势形态
- 双底 (W底)、双顶 (M头)
- 头肩底、头肩顶
- 上升三角形、下降三角形

## 交易建议评分

| 分数 | 建议 | 仓位 |
|------|------|------|
| ≥6 | 强烈买入 | 30% |
| 3-5 | 建议买入 | 20% |
| -2~2 | 观望 | - |
| -3~-5 | 建议卖出 | - |
| ≤-6 | 强烈卖出 | - |

## 项目结构

```
stock-master/
├── SKILL.md                    # Claude Skill 定义
├── README.md                   # 本文件
├── LICENSE                     # MIT 许可证
├── requirements.txt            # Python 依赖
├── config.example.json         # 配置模板
├── feishu_config.example.json  # 飞书配置模板
├── scripts/
│   ├── main.py                 # 主分析器
│   ├── indicators.py           # 技术指标计算
│   ├── beginner_analyzer.py    # 小白友好报告生成
│   ├── portfolio.py            # 持仓管理
│   ├── feishu_sync.py          # 飞书同步
│   └── feishu_init_tables.py   # 飞书表结构初始化
└── references/
    ├── investment-wisdom.md    # 投资智慧与哲学
    ├── portfolio-guide.md      # Excel 持仓管理指南
    ├── feishu-guide.md         # 飞书同步详细指南
    ├── mcp-tools.md            # MCP 工具使用指南
    ├── scripts-guide.md        # 脚本详细说明
    └── changelog.md            # 更新日志
```

## 详细文档

| 文档 | 说明 |
|------|------|
| [投资智慧](references/investment-wisdom.md) | 股民十大境界、交易原则、心态修炼 |
| [持仓管理](references/portfolio-guide.md) | Excel 持仓表格使用指南 |
| [飞书同步](references/feishu-guide.md) | 飞书多维表格配置与同步 |
| [MCP 工具](references/mcp-tools.md) | Alpha Vantage API 调用指南 |

## 风险提示

> **免责声明**: 本工具仅供学习和参考，不构成投资建议。
>
> - 股市有风险，投资需谨慎
> - 技术分析不能保证盈利
> - 请根据自身情况做出决策

## 贡献

欢迎提交 Issue 和 Pull Request！

## 许可证

MIT License - 详见 [LICENSE](LICENSE)

## 致谢

- [yfinance](https://github.com/ranaroussi/yfinance) - Yahoo Finance 数据
- [Alpha Vantage](https://www.alphavantage.co/) - 专业技术指标
- [Claude Code](https://claude.ai) - AI 编程助手

---

如果觉得有用，请给个 Star ⭐ 支持一下！
