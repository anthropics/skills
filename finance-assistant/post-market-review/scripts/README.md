# 盘后自动化脚本套件

A股ETF盘后数据自动采集工具，每日收盘后自动运行，生成结构化复盘素材。

## 目录结构

```
 scripts/
├── README.md               # 本文件
├── requirements.txt        # Python 依赖
├── config.py               # 配置文件（ETF列表、路径等）
├── fetch_market_data.py    # 采集大盘数据（成交量/涨跌停）
├── fetch_etf_shares.py     # 采集ETF份额变化
├── fetch_fund_flow.py      # 采集主力资金净流向
├── generate_report.py      # 汇总生成Markdown复盘报告
├── scheduler.py            # 定时任务调度器
├── intraday_check.py        # 午盘一键检查（13:00-15:00）
├── morning_brief.py        # 早盘定性判断（8:00-9:25）
├── run.sh                   # 盘后一键运行（Mac/Linux）
├── run.bat                  # 盘后一键运行（Windows）
└── output/                  # 报告输出目录（自动创建）
    └── YYYY-MM-DD/
        ├── market_data.json
        ├── etf_shares.json
        ├── fund_flow.json
        └── review_YYYY-MM-DD.md
```

## 快速开始

### 1. 安装依赖

```bash
cd d:\skill-collection\finance-assistant\post-market-review\scripts
pip install -r requirements.txt
```

### 2. 配置ETF列表

编辑 `config.py`，填入你持仓的ETF代码：

```python
WATCHLIST_ETFS = ["159770", "588690", "512670", "510880"]
```

### 3. 手动运行（单次测试）

```bash
# 采集今日全部数据并生成报告（一键运行）
python generate_report.py

# 单独运行某个模块
python fetch_market_data.py
python fetch_etf_shares.py
python fetch_fund_flow.py
```

### 4. 盘中/盘前脚本（可选）

```bash
# 午盘一键检查（13:00-15:00 任意时刻）
python intraday_check.py

# 早盘定性判断（8:00-9:25）
python morning_brief.py
```

### 5. 盘后一键运行

```bash
# Mac/Linux
chmod +x run.sh && ./run.sh

# Windows: 双击 run.bat 或在 cmd 中运行
run.bat
```

### 6. 设置定时任务（自动运行）

Windows 任务计划程序（推荐）：

```bash
# 运行调度器脚本，自动注册任务计划
python scheduler.py --install
```

或手动在 Windows 任务计划程序中添加：
- 触发器：每个工作日 15:30
- 程序：`python`
- 参数：`d:\skill-collection\finance-assistant\post-market-review\scripts\generate_report.py`

## 数据源说明

| 数据 | 来源 | 方式 |
|------|------|------|
| 大盘行情 | 新浪财经/东方财富 | HTTP API |
| ETF份额 | 上海证券交易所 | 公开公告解析 |
| 主力资金 | 东方财富 | HTTP API |
| 涨跌停统计 | 新浪财经 | HTTP API |

## 注意事项

- 数据均来自公开免费接口，无需付费订阅
- 建议在15:30之后运行（数据更新完整）
- ETF份额数据通常在17:00前更新完毕
- 所有数据仅用于个人投资研究，请遵守相关法规
