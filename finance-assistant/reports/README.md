# 📁 Finance Assistant · 分析报告归档中心

> **归档范围**：盘前晨报 / 盘中监控 / 盘后复盘  
> **更新频率**：每个交易日自动归档  
> **目录维护**：每次新报告生成后，更新下方的报告索引

---

## 📐 文件命名规范

| SKILL | 文件命名格式 | 示例 |
|-------|-------------|------|
| 盘前晨报（pre-market-briefing） | `YYYY-MM-DD-pre-market.md` | `2026-03-02-pre-market.md` |
| 盘中监控（intraday-monitor） | `YYYY-MM-DD-intraday.md` | `2026-03-02-intraday.md` |
| 盘后复盘（post-market-review） | `YYYY-MM-DD-post-market.md` | `2026-03-02-post-market.md` |

**规则说明**：
- 日期格式统一使用 `YYYY-MM-DD`（ISO 8601），方便按时间排序
- 后缀使用英文类型标识，区分三类报告
- 同一交易日的三份报告共享日期前缀，便于按日聚合查阅
- 非交易日（周末/节假日）不生成文件

---

## 📂 目录结构

```
finance-assistant/
├── reports/                        ← 📁 本目录：所有报告归档
│   ├── README.md                   ← 本索引文件
│   ├── 2026-03-02-pre-market.md    ← 盘前晨报
│   ├── 2026-03-02-intraday.md      ← 盘中监控记录
│   ├── 2026-03-02-post-market.md   ← 盘后复盘
│   └── ...
├── pre-market-briefing/
│   └── SKILL.md
├── intraday-monitor/
│   └── SKILL.md
└── post-market-review/
    └── SKILL.md
```

---

## 📋 报告文件头部规范

每份报告文件须包含以下 YAML frontmatter 头部：

```yaml
---
date: YYYY-MM-DD
type: pre-market | intraday | post-market
market_tone: 偏强 | 震荡 | 偏弱
score: XX        # 综合定调评分（盘前/盘后适用）
tags: [两会, 中东, AI, 稀土]   # 当日核心主题标签（最多5个）
---
```

---

## 📊 报告归档索引

> 最新报告在最上方，时间倒序排列

### 2026年3月

| 日期 | 盘前晨报 | 盘中监控 | 盘后复盘 | 定调 | 核心主题 |
|------|---------|---------|---------|------|---------|
| 2026-03-02 | [📋 盘前](./2026-03-02-pre-market.md) | — | — | 🟡 震荡偏多 | 两会+中东+能源+军工稀土 |

---

*索引每次新增报告后手动同步更新，或在盘后复盘时统一补充。*
