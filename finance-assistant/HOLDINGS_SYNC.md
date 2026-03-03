# 📡 持仓同步方案说明

> 此文档说明如何将东方财富的实际持仓数据同步到 `config.py`，供盘前/盘中/盘后三个 SKILL 自动调用

---

## 方案对比速览

| 方案 | 费用 | 自动化程度 | 安全性 | 实现难度 | 推荐指数 |
|------|------|----------|--------|---------|---------|
| **① CSV 导出解析**（当前） | 免费 | 半自动（每日一次手动导出） | ⭐⭐⭐ 最安全 | ⭐ 最简单 | ✅✅ **首选** |
| **② easytrader 驱动客户端** | 免费 | 全自动 | ⭐⭐ 有风险 | ⭐⭐⭐ 中等 | ⚠️ 可选 |
| **③ Web API 逆向（Cookie）** | 免费 | 全自动 | ⭐ 账号安全风险 | ⭐⭐⭐⭐ 复杂 | ❌ 不推荐 |
| **④ Choice 官方量化 API** | ~3万/年 | 全自动 | ⭐⭐⭐ 官方 | ⭐⭐ 中等 | 💰 机构用 |

---

## ✅ 方案一：CSV 导出 + 自动解析（推荐）

### 第一步：从东方财富导出持仓 CSV

**PC 客户端方式**（推荐）：
```
打开东方财富证券客户端
→ 顶部菜单"资金账户" 或 "交易"
→ 点击"持仓"标签页
→ 在持仓列表上右键 → "导出数据" / "导出到 Excel/CSV"
→ 选择保存位置（建议存到 Downloads 文件夹）
```

**网页版方式**：
```
登录 https://trade.eastmoney.com/
→ 持仓页面 → 点击"导出"按钮
```

### 第二步：运行同步脚本

```bash
cd d:\skill-collection\finance-assistant

# 自动搜索 Downloads/桌面 中最新的持仓 CSV
python sync_holdings.py

# 或者指定文件路径
python sync_holdings.py --file "C:\Users\你的用户名\Downloads\持仓20260302.csv"

# 仅预览，不修改 config.py
python sync_holdings.py --preview
```

### 脚本输出示例

```
🔄 东方财富持仓同步工具
=============================================
✅ 使用文件：C:\Users\Admin\Downloads\持仓20260302.csv
   文件时间：2026-03-02 15:35

⚙️  解析持仓数据...
✅ 解析到 23 个 ETF 持仓

=================================================================
  📊 持仓快照  共 23 只 ETF  总市值 ¥   358,420.00
=================================================================
  代码       名称             数量         市值      盈亏%
  ------------------------------------------------------------
  159715   稀土ETF        20,000    ¥  45,200.00   +12.30%
  562800   稀有金属       15,000    ¥  38,850.00    +8.75%
  512710   军工龙头       30,000    ¥  35,100.00    +5.20%
  ...
=================================================================

✅ config.py WATCHLIST_ETFS 和 ETF_NAME_MAP 已更新
✅ 持仓快照已保存：reports/2026-03-02-holdings-snapshot.json
```

### 生成的持仓快照 JSON 格式

每次同步后会在 `reports/` 目录生成一个快照文件，供分析报告调用：

```json
{
  "date": "2026-03-02",
  "synced_at": "2026-03-02T15:35:12",
  "source": "eastmoney_csv_export",
  "total_market_value": 358420.00,
  "holdings": [
    {
      "code": "159715",
      "name": "稀土ETF",
      "quantity": 20000,
      "market_val": 45200.00,
      "cost": 1.85,
      "profit_pct": 12.30
    }
  ]
}
```

---

## ⚠️ 方案二：easytrader 自动化（进阶）

> 适合希望盘后自动触发同步、无需手动操作的用户

### 安装

```bash
pip install easytrader
```

### 使用方式

```python
# 需要本地打开东方财富客户端并已登录
import easytrader

user = easytrader.use('eastmoney')   # 东方财富证券
user.connect('东方财富客户端路径')   # 通常是 C:\...\EMT.exe

# 获取持仓（含市值、数量、成本）
positions = user.position
# 返回格式：[{'证券代码': '159715', '证券名称': '稀土ETF', '持仓数量': 20000, '参考市值': 45200, ...}]

# 获取余额
balance = user.balance
```

### 注意事项

- ⚠️ 需要本地客户端保持登录状态
- ⚠️ 客户端 UI 更新后可能失效（需维护）
- ⚠️ 部分券商会检测自动化行为，有极小概率触发风控
- ✅ 如决定使用，建议只用于读取持仓，**不要用于自动下单**

---

## 建议的日常操作流程

```
每日 15:00 （收盘后）
    ↓
打开东方财富客户端 → 导出持仓 CSV（30秒）
    ↓
运行：python sync_holdings.py（自动）
    ↓
config.py 和持仓快照 JSON 自动更新
    ↓
17:00 盘后脚本自动运行：取到最新持仓进行复盘分析
```

---

## 快照文件调用方式

盘前/盘后分析脚本可以直接读取最新快照：

```python
import json, os, glob
from config import REPORTS_DIR

# 获取最新的持仓快照
snapshots = sorted(glob.glob(os.path.join(REPORTS_DIR, "*-holdings-snapshot.json")))
if snapshots:
    with open(snapshots[-1]) as f:
        holdings = json.load(f)
    total_val = holdings["total_market_value"]
    print(f"最近持仓市值：¥{total_val:,.2f}（{holdings['date']}）")
```
