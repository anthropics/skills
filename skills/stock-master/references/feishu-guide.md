# 飞书多维表格同步指南

Stock Master 支持将分析结果同步到飞书多维表格，实现云端管理。

## 功能概览

- **技术信号同步**：股票分析结果实时同步
- **持仓管理**：云端管理持仓数据
- **交易记录**：记录每次买卖操作
- **多端访问**：手机、电脑随时查看

## 前置准备

### 1. 创建飞书应用

1. 访问 [飞书开放平台](https://open.feishu.cn/)
2. 创建企业自建应用
3. 获取 `App ID` 和 `App Secret`

### 2. 配置应用权限

在应用的"权限管理"中添加以下权限：
- `bitable:app` - 多维表格应用权限
- `bitable:app:readonly` - 读取多维表格

### 3. 创建多维表格

1. 在飞书中创建新的多维表格
2. 记录 `App Token`（在表格 URL 中）

**URL 格式**：
```
https://xxx.feishu.cn/base/xxxxAPP_TOKENxxxx?table=tblXXXX
```

## 配置文件

创建 `feishu_config.json`：

```json
{
  "APP_ID": "cli_xxxxxxxxx",
  "APP_SECRET": "xxxxxxxxxxxxxxxx",
  "APP_TOKEN": "xxxxxxxxxxxxxxxx",
  "TABLE_ID": "tblXXXXXXXXXX"
}
```

| 字段 | 说明 | 获取方式 |
|------|------|----------|
| APP_ID | 应用 ID | 开放平台 → 应用凭证 |
| APP_SECRET | 应用密钥 | 开放平台 → 应用凭证 |
| APP_TOKEN | 多维表格 Token | 表格 URL 中获取 |
| TABLE_ID | 默认数据表 ID | 表格 URL 的 table 参数 |

## 初始化表结构

运行初始化脚本创建标准表结构：

```bash
python scripts/feishu_init_tables.py
```

或在 Claude 中说：
```
初始化飞书表格
```

### 自动创建的表

#### 1. 技术信号表

| 字段 | 类型 | 说明 |
|------|------|------|
| 股票代码 | 文本 | 股票代码 |
| 股票名称 | 文本 | 公司名称 |
| 当前价格 | 数字 | 最新价格 |
| 综合评分 | 数字 | -10 到 +10 |
| 操作建议 | 单选 | 强烈买入/建议买入/观望/建议卖出/强烈卖出 |
| RSI | 数字 | RSI 指标值 |
| MACD信号 | 单选 | 金叉/多头/空头/死叉 |
| KDJ信号 | 单选 | 金叉/超卖/中性/超买/死叉 |
| 背离信号 | 单选 | 无/底背离/顶背离 |
| 形态信号 | 多选 | 识别到的形态 |
| 止损价 | 数字 | 建议止损价 |
| 止盈价 | 数字 | 建议止盈价 |
| 分析理由 | 文本 | 详细分析理由 |
| 更新时间 | 日期 | 最后更新时间 |

#### 2. 持仓管理表

| 字段 | 类型 | 说明 |
|------|------|------|
| 股票代码 | 文本 | 股票代码 |
| 股票名称 | 文本 | 公司名称 |
| 市场 | 单选 | 美股/港股/A股 |
| 持仓数量 | 数字 | 持有股数 |
| 成本价 | 数字 | 买入均价 |
| 当前价 | 数字 | 最新价格 |
| 市值 | 数字 | 持仓市值 |
| 盈亏金额 | 数字 | 浮动盈亏 |
| 盈亏比例 | 数字 | 盈亏百分比 |
| 买入日期 | 日期 | 建仓日期 |
| 备注 | 文本 | 备注信息 |

#### 3. 交易记录表

| 字段 | 类型 | 说明 |
|------|------|------|
| 股票代码 | 文本 | 股票代码 |
| 交易类型 | 单选 | 买入/卖出/做T买/做T卖 |
| 交易价格 | 数字 | 成交价格 |
| 交易数量 | 数字 | 成交数量 |
| 交易金额 | 数字 | 成交金额 |
| 交易时间 | 日期 | 成交时间 |
| 触发信号 | 文本 | 触发交易的信号 |
| 备注 | 文本 | 交易备注 |

## 使用命令

### 同步分析结果
```
分析 AAPL 并同步到飞书
```

### 同步持仓
```
同步持仓到飞书
```

### 记录交易
```
记录交易：买入 TSLA 10股 @ $400
```

### 查看飞书数据
```
查看飞书持仓
```

## 同步逻辑

### 数据流向
```
本地分析 ────────────→ 飞书多维表格
         （单向同步）
```

### 更新规则
- **技术信号**：按股票代码更新，已存在则覆盖
- **持仓数据**：按股票代码更新，已存在则覆盖
- **交易记录**：始终追加，不覆盖

## API 使用示例

### Python 代码调用

```python
from scripts.feishu_sync import FeishuBitable, sync_stock_signal

# 初始化连接
bitable = FeishuBitable()

# 同步信号
signal_data = {
    'ticker': 'AAPL',
    'name': '苹果',
    'current_price': 185.5,
    'score': 5,
    'action': 'BUY',
    'rsi': 45.2,
    'macd_signal': '金叉',
    'reasons': ['RSI 超卖', 'MACD 金叉']
}
sync_stock_signal(bitable, signal_data)

# 测试连接
from scripts.feishu_sync import test_connection
result = test_connection()
print(result)
```

### 快速同步

```python
from scripts.feishu_sync import quick_sync_signal

quick_sync_signal({
    'ticker': 'TSLA',
    'score': -3,
    'action': 'SELL',
    'rsi': 75,
    'reasons': ['RSI 超买']
})
```

## 常见问题

### Q: 提示 "获取 token 失败"
A: 检查 APP_ID 和 APP_SECRET 是否正确，应用是否已发布。

### Q: 提示 "无权限访问"
A:
1. 检查应用权限是否已添加
2. 检查多维表格是否已授权给应用
3. 在表格设置中添加应用为协作者

### Q: 字段类型不匹配
A: 运行 `python scripts/feishu_init_tables.py` 重新初始化表结构。

### Q: 如何查看 Table ID？
A: 在飞书表格 URL 中：
```
https://xxx.feishu.cn/base/APP_TOKEN?table=TABLE_ID
```

## 安全建议

1. **不要提交配置文件**：`feishu_config.json` 已在 `.gitignore` 中
2. **定期轮换密钥**：建议定期更换 APP_SECRET
3. **最小权限原则**：只授予必要的权限

---

*如有问题，欢迎在 GitHub 提 Issue！*
