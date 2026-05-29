# Alpha Vantage MCP 工具调用指南

## 目录
- [获取 RSI](#获取-rsi)
- [获取布林带](#获取布林带)
- [获取报价](#获取报价)
- [响应解析](#响应解析)

---

## 获取 RSI

```python
mcp__Alpha-Vantage__TOOL_CALL(
    tool_name="RSI",
    arguments={"symbol": "TSLA", "interval": "daily",
               "time_period": 14, "series_type": "close", "datatype": "json"}
)
```

**参数说明**:
- `symbol`: 股票代码（仅支持美股）
- `interval`: daily / weekly / monthly
- `time_period`: RSI 周期，通常 14
- `series_type`: close / open / high / low

---

## 获取布林带

```python
mcp__Alpha-Vantage__TOOL_CALL(
    tool_name="BBANDS",
    arguments={"symbol": "TSLA", "interval": "daily",
               "time_period": 20, "series_type": "close",
               "nbdevup": 2, "nbdevdn": 2, "datatype": "json"}
)
```

**参数说明**:
- `time_period`: 移动平均周期，通常 20
- `nbdevup`: 上轨标准差倍数，通常 2
- `nbdevdn`: 下轨标准差倍数，通常 2

---

## 获取报价

```python
mcp__Alpha-Vantage__TOOL_CALL(
    tool_name="GLOBAL_QUOTE",
    arguments={"symbol": "AAPL", "datatype": "json"}
)
```

---

## 响应解析

### RSI 响应示例
```json
{
  "Meta Data": {
    "Symbol": "TSLA",
    "Indicator": "Relative Strength Index (RSI)"
  },
  "Technical Analysis: RSI": {
    "2026-01-21": {"RSI": "45.2341"}
  }
}
```

### 布林带响应示例
```json
{
  "Technical Analysis: BBANDS": {
    "2026-01-21": {
      "Real Upper Band": "250.5432",
      "Real Middle Band": "240.1234",
      "Real Lower Band": "229.7036"
    }
  }
}
```

---

## 注意事项

1. **API 限制**: 免费版每天 25 次请求，注意控制调用频率
2. **延时**: 免费版数据有 15 分钟延时
3. **港股不支持**: Alpha Vantage 不支持港股，需使用本地计算
4. **MACD 不支持**: 免费版不支持 MACD，需本地计算
