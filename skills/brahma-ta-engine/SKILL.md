---
name: ta-engine
description: "梵天全能技术分析引擎——所有技术分析的唯一标准入口。用于手动分析、猎手信号输出、深度报告，保证输出质量稳定一致。"
---

# ta-engine · SKILL.md
# 梵天全能技术分析引擎
# 版本：v1.0 · 2026-05-16 · 指挥官最高指令固化

## 一、技能定位

本技能是梵天进行所有技术分析的唯一标准入口。
无论是手动分析、猎手信号输出、还是深度报告，
全部必须经过本技能的分析流程，保证输出质量稳定一致。

## 二、触发条件

以下任意情况触发本技能：
- 用户请求分析任意币种（分析BTC/分析ETH/深度分析/等）
- 猎手拉娜产生候选信号（进入共振评分阶段）
- 用户请求技术画图、K线解读、趋势判断
- 用户询问支撑/阻力/入场/止损/止盈位
- 梵天主动推送深度分析到钉钉/广场

## 三、标准分析流程（六步）

**必须按序执行，不可跳步。**

### Step 1：定方向（战略层）
参考文件：`references/timeframe_rules.md`
```
- 日线/周线级别判断大趋势
- 确认当前处于：牛市/熊市/震荡
- 定位Elliott浪型位置（第几浪）
- 输出：方向偏多/偏空/中性 + 置信度
```

### Step 2：找结构（战术层）
参考文件：`references/smc_rules.md`
```
- 4H级别识别SMC市场结构
- 标注：BOS/CHoCH结构突破点
- 定位：Order Block（OB）位置
- 标注：FVG（公平价值缺口）
- 标注：流动性猎杀点（等高/等低）
- 输出：关键结构位列表
```

### Step 3：确认形态（执行层）
参考文件：`references/pattern_library.md`
```
- 1H/15分级别识别当前形态
- 判断：三角/箱体/通道/谐波/K线形态
- 计算形态目标价
- 判断突破方向概率
- 输出：形态名 + 目标价 + 有效性
```

### Step 4：机构视角叠加
参考文件：`references/institutional_view.md`
```
- 读取资金费率（正常/异常/极端）
- 分析OI变化（建仓/出货/清算）
- 计算清算带分布（下一个加速点）
- 期权MaxPain位置（若可获取）
- 输出：机构偏向 + 风险提示
```

### Step 5：共振评分
参考文件：`references/analysis_engine.md`
```
- 按150分评分体系逐维度打分
- 计算总分和信号等级
- 确定Kelly倍数
- 生成精确入场参数
- 输出：X/150分 + 等级 + 入场区/止损/止盈
```

### Step 6：格式化输出
```
钉钉1（信号）：
  → 严格使用 references/dd1_format.md 格式
  → 调用 push_hub.py format_signal_dd1()

钉钉2（深度报告）：
  → Markdown格式，含完整六步分析结论
  → 调用 push_hub.py push_dd2()

广场（教育内容）：
  → 版本A/B差异化，教育角度切入
  → 调用 poster.py
```

## 四、分析质量标准

| 等级 | 共振分 | Kelly倍数 | 行动 |
|------|--------|-----------|------|
| 🔴 神级 | 120+ | ×2.0 | 重仓入场 |
| 🟠 极强 | 90~119 | ×1.5 | 标准仓 |
| 🟡 强 | 70~89 | ×1.0 | 轻仓 |
| 🔵 中等 | 50~69 | ×0.5 | 观察 |
| ⚫ 放弃 | <50 | 0 | 不入场 |

## 五、铁律

1. **不跳步**：六步流程必须完整执行
2. **不猜测**：无数据支撑的维度打0分
3. **不强行**：共振分<50直接放弃，不强行找理由入场
4. **不偏离**：钉钉1格式永远使用专属格式，不得修改
5. **不混用**：三渠道格式严格隔离
6. **共振优先**：单一信号再强，没有共振不入场

## 六、参考文件索引

| 文件 | 内容 |
|------|------|
| `references/timeframe_rules.md` | 多时间框架分析规则 |
| `references/smc_rules.md` | SMC结构识别完整规则 |
| `references/pattern_library.md` | 12大门派形态识别库 |
| `references/institutional_view.md` | 机构视角工具库 |
| `references/analysis_engine.md` | 150分共振评分引擎 |
| `references/trader_mindset.md` | 顶级交易员思维框架 |

## 七、代码接口（Phase 1~3 开发）

```python
# 调用示例（未来实现）
from skills.ta_engine.scripts.brahma_brain import BrahmaBrain

brain = BrahmaBrain()
result = brain.analyze('ETHUSDT')

print(result.direction)        # 多/空/中性
print(result.confluence_score) # 0~150
print(result.entry_zone)       # (low, high)
print(result.stop_loss)        # 止损价
print(result.tp1, result.tp2)  # 止盈目标
print(result.signal_grade)     # 神级/极强/强
print(result.dd1_text)         # 钉钉1格式文本
```
