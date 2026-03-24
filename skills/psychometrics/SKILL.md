---
name: psychometrics
description: Psychometric review checklist for validating personality assessment systems against academic standards. Use when reviewing construct validity, reliability, cross-framework mapping, confidence calibration, or ethical boundaries of personality assessment engines and signal dictionaries.
license: Complete terms in LICENSE.txt
---

# /psychometrics — 心理测量学审查

> 用于审查 EnneaMe 多维人格评估系统的心理测量学合规性。

## 使用方式

```
/psychometrics [审查对象]
```

示例：
- `/psychometrics big-five-signal-dictionary` — 审查 Big Five 信号字典的构念效度
- `/psychometrics bayesian-engine` — 审查贝叶斯推断引擎的测量信度
- `/psychometrics enneagram-bigfive-mapping` — 审查跨框架先验映射的学术基础

## 审查维度

### 1. 构念效度（Construct Validity）
- 我们提取的信号是否真正测量了目标构念？
- 信号定义是否与原始量表（NEO-PI-R、MBTI Form M）的维度定义一致？
- facet 级别的定义是否足够精确，避免维度交叉污染？

### 2. 信度（Reliability）
- 测试-重测信度：同一用户在不同对话中是否得到一致结果？
- 内部一致性：同一维度的多个信号之间是否相关？
- LLM 信号提取的评估者间信度（inter-rater reliability）：不同 LLM 是否提取相同信号？

### 3. 框架间映射合理性
- Enneagram → Big Five 先验映射是否有文献支撑？
- 引用的研究样本量是否足够（N > 200）？
- 映射关系是统计相关还是因果关系？（只应做相关推断）

### 4. 置信度校准
- 贝叶斯后验的置信度是否与实际准确度校准？
- 多少信号点后才应展示结果？
- 是否需要设置最低 confidence 阈值？

### 5. 伦理与边界
- 产品是否明确声明"这不是临床诊断工具"？
- 是否避免了对用户的标签化伤害？
- 用户是否可以对推断结果提出异议/修正？

## 关键学术参考

| 框架 | 核心量表 | 关键文献 |
|------|---------|---------|
| Big Five | NEO-PI-R (Costa & McCrae 1992) | McCrae et al. 2005 (跨文化验证) |
| MBTI | Form M (Myers & Briggs) | Pittenger 1993 (批评性综述) |
| Enneagram | RHETI v2.5 (Riso & Hudson) | Wagner & Walker 1983 |
| VIA | VIA-IS (Peterson & Seligman 2004) | Park et al. 2006 |

## 审查产出物

产出 `psychometrics-review-{subject}.md` 文件，包含：
1. 各维度的合规/不合规评估（pass / warning / fail）
2. 具体问题描述和修正建议
3. 需要补充的文献引用
4. 信号字典/引擎设计的修改建议

## 审查标准

| 等级 | 含义 |
|------|------|
| Pass | 符合心理测量学标准，可直接使用 |
| Warning | 有潜在问题，建议修正后使用 |
| Fail | 严重违反测量学原则，必须修正 |
