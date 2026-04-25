# AI 安全与对齐

> 能力越大，责任越大——训练一个强大的模型只是开始，让它安全、可信、对齐人类价值观才是真正的挑战。

## 📚 本章概述

AI 安全与对齐是确保大语言模型在部署后行为符合人类意图和价值观的关键工程领域。本章覆盖对齐技术（RLHF/DPO）、安全防护（Guardrails）、红队测试、安全评估基准和负责任 AI 框架，从基础设施角度讲解如何构建安全的 AI 系统。

### 学习目标

- 理解 AI 对齐的核心概念和必要性
- 掌握 RLHF/DPO/KTO 等对齐训练方法及其基础设施需求
- 了解红队测试的方法论和工具
- 掌握 Guardrails 系统的设计和部署
- 能够进行系统化的 AI 安全评估
- 理解负责任 AI 的法规合规要求

### 前置知识

- 了解 LLM 的基本原理（推荐先阅读 [00-training-fundamentals](../00-training-fundamentals/)）
- 基本的强化学习概念（奖励、策略）
- 了解模型微调的基本流程

---

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|--------------|
| 01 | [对齐概述](01-alignment-overview.md) | AI 对齐的定义、必要性、对齐税、安全 vs 能力的平衡 | 20 分钟 |
| 02 | [RLHF 与 DPO](02-rlhf-dpo.md) | 人类反馈强化学习全流程、奖励模型、PPO/DPO/KTO 对比、基础设施需求 | 40 分钟 |
| 03 | [红队测试](03-red-teaming.md) | 攻击向量分类、Prompt Injection、越狱技术、自动化红队工具 | 30 分钟 |
| 04 | [Guardrails 实践](04-guardrails.md) | NeMo Guardrails、Llama Guard、内容过滤、输入输出安全检测 | 35 分钟 |
| 05 | [安全评估](05-safety-evaluation.md) | TruthfulQA/BBQ/ToxiGen 评估基准、安全评分、持续监控 | 25 分钟 |
| 06 | [负责任 AI](06-responsible-ai.md) | 伦理框架、偏见检测、可解释性、EU AI Act 等法规合规 | 30 分钟 |

---

## 🗺️ 知识地图

```
                      AI 安全与对齐
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
   ┌────▼────┐        ┌────▼─────┐        ┌────▼────┐
   │ 对齐技术 │        │ 防护体系  │        │ 治理合规 │
   └────┬────┘        └────┬─────┘        └────┬────┘
        │                  │                   │
   ┌────▼────┐       ┌────┴────┐          ┌────▼────┐
   │RLHF/DPO│  ┌────▼───┐┌───▼────┐     │负责任AI │
   │对齐训练 │  │红队测试││Guardrails│    │法规合规 │
   └────┬────┘  └────────┘└────────┘     └────┬────┘
        │                                     │
   ┌────▼────┐                           ┌────▼────┐
   │安全评估 │                           │偏见检测 │
   │基准测试 │                           │可解释性 │
   └─────────┘                           └─────────┘
```

---

## 🎯 学习路径建议

### 路径 A：快速入门（1 小时）
1. [对齐概述](01-alignment-overview.md)
2. [Guardrails 实践](04-guardrails.md)
3. [安全评估](05-safety-evaluation.md) 概述部分

### 路径 B：深入学习（3 小时）
1. 按顺序阅读所有文档
2. 重点关注 RLHF/DPO 的基础设施需求
3. 实践 Guardrails 部署

### 路径 C：专题深入
- **对齐工程**：[01-对齐概述](01-alignment-overview.md) + [02-RLHF/DPO](02-rlhf-dpo.md)
- **安全防护**：[03-红队测试](03-red-teaming.md) + [04-Guardrails](04-guardrails.md)
- **合规治理**：[05-安全评估](05-safety-evaluation.md) + [06-负责任 AI](06-responsible-ai.md)

---

## 🔗 相关章节

- **上一章**：[10-ai-networking](../10-ai-networking/) - AI 网络基础设施
- **下一章**：[12-data-engineering](../12-data-engineering/) - 数据工程
- **相关**：[04-mlops-llmops/11-ai-safety-guardrails](../04-mlops-llmops/11-ai-safety-guardrails.md) - MLOps 中的安全概述
- **相关**：[13-finetuning-adaptation](../13-finetuning-adaptation/) - 微调与适配

---

## 📚 延伸阅读

- [Anthropic Research on AI Safety](https://www.anthropic.com/research)
- [OpenAI Safety & Alignment](https://openai.com/safety)
- [NIST AI Risk Management Framework](https://www.nist.gov/artificial-intelligence)
- 论文: *Training language models to follow instructions with human feedback* (InstructGPT)
- 论文: *Direct Preference Optimization* (DPO)
