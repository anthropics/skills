# 数据工程与数据管线

> 数据是 AI 模型的"食粮"——垃圾进垃圾出，数据质量决定模型质量。

## 📚 本章概述

高质量的训练数据是大语言模型成功的基石。本章覆盖 AI 训练数据的全生命周期：从数据采集、清洗、去重、标注，到合成数据生成、版本管理和合规治理。掌握这些数据工程实践，是构建竞争力模型的关键能力。

### 学习目标

- 理解 AI 训练数据的完整生命周期
- 掌握大规模数据清洗和去重技术（MinHash/SimHash/SemDeDup）
- 了解数据标注平台和质量控制方法
- 掌握合成数据生成的技术和最佳实践
- 了解数据版本管理（DVC/LakeFS）
- 理解数据合规要求（GDPR/CCPA/版权）

### 前置知识

- 基本的 Python 编程能力
- 了解 NLP 基础概念（tokenization 等）
- 基本的数据处理经验

---

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|--------------|
| 01 | [数据生命周期](01-data-lifecycle.md) | AI 训练数据全流程、数据飞轮、数据是新石油 | 20 分钟 |
| 02 | [数据采集与清洗](02-data-collection-cleaning.md) | Web 爬取、Common Crawl、去重（MinHash/SimHash）、质量过滤 | 40 分钟 |
| 03 | [数据标注](03-data-labeling.md) | 标注平台、主动学习、人机协同标注、质量控制 | 30 分钟 |
| 04 | [合成数据](04-synthetic-data.md) | LLM 生成训练数据、Self-Instruct、Evol-Instruct、质量验证 | 35 分钟 |
| 05 | [数据版本管理](05-data-versioning.md) | DVC、LakeFS、数据血缘追踪、可复现训练 | 25 分钟 |
| 06 | [数据合规](06-data-compliance.md) | 版权问题、PII 检测/脱敏、GDPR/CCPA、数据许可证 | 30 分钟 |

---

## 🗺️ 知识地图

```
                      数据工程与数据管线
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
   ┌────▼────┐        ┌────▼─────┐        ┌────▼────┐
   │ 数据获取 │        │ 数据处理  │        │ 数据治理 │
   └────┬────┘        └────┬─────┘        └────┬────┘
        │                  │                   │
   ┌────▼────┐       ┌────┴────┐          ┌────▼────┐
   │数据采集 │  ┌────▼───┐┌───▼────┐     │版本管理 │
   │Web爬取  │  │清洗去重││标注     │     │DVC      │
   │Common   │  │MinHash ││Label   │     │LakeFS   │
   │Crawl    │  └────────┘│Studio  │     └────┬────┘
   └────┬────┘            └────────┘          │
        │                                ┌────▼────┐
   ┌────▼────┐                           │数据合规 │
   │合成数据 │                           │GDPR/PII │
   │Self-Inst│                           └─────────┘
   └─────────┘
```

---

## 🎯 学习路径建议

### 路径 A：快速入门（1 小时）
1. [数据生命周期](01-data-lifecycle.md) - 全貌概览
2. [数据采集与清洗](02-data-collection-cleaning.md) - 核心概念
3. [数据合规](06-data-compliance.md) - 必知合规要求

### 路径 B：深入学习（3 小时）
1. 按顺序阅读所有文档
2. 实践数据清洗和去重
3. 尝试合成数据生成

---

## 🔗 相关章节

- **上一章**：[11-ai-safety-alignment](../11-ai-safety-alignment/) - AI 安全与对齐
- **下一章**：[13-finetuning-adaptation](../13-finetuning-adaptation/) - 微调与适配
- **相关**：[04-mlops-llmops/10-data-management](../04-mlops-llmops/10-data-management.md) - MLOps 数据管理概述

---

## 📚 延伸阅读

- [The Pile: An 800GB Dataset of Diverse Text](https://pile.eleuther.ai/)
- [RedPajama: Open Dataset for Training LLMs](https://github.com/togethercomputer/RedPajama-Data)
- [DVC Documentation](https://dvc.org/doc)
- 论文: *Scaling Data-Constrained Language Models* (2023)
- 论文: *Textbooks Are All You Need* (Phi-1, 2023)
