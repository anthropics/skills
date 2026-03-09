# 微调与适配

> 微调是让通用大模型变成"专科医生"的过程——不需要从医学院重新培训，只需要在专业领域深入实习即可。

## 📚 本章概述

大语言模型的预训练赋予了模型通用的语言理解和生成能力，但要让模型在特定领域或任务上表现出色，微调（Fine-tuning）是关键步骤。本章系统讲解从全量微调到参数高效微调（PEFT）的技术演进，涵盖 LoRA 家族、监督微调流程、对齐训练基础设施、主流微调平台，以及生产级微调的最佳实践。

### 学习目标

完成本章学习后，你将能够：

- 理解全量微调与参数高效微调的区别和适用场景
- 掌握 LoRA/QLoRA/DoRA 等技术的原理和实践
- 独立完成 SFT 监督微调全流程
- 了解 RLHF/DPO 对齐训练的基础设施需求
- 选择合适的微调平台和框架
- 应用微调最佳实践，避免常见陷阱

### 前置知识

- 了解 Transformer 架构基础（参考 [00-training-fundamentals](../00-training-fundamentals/README.md)）
- 熟悉分布式训练基本概念（参考 [02-distributed-training](../02-distributed-training/README.md)）
- 了解推理部署基础（参考 [03-inference-serving](../03-inference-serving/README.md)）

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|-------------|
| 01 | [微调概述](01-finetuning-overview.md) | 全量微调 vs PEFT、微调 vs RAG vs Prompt Engineering 决策树、技术演进 | 25 分钟 |
| 02 | [LoRA 家族](02-lora-family.md) | LoRA 低秩分解原理、QLoRA、DoRA、LoRA+、适配器合并策略 | 35 分钟 |
| 03 | [SFT 流程](03-sft-pipeline.md) | 监督微调全流程：数据准备、训练配置、Chat Template、评估方法 | 30 分钟 |
| 04 | [对齐训练基础设施](04-alignment-training.md) | RLHF/DPO 训练的硬件需求、TRL/OpenRLHF 框架、奖励模型训练 | 30 分钟 |
| 05 | [微调平台](05-finetuning-platforms.md) | Axolotl、LLaMA-Factory、Unsloth、AutoTrain、云上微调服务对比 | 25 分钟 |
| 06 | [微调最佳实践](06-finetuning-best-practices.md) | 超参数调优、过拟合防护、灾难性遗忘、评估验证、成本优化 | 30 分钟 |

## 🗺️ 知识地图

```
微调与适配
│
├── 基础概念 ─────────────────────────────────────────────────────
│   ├── 全量微调 (Full Fine-tuning)
│   │   └── 更新所有参数 → 高性能但高成本
│   ├── 参数高效微调 (PEFT)
│   │   ├── LoRA 家族 → 低秩适配器
│   │   ├── Prefix Tuning → 虚拟前缀
│   │   └── Adapter → 插入适配层
│   └── 决策框架
│       ├── Fine-tuning → 需要深度定制
│       ├── RAG → 需要最新知识
│       └── Prompt Engineering → 快速原型
│
├── 核心技术 ─────────────────────────────────────────────────────
│   ├── LoRA 原理
│   │   ├── 低秩分解：W = W₀ + BA
│   │   ├── QLoRA：4-bit 量化 + LoRA
│   │   ├── DoRA：权重分解 + 方向适配
│   │   └── LoRA 合并：多适配器管理
│   ├── 监督微调 (SFT)
│   │   ├── 数据格式：指令/对话数据集
│   │   ├── Chat Template：角色标记
│   │   ├── 训练配置：学习率/批大小/轮次
│   │   └── 评估：基准测试 + 人工评估
│   └── 对齐训练
│       ├── RLHF：SFT → RM → PPO
│       ├── DPO：直接偏好优化
│       └── 基础设施需求：多模型并行
│
├── 工具生态 ─────────────────────────────────────────────────────
│   ├── 框架与库
│   │   ├── PEFT (HuggingFace) → LoRA 实现
│   │   ├── TRL → 对齐训练
│   │   └── DeepSpeed → 大规模微调
│   ├── 微调平台
│   │   ├── Axolotl → 配置化微调
│   │   ├── LLaMA-Factory → 一站式平台
│   │   ├── Unsloth → 2x 加速
│   │   └── AutoTrain → 零代码微调
│   └── 云服务
│       ├── AWS SageMaker
│       ├── Google Vertex AI
│       └── Azure ML / Together AI
│
└── 最佳实践 ─────────────────────────────────────────────────────
    ├── 数据策略
    │   ├── 质量 > 数量
    │   ├── 数据多样性
    │   └── 数据去污染
    ├── 训练策略
    │   ├── 学习率调度
    │   ├── 梯度累积
    │   └── 过拟合检测
    └── 评估策略
        ├── 基准测试
        ├── 人工评估
        └── A/B 测试
```

## 🎯 学习路径建议

### 路径 A：快速上手（入门者）

```
01-微调概述 → 02-LoRA 家族（前半部分） → 03-SFT 流程 → 05-微调平台
```

适合：有基本深度学习知识，想快速实现第一个微调任务的开发者。

### 路径 B：深入掌握（进阶者）

```
01-微调概述 → 02-LoRA 家族（完整） → 03-SFT 流程 → 04-对齐训练 → 06-最佳实践
```

适合：需要在生产环境部署微调模型，关注性能优化和质量保障的工程师。

### 路径 C：全栈微调工程师

```
按顺序完整学习 01-06，结合实际项目练习
```

适合：负责端到端微调管线建设的 AI 基础设施工程师。

## 🔗 相关章节

| 章节 | 关联内容 |
|------|----------|
| [00-训练基础](../00-training-fundamentals/README.md) | Transformer 架构、训练循环 |
| [02-分布式训练](../02-distributed-training/README.md) | 大规模微调的并行策略 |
| [03-推理部署](../03-inference-serving/README.md) | 微调模型的部署 |
| [04-MLOps](../04-mlops-llmops/README.md) | 微调流水线管理 |
| [11-AI 安全与对齐](../11-ai-safety-alignment/README.md) | RLHF/DPO 的安全视角 |
| [12-数据工程](../12-data-engineering/README.md) | 微调数据准备 |

## 📚 延伸阅读

- [LoRA: Low-Rank Adaptation of Large Language Models](https://arxiv.org/abs/2106.09685) - Hu et al., 2021
- [QLoRA: Efficient Finetuning of Quantized LLMs](https://arxiv.org/abs/2305.14314) - Dettmers et al., 2023
- [Direct Preference Optimization (DPO)](https://arxiv.org/abs/2305.18290) - Rafailov et al., 2023
- [PEFT Library Documentation](https://huggingface.co/docs/peft)
- [TRL Documentation](https://huggingface.co/docs/trl)
- [Axolotl GitHub](https://github.com/OpenAccess-AI-Collective/axolotl)
- [LLaMA-Factory GitHub](https://github.com/hiyouga/LLaMA-Factory)

---

*上一章：[12-数据工程](../12-data-engineering/README.md)* | *下一章：[14-AI 编译器与可观测性](../14-compiler-observability/README.md)*
