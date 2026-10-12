# 分布式训练详解

> 大模型无法在单卡上训练，分布式训练是唯一出路。

## 📚 本章概述

随着模型规模从百万参数增长到千亿参数，单卡显存和算力已无法满足训练需求。分布式训练通过将计算和存储分散到多个设备，使大模型训练成为可能。

### 学习目标

- 理解分布式训练的必要性和三大瓶颈
- 掌握数据并行、模型并行、流水线并行的原理
- 学会使用 PyTorch DDP、FSDP、DeepSpeed
- 理解 ZeRO 优化器的三个阶段
- 掌握 3D 并行的配置方法

### 前置知识

- GPU 硬件基础知识
- PyTorch 基本用法
- 深度学习训练流程

---

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|--------------|
| 01 | [为什么需要分布式训练](01-why-distributed.md) | 三大瓶颈分析、解决方案概述 | 15 分钟 |
| 02 | [并行策略总览](02-parallelism-overview.md) | 四种并行方式对比、组合策略 | 20 分钟 |
| 03 | [数据并行详解](03-data-parallelism.md) | DDP 原理、ZeRO 三阶段、FSDP | 40 分钟 |
| 04 | [模型并行详解](04-model-parallelism.md) | 张量并行原理、列切分与行切分 | 30 分钟 |
| 05 | [流水线并行详解](05-pipeline-parallelism.md) | 按层切分、GPipe、1F1B 调度 | 30 分钟 |
| 06 | [3D 并行实践](06-3d-parallelism.md) | Megatron-LM、DeepSpeed 配置 | 35 分钟 |
| 07 | [训练框架对比](07-training-frameworks.md) | DDP/DeepSpeed/Megatron 选择 | 25 分钟 |
| 08 | [通信优化](08-communication-optimization.md) | 集合通信、NCCL、通信重叠 | 30 分钟 |
| 09 | [Checkpoint 与容错](09-checkpoint-fault-tolerance.md) | 保存策略、分片、弹性训练 | 25 分钟 |
| 10 | [序列并行详解](10-sequence-parallelism.md) | Megatron SP、DeepSpeed Ulysses、Ring Attention | 30 分钟 |
| 11 | [专家并行与 MoE](11-expert-parallelism-moe.md) | MoE 原理、Expert Parallelism、负载均衡 | 35 分钟 |
| 12 | [混合精度训练](12-mixed-precision-training.md) | FP16/BF16/FP8、Loss Scaling、Transformer Engine | 30 分钟 |
| 13 | [AdamW 优化器深入讲解](13-adamw-optimizer.md) | SGD→Adam→AdamW 演化、解耦权重衰减、显存开销 | 25 分钟 |
| 14 | [激活重计算](14-activation-checkpointing.md) | 用计算换显存、全量/选择性/分段策略、FSDP/DeepSpeed 集成 | 25 分钟 |
| 15 | [大规模训练网络架构](15-network-architecture.md) | RoCE vs InfiniBand、RDMA 原理、网络拓扑设计、GPUDirect、带宽规划 | 35 分钟 |
| 16 | [分布式数据加载与预处理](16-data-loading-pipeline.md) | DataLoader 优化、WebDataset、Mosaic Streaming、NVIDIA DALI | 30 分钟 |

---

## 🗺️ 知识地图

```
                        分布式训练
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
   ┌────▼────┐        ┌─────▼─────┐       ┌────▼────┐
   │ 为什么   │        │ 并行策略   │       │ 工程实践 │
   │ 需要     │        │           │       │         │
   └────┬────┘        └─────┬─────┘       └────┬────┘
        │                   │                   │
   三大瓶颈           ┌─────┼─────┐        ┌────┼────┐
   • 显存             │     │     │        │         │
   • 计算        ┌────▼──┐ ▼    ▼     训练框架   通信优化
   • 数据        │数据并行│模型并行 流水线       │         │
                │      │       │          Checkpoint
                └──┬───┴───┬───┘             容错
                   │       │
                3D 并行    │
                   │  ┌────┴────┐
                   │  │ 序列并行 │
                   │  │ MoE/EP  │
                   │  │ 混合精度 │
                   │  │ 激活重计算│
                   │  └─────────┘
```

---

## 🎯 学习路径建议

### 路径 A：快速入门（1.5 小时）

1. [为什么需要分布式训练](01-why-distributed.md)
2. [并行策略总览](02-parallelism-overview.md)
3. [数据并行详解](03-data-parallelism.md)
4. [训练框架对比](07-training-frameworks.md)

### 路径 B：深入学习（6 小时）

按顺序阅读所有文档，重点关注：
- ZeRO 三阶段的内存优化原理
- 张量并行在 Transformer 中的实现
- 3D 并行的配置方法
- 序列并行与超长上下文训练
- MoE 架构与专家并行
- 混合精度训练（BF16/FP8）

### 路径 C：按需查阅

- **内存优化**：[03-数据并行](03-data-parallelism.md)（ZeRO/FSDP）
- **大模型训练**：[06-3D并行](06-3d-parallelism.md)
- **超长序列**：[10-序列并行](10-sequence-parallelism.md)
- **MoE 模型**：[11-专家并行](11-expert-parallelism-moe.md)
- **精度优化**：[12-混合精度](12-mixed-precision-training.md)
- **显存优化**：[14-激活重计算](14-activation-checkpointing.md)
- **框架选型**：[07-训练框架](07-training-frameworks.md)

---

## 💡 核心概念速览

### 并行策略对比

| 并行方式 | 切分维度 | 解决问题 | 通信开销 |
|----------|----------|----------|----------|
| **数据并行** | Batch | 加速计算 | AllReduce 梯度 |
| **张量并行** | 隐藏层 | 显存不足 | 每层 AllReduce |
| **流水线并行** | 层 | 显存不足 | 相邻阶段传输 |
| **序列并行** | 序列 | 长序列显存 | AllGather |

### ZeRO 显存优化

| 阶段 | 切分内容 | 每 GPU 显存 |
|------|----------|------------|
| Stage 0 | 无 | M + G + O |
| Stage 1 | 优化器状态 | M + G + O/N |
| Stage 2 | + 梯度 | M + G/N + O/N |
| Stage 3 | + 参数 | M/N + G/N + O/N |

### 框架选择建议

| 模型规模 | 推荐框架 |
|----------|----------|
| < 10B | PyTorch DDP/FSDP |
| 10B - 100B | DeepSpeed ZeRO-3 |
| > 100B | Megatron-LM + DeepSpeed |

---

## 🔗 相关章节

- **前置**：[01-gpu-hardware](../01-gpu-hardware/) - GPU 硬件基础
- **后续**：[03-inference-serving](../03-inference-serving/) - 推理部署
- **相关**：[05-cluster-scheduling](../05-cluster-scheduling/) - 集群调度

---

## 📚 延伸阅读

### 必读论文

- [Megatron-LM](https://arxiv.org/abs/1909.08053) - 模型并行经典
- [ZeRO](https://arxiv.org/abs/1910.02054) - 内存优化革命
- [GPipe](https://arxiv.org/abs/1811.06965) - 流水线并行

### 官方文档

- [PyTorch Distributed](https://pytorch.org/docs/stable/distributed.html)
- [DeepSpeed Documentation](https://www.deepspeed.ai/)
- [Megatron-LM GitHub](https://github.com/NVIDIA/Megatron-LM)
