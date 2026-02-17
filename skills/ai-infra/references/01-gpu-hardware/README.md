# GPU/硬件基础详解

> GPU 是 AI 计算的核心引擎，理解硬件架构才能写出高效的 AI 代码。

## 📚 本章概述

GPU (Graphics Processing Unit) 最初为图形渲染设计，但其大规模并行计算能力使其成为深度学习的核心硬件。本章将从底层原理出发，帮助你理解为什么 GPU 适合 AI 计算，以及如何充分利用 GPU 的能力。

### 学习目标

- 理解 CPU 与 GPU 的设计哲学差异
- 掌握 NVIDIA GPU 架构的核心概念
- 学会 CUDA 编程的基本模型
- 了解内存层次结构及优化策略
- 掌握 Tensor Core 的原理和使用方法
- 理解多卡互联技术的选型

### 前置知识

- 基本的计算机体系结构知识
- Python 编程基础
- 了解神经网络的基本概念

---

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|--------------|
| 01 | [为什么需要 GPU](01-why-gpu.md) | CPU vs GPU 设计哲学、AI 对 GPU 的需求分析、计算特性对比 | 15 分钟 |
| 02 | [GPU 架构演进](02-architecture-evolution.md) | 从 Volta 到 Blackwell 的架构时间线、关键规格对比、性能飞跃原因 | 20 分钟 |
| 03 | [NVIDIA GPU 架构详解](03-nvidia-architecture.md) | GPU 层次结构、SM 详解、Warp 执行模型 | 30 分钟 |
| 04 | [CUDA 编程模型](04-cuda-programming.md) | 基本概念映射、核函数编写、关键优化技术 | 45 分钟 |
| 05 | [内存层次结构](05-memory-hierarchy.md) | 内存金字塔、HBM 详解、内存优化策略 | 30 分钟 |
| 06 | [Tensor Core 详解](06-tensor-core.md) | MMA 操作、数据类型支持、使用方法、Transformer Engine | 30 分钟 |
| 07 | [多卡互联技术](07-multi-gpu-interconnect.md) | PCIe/NVLink/NVSwitch/InfiniBand 对比和架构详解 | 25 分钟 |
| 08 | [硬件选型指南](08-hardware-selection.md) | 场景选择、考量因素、显存需求估算、成本分析 | 20 分钟 |

---

## 🗺️ 知识地图

```
                           GPU/硬件基础
                                │
        ┌───────────────────────┼───────────────────────┐
        │                       │                       │
   ┌────▼────┐            ┌─────▼─────┐           ┌────▼────┐
   │ 为什么   │            │ 架构原理   │           │ 实践应用 │
   │ 需要GPU  │            │           │           │         │
   └────┬────┘            └─────┬─────┘           └────┬────┘
        │                       │                       │
   ┌────▼────┐            ┌─────┴─────┐           ┌────▼────┐
   │CPU vs   │       ┌────▼────┐ ┌────▼────┐     │硬件选型 │
   │GPU对比  │       │架构演进 │ │NVIDIA   │     │         │
   └─────────┘       │        │ │架构详解 │     └────┬────┘
                     └────────┘ └─────────┘          │
                                    │           ┌────▼────┐
                          ┌─────────┼─────────┐ │显存估算 │
                          │         │         │ │场景分析 │
                     ┌────▼───┐┌────▼───┐┌───▼───┐└────────┘
                     │CUDA编程││内存层次││Tensor │
                     │模型    ││结构    ││Core   │
                     └────┬───┘└────┬───┘└───┬───┘
                          │         │        │
                          └─────────┼────────┘
                                    │
                              ┌─────▼─────┐
                              │ 多卡互联   │
                              │ 技术      │
                              └───────────┘
```

---

## 🎯 学习路径建议

### 路径 A：快速入门（1-2 小时）

适合希望快速了解 GPU 基础知识的读者：

1. [为什么需要 GPU](01-why-gpu.md) - 理解 GPU 的价值
2. [NVIDIA GPU 架构详解](03-nvidia-architecture.md) - 核心概念
3. [硬件选型指南](08-hardware-selection.md) - 实际选型

### 路径 B：深入学习（4-6 小时）

适合需要进行 GPU 编程或优化的开发者：

1. 按顺序阅读所有文档
2. 完成每个文档中的实战练习
3. 尝试优化自己的 AI 代码

### 路径 C：专题深入

根据具体需求选择性阅读：

- **性能优化**：[04-CUDA 编程](04-cuda-programming.md) + [05-内存层次](05-memory-hierarchy.md)
- **大模型训练**：[06-Tensor Core](06-tensor-core.md) + [07-多卡互联](07-multi-gpu-interconnect.md)
- **选型评估**：[02-架构演进](02-architecture-evolution.md) + [08-硬件选型](08-hardware-selection.md)

---

## 💡 核心概念速览

### GPU 与 CPU 的本质区别

| 维度 | CPU | GPU |
|------|-----|-----|
| 设计目标 | 低延迟 | 高吞吐 |
| 核心数量 | 数十个（强大） | 数千个（简单） |
| 适用任务 | 串行、复杂逻辑 | 并行、数据密集 |
| 内存带宽 | ~100 GB/s | ~3 TB/s (HBM) |

### NVIDIA GPU 关键规格

| GPU | 架构 | Tensor Core | HBM | 带宽 | 适用场景 |
|-----|------|-------------|-----|------|----------|
| V100 | Volta | Gen 1 | 32GB HBM2 | 900 GB/s | 入门训练 |
| A100 | Ampere | Gen 3 | 80GB HBM2e | 2 TB/s | 主流训练推理 |
| H100 | Hopper | Gen 4 | 80GB HBM3 | 3.35 TB/s | 大模型训练 |
| B200 | Blackwell | Gen 5 | 192GB HBM3e | 8 TB/s | 超大模型 |

### 关键概念清单

- **SM (Streaming Multiprocessor)**：GPU 的基本计算单元
- **Warp**：32 个线程的执行单位，SIMT 模型
- **Tensor Core**：专用矩阵乘累加硬件
- **NVLink**：GPU 间高速互联
- **HBM (High Bandwidth Memory)**：高带宽显存

---

## 🔗 相关章节

- **下一章**：[02-distributed-training](../02-distributed-training/) - 分布式训练详解
- **相关**：[03-inference-serving](../03-inference-serving/) - 模型推理与部署
- **进阶**：[05-cluster-scheduling](../05-cluster-scheduling/) - GPU 集群调度

---

## 📚 延伸阅读

### 官方文档

- [CUDA C++ Programming Guide](https://docs.nvidia.com/cuda/cuda-c-programming-guide/)
- [NVIDIA GPU Architecture Whitepapers](https://www.nvidia.com/en-us/data-center/resources/)
- [PyTorch CUDA Semantics](https://pytorch.org/docs/stable/notes/cuda.html)

### 推荐书籍

- *Programming Massively Parallel Processors* - CUDA 编程圣经
- *CUDA by Example* - 入门实践指南

### 必读论文

- [NVIDIA Tesla V100 GPU Architecture](https://images.nvidia.com/content/volta-architecture/pdf/volta-architecture-whitepaper.pdf)
- [NVIDIA A100 Tensor Core GPU Architecture](https://www.nvidia.com/content/dam/en-zz/Solutions/Data-Center/nvidia-ampere-architecture-whitepaper.pdf)
- [NVIDIA H100 Tensor Core GPU Architecture](https://resources.nvidia.com/en-us-tensor-core)
