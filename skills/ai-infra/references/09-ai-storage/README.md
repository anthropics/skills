# AI 存储基础设施

> 数据是 AI 的燃料，存储是 AI 的油箱——没有高效的存储系统，再强的 GPU 也只能空转。

## 📚 本章概述

大规模 AI 训练和推理对存储系统提出了前所未有的要求：PB 级训练数据的高吞吐读取、TB 级 Checkpoint 的快速写入、数百 GB 模型权重的并发加载。存储系统已成为 AI 基础设施中仅次于 GPU 的第二大性能瓶颈。本章将从存储基础出发，深入讲解分布式文件系统、Checkpoint 优化、对象存储、模型仓库，以及生产级存储架构设计。

### 学习目标

- 理解 AI 工作负载对存储的特殊需求（吞吐、IOPS、延迟）
- 掌握主流分布式文件系统（Lustre/GPFS/JuiceFS/CephFS）的架构差异与选型
- 深入理解 Checkpoint 存储的挑战与加速方案
- 了解对象存储和数据湖在 AI 中的应用
- 掌握模型仓库的设计与管理策略
- 能够设计生产级 AI 存储架构

### 前置知识

- 基本的操作系统与文件系统概念
- 了解分布式训练的基本流程
- 基本的网络和 IO 知识
- 对 GPU 训练流程有初步了解（推荐先阅读 [00-training-fundamentals](../00-training-fundamentals/)）

---

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|--------------|
| 01 | [AI 存储基础](01-storage-fundamentals.md) | 存储在 AI 工作负载中的角色、训练/推理/数据的不同存储需求、IOPS vs 吞吐 vs 延迟、存储介质对比 | 25 分钟 |
| 02 | [分布式文件系统](02-distributed-filesystems.md) | Lustre/GPFS/BeeGFS/JuiceFS/CephFS 架构深入对比、元数据管理、条带化策略、性能调优 | 40 分钟 |
| 03 | [Checkpoint 存储](03-checkpoint-storage.md) | 大模型 Checkpoint 挑战、异步/分布式/增量 Checkpoint、GPUDirect Storage、生产方案设计 | 35 分钟 |
| 04 | [对象存储与数据湖](04-object-storage.md) | S3/MinIO/GCS 深入、数据湖架构（Delta Lake/Iceberg）、训练数据管理、分层存储策略 | 30 分钟 |
| 05 | [模型仓库](05-model-repository.md) | HuggingFace Hub 架构、Model Registry 设计、模型分发与缓存、大模型存储策略 | 25 分钟 |
| 06 | [存储架构设计](06-storage-architecture.md) | 存算分离 vs 存算一体、分层存储、缓存策略、生产级存储方案设计、成本优化 | 35 分钟 |

---

## 🗺️ 知识地图

```
                        AI 存储基础设施
                              │
        ┌─────────────────────┼─────────────────────┐
        │                     │                     │
   ┌────▼────┐          ┌─────▼─────┐          ┌────▼────┐
   │ 存储基础 │          │ 核心系统   │          │ 架构设计 │
   │         │          │           │          │         │
   └────┬────┘          └─────┬─────┘          └────┬────┘
        │                     │                     │
   ┌────▼────┐          ┌─────┴──────┐         ┌────▼────┐
   │存储需求 │     ┌────▼────┐ ┌────▼────┐    │存算分离 │
   │IOPS/吞吐│     │分布式FS │ │Checkpoint│    │分层存储 │
   │存储介质 │     │Lustre   │ │异步/分布式│    │缓存策略 │
   └─────────┘     │GPFS     │ │GPUDirect │    └────┬────┘
                   │JuiceFS  │ └─────────┘         │
                   └────┬────┘                ┌────▼────┐
                        │                     │生产方案 │
                   ┌────┴────┐                │成本优化 │
              ┌────▼────┐┌───▼────┐           └─────────┘
              │对象存储  ││模型仓库│
              │数据湖   ││HF Hub  │
              │S3/MinIO ││Registry│
              └─────────┘└────────┘
```

---

## 🎯 学习路径建议

### 路径 A：快速入门（1 小时）

适合希望快速了解 AI 存储全貌的读者：

1. [AI 存储基础](01-storage-fundamentals.md) - 理解存储需求
2. [存储架构设计](06-storage-architecture.md) - 了解整体架构
3. 快速浏览其他文档的概述部分

### 路径 B：深入学习（3-4 小时）

适合需要设计和管理 AI 存储系统的工程师：

1. 按顺序阅读所有文档
2. 重点关注分布式文件系统选型和 Checkpoint 优化
3. 结合自身场景设计存储方案

### 路径 C：专题深入

根据具体需求选择性阅读：

- **文件系统选型**：[01-存储基础](01-storage-fundamentals.md) + [02-分布式文件系统](02-distributed-filesystems.md)
- **训练优化**：[03-Checkpoint 存储](03-checkpoint-storage.md) + [06-存储架构设计](06-storage-architecture.md)
- **数据管理**：[04-对象存储与数据湖](04-object-storage.md) + [05-模型仓库](05-model-repository.md)

---

## 💡 核心概念速览

### AI 存储需求矩阵

| 工作负载 | 数据量 | IO 模式 | 关键指标 | 典型技术 |
|---------|--------|---------|---------|---------|
| 训练数据读取 | TB-PB | 顺序大块读 | 高吞吐 | Lustre/GPFS |
| Checkpoint | GB-TB/次 | 突发写入 | 低延迟+高吞吐 | NVMe+异步 |
| 模型权重加载 | 百GB | 并发一次性读 | 高吞吐 | 本地缓存 |
| 数据预处理 | TB | 随机读写 | 高 IOPS | NVMe SSD |
| 日志与指标 | GB | 追加写入 | 中等吞吐 | 对象存储 |

### 存储性能关键指标

```
三大存储性能指标:

  IOPS (Input/Output Operations Per Second)
  ├── 衡量每秒能处理多少次 IO 请求
  ├── 关键场景: 小文件读写、随机访问、元数据操作
  └── NVMe SSD: ~1M IOPS, HDD: ~200 IOPS

  吞吐量 (Throughput, GB/s)
  ├── 衡量每秒传输多少数据
  ├── 关键场景: 大文件顺序读写、训练数据加载
  └── NVMe SSD: 6-14 GB/s, Lustre: 10-100+ GB/s

  延迟 (Latency, μs/ms)
  ├── 衡量单次 IO 请求的响应时间
  ├── 关键场景: Checkpoint 写入、模型加载
  └── NVMe: ~10 μs, 网络FS: ~100 μs-1 ms, 对象存储: ~10 ms
```

---

## 🔗 相关章节

- **上一章**：[08-cost-optimization](../08-cost-optimization/) - 成本优化
- **下一章**：[10-ai-networking](../10-ai-networking/) - AI 网络基础设施
- **相关**：[02-distributed-training](../02-distributed-training/) - 分布式训练详解
- **相关**：[05-cluster-scheduling](../05-cluster-scheduling/) - GPU 集群调度（含存储系统概述）

---

## 📚 延伸阅读

### 官方文档

- [Lustre Documentation](https://doc.lustre.org/)
- [JuiceFS 文档](https://juicefs.com/docs/zh/)
- [NVIDIA GPUDirect Storage](https://docs.nvidia.com/gpudirect-storage/)
- [PyTorch Distributed Checkpoint](https://pytorch.org/docs/stable/distributed.checkpoint.html)

### 推荐文章

- [AI Training at Scale: A Guide to Storage Architecture](https://www.nvidia.com/en-us/data-center/resources/)
- [Building Storage for AI Workloads](https://www.usenix.org/publications/loginonline)
- [Checkpoint Efficiency in Large-Scale Training](https://arxiv.org/search/?query=checkpoint+large+language+model)

### 行业报告

- *The AI Infrastructure Landscape* - 存储部分
- *IDC: Worldwide AI Storage Market Analysis*
