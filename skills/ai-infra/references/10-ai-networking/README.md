# AI 网络基础设施

> 网络是大规模 AI 训练的"血管系统"——GPU 再强，网络不通，分布式训练就是一盘散沙。

## 📚 本章概述

大规模分布式 AI 训练对网络提出了极高的要求：数百 GB/s 的节点间通信带宽、微秒级延迟、高可靠性。网络性能直接决定了训练的线性扩展效率。本章深入讲解 RDMA、InfiniBand、RoCE、网络拓扑设计、GPUDirect 技术、网络故障排查和规划建设。

### 学习目标

- 理解 AI 训练对网络的特殊需求和通信模式
- 掌握 RDMA（InfiniBand/RoCE v2）的原理和配置
- 了解 Fat-tree、Rail-optimized、Dragonfly 等网络拓扑
- 理解 GPUDirect RDMA/Storage 的工作原理
- 掌握网络故障排查和性能诊断方法
- 能够进行 AI 集群网络规划和成本估算

### 前置知识

- 基本的计算机网络知识（TCP/IP）
- 了解分布式训练的通信模式（推荐先阅读 [02-distributed-training](../02-distributed-training/)）
- 基本的 Linux 系统管理技能

---

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|--------------|
| 01 | [AI 网络基础](01-networking-fundamentals.md) | 网络为什么是瓶颈、通信带宽需求估算、网络延迟影响分析、AI 通信模式 | 25 分钟 |
| 02 | [RDMA 深入](02-rdma-deep-dive.md) | RDMA 原理、InfiniBand vs RoCE v2、Verbs API、NCCL 与 RDMA 集成 | 40 分钟 |
| 03 | [网络拓扑设计](03-network-topology.md) | Fat-tree/Clos、Rail-optimized、Dragonfly 拓扑对比与选择 | 35 分钟 |
| 04 | [GPUDirect 技术族](04-gpudirect-technologies.md) | GPUDirect RDMA/Storage/Peer、NVLink 网络、零拷贝通信 | 30 分钟 |
| 05 | [网络故障排查](05-network-troubleshooting.md) | 常见问题、perftest 诊断、NCCL 调试、丢包分析、性能回退排查 | 35 分钟 |
| 06 | [网络规划与建设](06-network-planning.md) | 带宽规划、交换机选型、布线设计、成本估算、云上 vs 自建 | 30 分钟 |

---

## 🗺️ 知识地图

```
                       AI 网络基础设施
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
   ┌────▼────┐         ┌────▼─────┐         ┌────▼────┐
   │ 网络基础 │         │ 核心技术  │         │ 工程实践 │
   │         │         │          │         │         │
   └────┬────┘         └────┬─────┘         └────┬────┘
        │                   │                    │
   ┌────▼────┐        ┌────┴────┐          ┌────▼────┐
   │通信模式 │   ┌────▼────┐┌───▼───┐     │故障排查 │
   │带宽估算 │   │RDMA深入 ││GPUDirect│    │性能诊断 │
   │延迟分析 │   │IB/RoCE  ││技术族   │    └────┬────┘
   └─────────┘   └────┬────┘└────────┘         │
                      │                   ┌────▼────┐
                 ┌────▼────┐              │网络规划 │
                 │网络拓扑 │              │成本估算 │
                 │Fat-tree │              └─────────┘
                 │Rail-opt │
                 └─────────┘
```

---

## 🎯 学习路径建议

### 路径 A：快速入门（1 小时）

1. [AI 网络基础](01-networking-fundamentals.md) - 理解网络需求
2. [RDMA 深入](02-rdma-deep-dive.md) - 核心概念部分
3. [网络规划](06-network-planning.md) - 了解整体方案

### 路径 B：深入学习（3-4 小时）

1. 按顺序阅读所有文档
2. 重点关注 RDMA 和网络拓扑
3. 实践网络故障排查工具

### 路径 C：专题深入

- **RDMA 工程**：[02-RDMA 深入](02-rdma-deep-dive.md) + [04-GPUDirect](04-gpudirect-technologies.md)
- **集群设计**：[03-网络拓扑](03-network-topology.md) + [06-网络规划](06-network-planning.md)
- **运维排障**：[05-故障排查](05-network-troubleshooting.md)

---

## 🔗 相关章节

- **上一章**：[09-ai-storage](../09-ai-storage/) - AI 存储基础设施
- **下一章**：[11-ai-safety-alignment](../11-ai-safety-alignment/) - AI 安全与对齐
- **相关**：[02-distributed-training](../02-distributed-training/) - 分布式训练详解
- **相关**：[01-gpu-hardware/07-multi-gpu-interconnect](../01-gpu-hardware/07-multi-gpu-interconnect.md) - 多卡互联

---

## 📚 延伸阅读

- [NVIDIA Networking Documentation](https://docs.nvidia.com/networking/)
- [InfiniBand Trade Association](https://www.infinibandta.org/)
- [NCCL Developer Guide](https://docs.nvidia.com/deeplearning/nccl/)
- [RoCE Configuration Guide](https://enterprise-support.nvidia.com/s/article/howto-configure-roce-v2)
