# AI 编译器与可观测性

> AI 编译器是让模型跑得更快的"翻译官"，可观测性是让训练和推理过程"透明可控"的"X光机"。

## 📚 本章概述

AI 模型从 Python 代码到 GPU 执行之间，存在一个关键的"编译"层——AI 编译器负责将高层计算图转换为硬件高效的底层指令。同时，面对大规模训练和生产推理的复杂性，可观测性（Observability）成为保障系统稳定运行的关键能力。本章系统讲解 AI 编译器原理、主流编译器对比、算子优化技术、性能分析工具、训练调试方法和生产可观测性体系。

### 学习目标

完成本章学习后，你将能够：

- 理解 AI 编译器的作用和计算图优化原理
- 对比 XLA、TVM、Triton、torch.compile 的适用场景
- 掌握 FlashAttention 等算子优化的核心思想
- 熟练使用 PyTorch Profiler、Nsight Systems 等性能分析工具
- 系统排查训练中的 Loss 异常、NaN/Inf 等问题
- 设计生产级推理服务的监控和告警体系

### 前置知识

- 了解 GPU 架构基础（参考 [01-gpu-hardware](../01-gpu-hardware/README.md)）
- 了解分布式训练基础（参考 [02-distributed-training](../02-distributed-training/README.md)）
- 了解推理部署基础（参考 [03-inference-serving](../03-inference-serving/README.md)）

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|-------------|
| 01 | [AI 编译器概述](01-ai-compiler-overview.md) | 为什么需要 AI 编译器、计算图优化、算子融合、与传统编译器的区别 | 25 分钟 |
| 02 | [主流编译器](02-xla-tvm-triton.md) | XLA、TVM、Triton、torch.compile/Inductor 对比与实践 | 35 分钟 |
| 03 | [算子优化](03-operator-optimization.md) | FlashAttention 原理、自定义 CUDA Kernel、Fused Kernel、内存优化 | 35 分钟 |
| 04 | [性能分析工具](04-profiling-tools.md) | PyTorch Profiler、Nsight Systems/Compute、性能瓶颈定位 | 30 分钟 |
| 05 | [训练调试](05-training-debugging.md) | Loss 曲线分析、NaN/Inf 检测、梯度监控、分布式训练调试 | 30 分钟 |
| 06 | [生产可观测性](06-production-observability.md) | 推理服务监控、SLO 设计、告警策略、全链路追踪 | 30 分钟 |

## 🗺️ 知识地图

```
AI 编译器与可观测性
│
├── 编译优化 ─────────────────────────────────────────────────
│   ├── 计算图优化
│   │   ├── 算子融合 (Operator Fusion)
│   │   ├── 常量折叠 (Constant Folding)
│   │   ├── 死代码消除 (Dead Code Elimination)
│   │   └── 内存规划 (Memory Planning)
│   ├── 主流编译器
│   │   ├── XLA → JAX/TensorFlow 生态
│   │   ├── TVM → 跨平台部署
│   │   ├── Triton → 自定义 GPU Kernel
│   │   └── torch.compile → PyTorch 原生
│   └── 算子优化
│       ├── FlashAttention → 注意力加速
│       ├── Fused Kernel → 算子融合
│       └── 自定义 CUDA Kernel → 极致性能
│
├── 性能分析 ─────────────────────────────────────────────────
│   ├── 工具链
│   │   ├── PyTorch Profiler → Python 级分析
│   │   ├── Nsight Systems → 系统级分析
│   │   ├── Nsight Compute → Kernel 级分析
│   │   └── TensorBoard → 可视化
│   └── 方法论
│       ├── 瓶颈定位（计算/通信/IO）
│       ├── Roofline 模型分析
│       └── 性能回归检测
│
├── 训练调试 ─────────────────────────────────────────────────
│   ├── Loss 异常
│   │   ├── Loss 曲线分析
│   │   ├── NaN/Inf 检测
│   │   └── 梯度爆炸/消失
│   ├── 分布式调试
│   │   ├── NCCL 错误排查
│   │   ├── 节点间不一致
│   │   └── 慢节点检测
│   └── 权重分析
│       ├── 权重分布监控
│       └── 激活值统计
│
└── 生产可观测性 ─────────────────────────────────────────────
    ├── 监控指标
    │   ├── 推理延迟 (P50/P95/P99)
    │   ├── 吞吐量 (tokens/sec)
    │   ├── GPU 利用率
    │   └── 队列深度
    ├── 告警策略
    │   ├── SLO 违规
    │   ├── 错误率
    │   └── 资源饱和
    └── 可观测性栈
        ├── Metrics → Prometheus/Grafana
        ├── Logs → ELK/Loki
        └── Traces → Jaeger/Zipkin
```

## 🎯 学习路径建议

### 路径 A：应用开发者（快速入门）

```
01-编译器概述（前半部分） → 04-性能分析工具 → 05-训练调试
```

适合：使用 PyTorch 训练模型，需要排查性能问题和训练异常的开发者。

### 路径 B：性能工程师（深入优化）

```
01-编译器概述 → 02-主流编译器 → 03-算子优化 → 04-性能分析工具
```

适合：专注于模型性能优化、Kernel 开发的性能工程师。

### 路径 C：平台 SRE（生产运维）

```
04-性能分析工具 → 05-训练调试 → 06-生产可观测性
```

适合：负责 AI 推理服务运维和监控告警的 SRE 工程师。

## 🔗 相关章节

| 章节 | 关联内容 |
|------|----------|
| [01-GPU 硬件](../01-gpu-hardware/README.md) | CUDA 编程、Tensor Core |
| [02-分布式训练](../02-distributed-training/README.md) | 通信优化、训练性能 |
| [03-推理部署](../03-inference-serving/README.md) | 推理优化、量化 |
| [04-MLOps](../04-mlops-llmops/README.md) | 监控运维体系 |
| [05-集群调度](../05-cluster-scheduling/README.md) | 集群监控 |
| [10-AI 网络](../10-ai-networking/README.md) | 网络性能调优 |

## 📚 延伸阅读

- [FlashAttention: Fast and Memory-Efficient Attention](https://arxiv.org/abs/2205.14135) - Dao et al., 2022
- [Triton: An Intermediate Language for Block Programs](https://www.eecs.harvard.edu/~htk/publication/2019-mapl-tillet-kung-cox.pdf)
- [TVM: An Automated End-to-End Optimizing Compiler](https://arxiv.org/abs/1802.04799)
- [PyTorch 2.0 torch.compile Deep Dive](https://pytorch.org/get-started/pytorch-2.0/)
- [NVIDIA Nsight Systems Documentation](https://developer.nvidia.com/nsight-systems)

---

*上一章：[13-微调与适配](../13-finetuning-adaptation/README.md)*
