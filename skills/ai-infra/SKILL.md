---
name: ai-infra
description: AI Infrastructure 深入学习框架。系统性地介绍支撑 AI 工作负载的基础设施技术栈，包括 GPU/硬件基础、分布式训练、模型推理部署、MLOps/LLMOps 和集群调度。适用于后端工程师转型、AI/ML 工程师深入底层、以及从零开始学习 AI Infra 的读者。
license: MIT
---

# AI Infrastructure 深入学习框架

> **AI Infra** = 为 AI 服务的基础设施，即"支撑 AI 运行的底座"

本文档提供一个系统性的 AI Infra 知识框架，帮助你从零开始构建对 AI 基础设施的完整认知。

## 目录

- [什么是 AI Infra](#什么是-ai-infra)
- [AI Infra 全景图](#ai-infra-全景图)
- [核心知识领域](#核心知识领域)
- [学习路径指南](#学习路径指南)
- [快速开始](#快速开始)

---

## 什么是 AI Infra

AI Infra（AI 基础设施）是支撑 AI/ML 工作负载运行的技术栈总和，核心目标是让 AI **跑得更快、更稳、更省**。

### 核心问题域

| 阶段 | 核心问题 | 关键技术 |
|------|----------|----------|
| **训练** | 如何高效训练大规模模型？ | 分布式训练、混合精度、Checkpoint |
| **推理** | 如何低延迟、高吞吐地服务模型？ | 量化、KV Cache、Continuous Batching |
| **资源** | 如何高效管理 GPU 集群？ | K8s、GPU 调度、资源隔离 |
| **运维** | 如何管理模型全生命周期？ | MLOps、实验跟踪、模型监控 |

### AI Infra vs Infra AI

| | AI Infra | Infra AI |
|---|---|---|
| **本质** | 为 AI **造路** | 用 AI **修路** |
| **方向** | 基础设施 → 服务于 AI | AI → 赋能基础设施 |
| **核心问题** | 如何让 AI 跑得更快更好？ | 如何让运维更智能更省人？ |

---

## AI Infra 全景图

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           AI Infra 技术栈全景                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                        应用层 (Applications)                         │   │
│  │  ChatGPT / Claude / Midjourney / GitHub Copilot / 推荐系统 / 搜索    │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                     模型服务层 (Model Serving)                        │   │
│  │  vLLM / TensorRT-LLM / Triton / TGI / SGLang / Ray Serve / BentoML  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                    训练平台层 (Training Platform)                     │   │
│  │  DeepSpeed / Megatron-LM / PyTorch FSDP / Horovod / ColossalAI      │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                      MLOps 层 (MLOps/LLMOps)                          │   │
│  │  MLflow / W&B / Kubeflow / Airflow / Feature Store / Model Registry │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                    调度编排层 (Orchestration)                         │   │
│  │  Kubernetes / Volcano / Yunikorn / Kueue / Slurm / Ray Cluster        │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                      计算层 (Compute)                                 │   │
│  │  NVIDIA GPU (H100/A100) / AMD MI300 / Google TPU / 华为昇腾          │   │
│  │  CUDA / ROCm / Tensor Core / NVLink / InfiniBand                    │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                      存储层 (Storage)                                 │   │
│  │  分布式文件系统 / 对象存储 / 向量数据库 / 模型仓库                      │   │
│  │  Lustre / GPFS / S3 / Milvus / Hugging Face Hub                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 核心知识领域

AI Infra 知识体系分为五大核心领域，每个领域都有详细的参考文档：

### 1. 🖥️ GPU/硬件基础

**为什么重要**：GPU 是 AI 计算的核心，理解硬件才能写出高效代码。

**核心内容**：
- GPU 架构演进（Volta → Ampere → Hopper → Blackwell）
- CUDA 编程模型与优化
- 内存层次结构（HBM、L2 Cache、Shared Memory）
- Tensor Core 原理与使用
- 多卡互联（NVLink、NVSwitch、InfiniBand）

📖 **详细文档**：[references/01-gpu-hardware.md](references/01-gpu-hardware.md)

---

### 2. 🔄 分布式训练

**为什么重要**：大模型无法在单卡上训练，分布式是唯一出路。

**核心内容**：
- 数据并行（DDP、FSDP、ZeRO）
- 模型并行（张量并行、流水线并行）
- 序列并行（DeepSpeed Ulysses、Ring Attention）
- 专家并行与 MoE（Mixture-of-Experts）
- 3D 并行策略组合
- 混合精度训练（FP16/BF16/FP8、Loss Scaling）
- 训练框架（DeepSpeed、Megatron-LM、ColossalAI）
- 通信优化（NCCL、AllReduce、梯度压缩）
- Checkpoint 策略与故障恢复

📖 **详细文档**：[references/02-distributed-training.md](references/02-distributed-training.md)

---

### 3. ⚡ 模型推理部署

**为什么重要**：模型价值通过推理服务实现，推理成本往往远超训练。

**核心内容**：
- 推理优化技术（量化、剪枝、蒸馏、FP8 量化）
- 推理引擎（TensorRT、TensorRT-LLM、ONNX Runtime）
- LLM 推理特性（KV Cache、Continuous Batching、PagedAttention、Prefix Caching）
- FlashAttention、Speculative Decoding
- 服务框架（vLLM、SGLang、TGI、Triton Inference Server）
- 推理时 Tensor Parallelism
- 部署架构模式与最佳实践

📖 **详细文档**：[references/03-inference-serving.md](references/03-inference-serving.md)

---

### 4. 🔧 MLOps / LLMOps

**为什么重要**：从实验到生产的桥梁，决定 AI 项目能否持续迭代。

**核心内容**：
- 实验跟踪（MLflow、Weights & Biases）
- 模型版本管理与 Registry
- 特征工程平台（Feature Store）
- CI/CD for ML
- 模型监控与可观测性
- LLMOps 特殊考量（Prompt 管理、评估、安全）

📖 **详细文档**：[references/04-mlops-llmops.md](references/04-mlops-llmops.md)

---

### 5. 📊 集群调度与资源管理

**为什么重要**：GPU 资源昂贵，高效调度直接影响成本和效率。

**核心内容**：
- Kubernetes 基础与 AI 工作负载适配
- GPU 调度策略（Device Plugin、GPU Operator、MIG、时间分片）
- 批调度器（Volcano、Yunikorn、Kueue）
- GPU 监控与可观测性（DCGM Exporter）
- 资源隔离与配额管理
- 多租户与公平调度
- 成本优化策略

📖 **详细文档**：[references/05-cluster-scheduling.md](references/05-cluster-scheduling.md)

---

## 学习路径指南

根据你的背景，选择合适的学习路径：

### 🛤️ 路径 A：后端/系统工程师转型

**背景**：熟悉分布式系统、K8s、网络，但对 ML/DL 较陌生

**建议路径**（4-6 个月）：

```
Week 1-2:  ML/DL 基础补课（推荐 fast.ai）
    ↓
Week 3-4:  GPU 基础 + CUDA 入门
    ↓
Week 5-8:  集群调度（你的优势领域延伸）
    ↓
Week 9-12: 分布式训练原理
    ↓
Week 13-16: 推理服务 + MLOps
    ↓
Week 17+:  动手项目实战
```

**重点关注**：`05-cluster-scheduling.md` → `01-gpu-hardware.md` → `02-distributed-training.md`

---

### 🛤️ 路径 B：AI/ML 工程师深入底层

**背景**：熟悉 PyTorch/TensorFlow、模型训练，想深入基础设施

**建议路径**（3-4 个月）：

```
Week 1-2:  GPU 架构深入（你可能忽略的硬件细节）
    ↓
Week 3-6:  分布式训练（从使用到原理）
    ↓
Week 7-10: 推理优化深入
    ↓
Week 11-12: 集群调度与资源管理
    ↓
Week 13+:  生产级项目实战
```

**重点关注**：`01-gpu-hardware.md` → `02-distributed-training.md` → `03-inference-serving.md`

---

### 🛤️ 路径 C：学生/新人从零开始

**背景**：CS 基础，对 AI Infra 感兴趣，想系统学习

**建议路径**（6-9 个月）：

```
Month 1:   编程基础 + Linux + Docker
    ↓
Month 2:   ML/DL 基础（动手训练几个模型）
    ↓
Month 3:   GPU 基础 + CUDA 入门
    ↓
Month 4:   PyTorch 分布式训练入门
    ↓
Month 5:   推理部署实践
    ↓
Month 6:   K8s 基础 + GPU 调度
    ↓
Month 7-9: 综合项目 + 源码阅读
```

**重点关注**：按顺序学习所有文档，不要跳跃

---

📖 **完整学习路线图**：[references/06-learning-roadmap.md](references/06-learning-roadmap.md)

---

## 快速开始

### 环境准备

```bash
# 1. 确认 GPU 可用
nvidia-smi

# 2. 安装 PyTorch (CUDA 12.1)
pip install torch torchvision torchaudio --index-url https://download.pytorch.org/whl/cu121

# 3. 安装常用工具
pip install deepspeed transformers accelerate vllm
```

### 第一个分布式训练

```python
# simple_ddp.py
import torch
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP

def main():
    dist.init_process_group("nccl")
    rank = dist.get_rank()
    device = torch.device(f"cuda:{rank}")
    
    model = torch.nn.Linear(10, 10).to(device)
    model = DDP(model, device_ids=[rank])
    
    # 训练循环...
    print(f"Rank {rank}: DDP model ready!")
    
    dist.destroy_process_group()

if __name__ == "__main__":
    main()

# 运行: torchrun --nproc_per_node=2 simple_ddp.py
```

### 第一个推理服务

```python
# simple_vllm.py
from vllm import LLM, SamplingParams

llm = LLM(model="facebook/opt-125m")
prompts = ["Hello, my name is"]
outputs = llm.generate(prompts, SamplingParams(max_tokens=50))

for output in outputs:
    print(output.outputs[0].text)
```

---

## 推荐资源

### 📚 必读书籍

| 书名 | 领域 | 推荐理由 |
|------|------|----------|
| *Programming Massively Parallel Processors* | GPU/CUDA | CUDA 编程圣经 |
| *Designing Data-Intensive Applications* | 分布式系统 | 分布式基础必读 |
| *Designing Machine Learning Systems* | MLOps | ML 系统设计最佳实践 |

### 🎓 推荐课程

- [CS149: Parallel Computing](https://gfxcourses.stanford.edu/cs149) - Stanford 并行计算
- [Full Stack Deep Learning](https://fullstackdeeplearning.com/) - 生产级 ML 系统
- [Made With ML](https://madewithml.com/) - MLOps 实践

### 📄 必读论文

- [Megatron-LM](https://arxiv.org/abs/1909.08053) - 模型并行经典
- [ZeRO](https://arxiv.org/abs/1910.02054) - 内存优化革命
- [FlashAttention](https://arxiv.org/abs/2205.14135) - Attention 优化
- [vLLM/PagedAttention](https://arxiv.org/abs/2309.06180) - LLM 推理优化

### 🔗 实用链接

- [NVIDIA Developer Blog](https://developer.nvidia.com/blog/)
- [PyTorch Distributed Tutorials](https://pytorch.org/tutorials/distributed/)
- [Hugging Face Transformers](https://huggingface.co/docs/transformers/)
- [Ray Documentation](https://docs.ray.io/)

---

## 文档索引

| 文档 | 描述 | 适合读者 |
|------|------|----------|
| [01-gpu-hardware.md](references/01-gpu-hardware.md) | GPU/硬件基础详解 | 所有人 |
| [02-distributed-training.md](references/02-distributed-training.md) | 分布式训练详解 | ML 工程师、系统工程师 |
| [03-inference-serving.md](references/03-inference-serving.md) | 推理部署详解 | ML 工程师、后端工程师 |
| [04-mlops-llmops.md](references/04-mlops-llmops.md) | MLOps/LLMOps 详解 | ML 工程师、DevOps |
| [05-cluster-scheduling.md](references/05-cluster-scheduling.md) | 集群调度详解 | 系统工程师、SRE |
| [06-learning-roadmap.md](references/06-learning-roadmap.md) | 完整学习路线图 | 所有人 |

---

*文档持续更新中，欢迎反馈和贡献！*
