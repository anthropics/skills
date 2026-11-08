---
name: ai-infra
description: AI Infrastructure 深入学习框架。系统性地介绍支撑 AI 工作负载的基础设施技术栈，包括 GPU/硬件基础、分布式训练、模型推理部署、MLOps/LLMOps、集群调度、知识库/RAG、上下文管理、AI 存储基础设施、AI 网络基础设施、AI 安全与对齐、数据工程与数据管线、微调与适配、AI 编译器与可观测性。适用于后端工程师转型、AI/ML 工程师深入底层、以及从零开始学习 AI Infra 的读者。
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
| **微调** | 如何让模型适配特定任务？ | LoRA/QLoRA、SFT、RLHF/DPO |
| **推理** | 如何低延迟、高吞吐地服务模型？ | 量化、KV Cache、Continuous Batching |
| **数据** | 如何准备高质量训练数据？ | 数据清洗、标注、合成数据、版本管理 |
| **资源** | 如何高效管理 GPU 集群？ | K8s、GPU 调度、存储、网络 |
| **安全** | 如何确保模型安全对齐？ | RLHF、Guardrails、红队测试 |
| **运维** | 如何管理模型全生命周期？ | MLOps、Profiling、监控、可观测性 |

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
│  ┌────────────────────────────┬────────────────────────────────────────┐   │
│  │  训练平台 (Training)        │  微调适配 (Fine-tuning)                 │   │
│  │  DeepSpeed / Megatron-LM   │  LoRA/QLoRA / TRL / Axolotl            │   │
│  │  PyTorch FSDP / ColossalAI │  LLaMA-Factory / Unsloth               │   │
│  └────────────────────────────┴────────────────────────────────────────┘   │
│                                    ▼                                        │
│  ┌────────────────────────────┬────────────────────────────────────────┐   │
│  │  MLOps (MLOps/LLMOps)      │  数据工程 (Data Engineering)            │   │
│  │  MLflow / W&B / Kubeflow   │  数据清洗 / 标注 / DVC / 合成数据       │   │
│  └────────────────────────────┴────────────────────────────────────────┘   │
│                                    ▼                                        │
│  ┌────────────────────────────┬────────────────────────────────────────┐   │
│  │  AI 安全 (Safety)          │  AI 编译器 (Compiler)                   │   │
│  │  RLHF/DPO / Guardrails    │  XLA / TVM / Triton / torch.compile    │   │
│  │  红队测试 / 安全评估       │  FlashAttention / Profiling / 监控      │   │
│  └────────────────────────────┴────────────────────────────────────────┘   │
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
│  ┌────────────────────────────┬────────────────────────────────────────┐   │
│  │  存储层 (Storage)           │  网络层 (Networking)                    │   │
│  │  Lustre / GPFS / JuiceFS   │  InfiniBand / RoCE v2 / RDMA          │   │
│  │  S3 / MinIO / HF Hub      │  Fat-tree / Rail-optimized / GPUDirect │   │
│  └────────────────────────────┴────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 核心知识领域

AI Infra 知识体系分为十三大核心领域，每个领域都有详细的参考文档：

### 0. 🧠 AI 训练基础

**为什么重要**：理解训练循环是所有 AI Infra 知识的前置基础。

**核心内容**：
- 训练循环全流程（数据准备、前向传播、损失计算、反向传播、参数更新）
- 反向传播与链式法则
- 梯度的含义和梯度下降
- 激活函数与自动微分
- 梯度累积与评估指标（Accuracy、F1、Perplexity、BLEU/ROUGE）
- 大数据特征工程（特征类型、Spark/Flink 技术栈、端到端 Pipeline、AI 使用特征的四种范式）

📖 **详细文档**：[references/00-training-fundamentals.md](references/00-training-fundamentals.md)

---

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
- 激活重计算（Activation Checkpointing，用计算换显存）
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

### 6. 📚 知识库（Knowledge Base）

**为什么重要**：知识库是 LLM 应用落地的关键基础设施，RAG 架构已成为消除幻觉、接入实时数据的标准方案。

**核心内容**：
- 知识库基础概念与技术栈全景（向量数据库、Embedding 模型、文档处理工具链）
- Embedding 模型深度解析（BGE-M3/OpenAI/E5/GTE、微调、多模态 CLIP）
- 向量数据库详解（HNSW/IVF/PQ 索引算法、Milvus/Qdrant/Chroma 选型、混合搜索）
- 从零构建知识库（数据采集、文档解析、分块策略、索引构建、Pipeline 设计）
- RAG 基础与高级技术（Naive RAG、HyDE、Self-RAG、Corrective RAG、Graph RAG、Agentic RAG）
- 消除幻觉与质量提升（Grounding、引用溯源、置信度评估、RAGAS 评估、Guardrails）
- 实时知识获取（Function Calling + 知识库、CDC 集成、时效性管理、在线-离线混合架构）
- Token 节省策略（语义缓存、Prompt 压缩、模型路由、成本监控）

📖 **详细文档**：[references/07-knowledge-base.md](references/07-knowledge-base.md)

---

### 7. 🧠 上下文管理（Context Management）

**为什么重要**：上下文窗口是 LLM 推理的核心约束，如何高效管理上下文直接决定服务质量、吞吐量和成本。

**核心内容**：
- 上下文窗口基础与演进（Token 限制、有效上下文 vs 标称窗口、Lost in the Middle 现象）
- KV Cache 深度优化（量化 INT8/FP8、淘汰策略 H2O/StreamingLLM、GQA/MQA 压缩、PagedAttention vs RadixAttention）
- Prefix Caching 技术（vLLM APC、SGLang RadixAttention 前缀树复用、多轮对话/Agent 场景缓存命中分析）
- 长上下文推理（RoPE 扩展 PI/NTK/YaRN、Lost in the Middle 缓解、长上下文训练工程实践）
- Chunked Prefill（长 Prompt 分块处理、与 Decode 交错调度、TTFT/吞吐量影响量化）
- Prefill/Decode 分离架构（KV Cache 跨节点传输、DistServe/Splitwise/Mooncake 方案对比、异构 GPU 调度）
- 上下文工程与压缩（LLMLingua、StreamingLLM、滑动窗口、摘要压缩、RAG 替代长上下文、技术选型决策树）

📖 **详细文档**：[references/08-context-management.md](references/08-context-management.md)

---

### 8. 💾 AI 存储基础设施

**为什么重要**：大模型训练的数据吞吐、Checkpoint 存储、模型分发都依赖高性能存储系统，存储是 AI 集群的"血管系统"。

**核心内容**：
- AI 工作负载的存储需求分析（IOPS vs 吞吐 vs 延迟）
- 分布式文件系统（Lustre/GPFS/BeeGFS/JuiceFS/CephFS 架构对比与选型）
- Checkpoint 存储优化（异步 Checkpoint、分布式保存、增量 Checkpoint、GPUDirect Storage）
- 对象存储与数据湖（S3/MinIO、Delta Lake/Iceberg、训练数据管理）
- 模型仓库（HuggingFace Hub、Model Registry、模型分发与缓存策略）
- 存储架构设计（存算分离 vs 存算一体、分层存储、缓存策略、生产级方案）

📖 **详细文档**：[references/09-ai-storage.md](references/09-ai-storage.md)

---

### 9. 🌐 AI 网络基础设施

**为什么重要**：网络是大规模分布式训练的核心瓶颈，网络带宽和延迟直接决定训练效率。

**核心内容**：
- AI 网络基础（通信原语、带宽需求估算、网络延迟影响分析）
- RDMA 深入（InfiniBand vs RoCE v2、Verbs API、PFC/ECN/DCQCN 配置）
- 网络拓扑设计（Fat-tree/Clos、Rail-optimized、Dragonfly、拓扑对训练性能的影响）
- GPUDirect 技术族（GPUDirect RDMA/Storage/Peer、NVLink 与网络协同、零拷贝通信）
- 网络故障排查（常见问题分类、诊断工具、NCCL 调试、丢包分析）
- 网络规划与建设（带宽规划、交换机选型、布线设计、成本估算、云上 vs 自建）

📖 **详细文档**：[references/10-ai-networking.md](references/10-ai-networking.md)

---

### 10. 🛡️ AI 安全与对齐

**为什么重要**：模型对齐和安全是 AI 落地的前提，RLHF/DPO 等对齐技术已成为大模型训练的标准环节。

**核心内容**：
- 对齐概述（什么是 AI 对齐、3H 原则、对齐税、安全 vs 能力的平衡）
- RLHF 与 DPO（三阶段 RLHF 流程、奖励模型训练、PPO/DPO/KTO/ORPO 对比）
- 红队测试（攻击向量分类、Prompt Injection、越狱技术、自动化红队工具）
- Guardrails 实践（NeMo Guardrails、Llama Guard、多层安全检测管线）
- 安全评估（TruthfulQA/BBQ/ToxiGen 等基准、安全评分体系、持续安全监控）
- 负责任 AI（伦理框架、偏见检测、可解释性、EU AI Act/GDPR 法规合规）

📖 **详细文档**：[references/11-ai-safety-alignment.md](references/11-ai-safety-alignment.md)

---

### 11. 🔧 数据工程与数据管线

**为什么重要**：数据是 AI 模型的"食粮"，数据质量决定模型质量，数据工程是 AI 开发的隐形支柱。

**核心内容**：
- 数据生命周期（AI 训练数据全流程、数据飞轮、数据规模 vs 质量的权衡）
- 数据采集与清洗（Web 爬取、Common Crawl、去重 MinHash/SimHash/SemDeDup、质量过滤）
- 数据标注（标注平台 Label Studio/Scale AI、主动学习、人机协同标注、质量控制）
- 合成数据（Self-Instruct、Evol-Instruct、领域数据生成、质量验证）
- 数据版本管理（DVC、LakeFS、数据血缘追踪、可复现训练）
- 数据合规（版权问题、PII 检测与脱敏、GDPR/CCPA/PIPL、数据许可证）

📖 **详细文档**：[references/12-data-engineering.md](references/12-data-engineering.md)

---

### 12. 🎯 微调与适配

**为什么重要**：微调是让通用大模型适配特定任务的关键手段，LoRA/QLoRA 使得低成本微调成为可能。

**核心内容**：
- 微调概述（全量微调 vs PEFT、微调 vs RAG vs Prompt Engineering 决策树）
- LoRA 家族（LoRA 低秩分解原理、QLoRA 4-bit 量化、DoRA 权重分解、适配器合并策略）
- SFT 流程（监督微调全流程：数据格式、Chat Template、训练配置、评估方法）
- 对齐训练基础设施（RLHF/DPO 训练的硬件需求、TRL/OpenRLHF 框架、奖励模型训练）
- 微调平台（Axolotl、LLaMA-Factory、Unsloth、AutoTrain、云上微调服务对比）
- 微调最佳实践（超参数调优、过拟合防护、灾难性遗忘、评估验证、成本优化）

📖 **详细文档**：[references/13-finetuning-adaptation.md](references/13-finetuning-adaptation.md)

---

### 13. ⚙️ AI 编译器与可观测性

**为什么重要**：AI 编译器是模型性能优化的"最后一公里"，可观测性是保障生产 AI 系统稳定运行的基础。

**核心内容**：
- AI 编译器概述（计算图优化、算子融合、Eager vs Graph vs JIT 编译模式）
- 主流编译器（XLA/TVM/Triton/torch.compile 对比与实践、TensorRT 推理优化）
- 算子优化（FlashAttention 原理、Fused Kernel 实战、内存访问优化、自定义 CUDA Kernel）
- 性能分析工具（PyTorch Profiler、NVIDIA Nsight Systems/Compute、Roofline 模型分析）
- 训练调试（Loss 曲线分析、NaN/Inf 检测、梯度监控、权重分析、分布式训练调试）
- 生产可观测性（推理服务监控指标、SLO 设计、Prometheus/Grafana 监控栈、告警策略、全链路追踪）

📖 **详细文档**：[references/14-compiler-observability.md](references/14-compiler-observability.md)

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
Week 9-12: 分布式训练原理 + AI 网络基础设施
    ↓
Week 13-16: 推理服务 + MLOps + AI 存储
    ↓
Week 17-20: AI 编译器与可观测性
    ↓
Week 21+:  动手项目实战
```

**重点关注**：`05-cluster-scheduling` → `01-gpu-hardware` → `02-distributed-training` → `10-ai-networking` → `14-compiler-observability`

---

### 🛤️ 路径 B：AI/ML 工程师深入底层

**背景**：熟悉 PyTorch/TensorFlow、模型训练，想深入基础设施

**建议路径**（3-4 个月）：

```
Week 1-2:  GPU 架构深入（你可能忽略的硬件细节）
    ↓
Week 3-6:  分布式训练（从使用到原理）
    ↓
Week 7-10: 推理优化深入 + 微调与适配
    ↓
Week 11-12: 上下文管理（KV Cache 优化、长上下文、PD 分离）
    ↓
Week 13-14: 集群调度与资源管理 + AI 编译器与可观测性
    ↓
Week 15-16: 知识库与 RAG + 数据工程 + AI 安全与对齐
    ↓
Week 17+:  生产级项目实战
```

**重点关注**：`01-gpu-hardware` → `02-distributed-training` → `03-inference-serving` → `13-finetuning-adaptation` → `08-context-management` → `14-compiler-observability`

---

### 🛤️ 路径 C：学生/新人从零开始

**背景**：CS 基础，对 AI Infra 感兴趣，想系统学习

**建议路径**（7-10 个月）：

```
Month 1:   编程基础 + Linux + Docker
    ↓
Month 2:   ML/DL 基础（动手训练几个模型）
    ↓
Month 3:   GPU 基础 + CUDA 入门
    ↓
Month 4:   PyTorch 分布式训练入门
    ↓
Month 5:   推理部署实践 + 微调与适配
    ↓
Month 6:   上下文管理 + 数据工程
    ↓
Month 7:   K8s 基础 + GPU 调度 + AI 存储与网络
    ↓
Month 8:   知识库与 RAG 实战 + AI 安全与对齐
    ↓
Month 9:   AI 编译器与可观测性
    ↓
Month 10-12: 综合项目 + 源码阅读
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
| [00-training-fundamentals.md](references/00-training-fundamentals.md) | AI 训练基础知识 | 所有人 |
| [01-gpu-hardware.md](references/01-gpu-hardware.md) | GPU/硬件基础详解 | 所有人 |
| [02-distributed-training.md](references/02-distributed-training.md) | 分布式训练详解 | ML 工程师、系统工程师 |
| [03-inference-serving.md](references/03-inference-serving.md) | 推理部署详解 | ML 工程师、后端工程师 |
| [04-mlops-llmops.md](references/04-mlops-llmops.md) | MLOps/LLMOps 详解 | ML 工程师、DevOps |
| [05-cluster-scheduling.md](references/05-cluster-scheduling.md) | 集群调度详解 | 系统工程师、SRE |
| [06-learning-roadmap.md](references/06-learning-roadmap.md) | 完整学习路线图 | 所有人 |
| [07-knowledge-base.md](references/07-knowledge-base.md) | 知识库与 RAG 技术详解 | AI 应用工程师、后端工程师 |
| [08-context-management.md](references/08-context-management.md) | 上下文管理详解 | ML 工程师、推理优化工程师 |
| [09-ai-storage.md](references/09-ai-storage.md) | AI 存储基础设施详解 | 存储工程师、系统工程师 |
| [10-ai-networking.md](references/10-ai-networking.md) | AI 网络基础设施详解 | 网络工程师、系统工程师 |
| [11-ai-safety-alignment.md](references/11-ai-safety-alignment.md) | AI 安全与对齐详解 | AI 安全工程师、ML 工程师 |
| [12-data-engineering.md](references/12-data-engineering.md) | 数据工程与数据管线详解 | 数据工程师、ML 工程师 |
| [13-finetuning-adaptation.md](references/13-finetuning-adaptation.md) | 微调与适配详解 | ML 工程师、AI 应用工程师 |
| [14-compiler-observability.md](references/14-compiler-observability.md) | AI 编译器与可观测性详解 | 性能工程师、SRE |

---

*文档持续更新中，欢迎反馈和贡献！*
