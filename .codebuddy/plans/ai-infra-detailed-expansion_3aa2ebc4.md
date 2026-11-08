---
name: ai-infra-detailed-expansion
overview: 为 AI Infra 学习框架的每个章节创建独立子文件夹，将每个主题拆分成更详细的子文档，形成深入的知识体系。
todos:
  - id: create-gpu-hardware-folder
    content: 创建 01-gpu-hardware 子文件夹，生成 README.md 索引和8个主题子文档(GPU架构、CUDA编程、内存层次、Tensor Core等)
    status: completed
  - id: create-distributed-training-folder
    content: 创建 02-distributed-training 子文件夹，生成 README.md 索引和9个主题子文档(数据并行、模型并行、3D并行、通信优化等)
    status: completed
  - id: create-inference-serving-folder
    content: 创建 03-inference-serving 子文件夹，生成 README.md 索引和10个主题子文档(量化、推理引擎、KV Cache、服务框架等)
    status: completed
  - id: create-mlops-folder
    content: 创建 04-mlops-llmops 子文件夹，生成 README.md 索引和9个主题子文档(实验跟踪、模型版本、CI/CD、LLMOps等)
    status: completed
  - id: create-cluster-scheduling-folder
    content: 创建 05-cluster-scheduling 子文件夹，生成 README.md 索引和7个主题子文档(K8s基础、GPU管理、批调度器、多租户等)
    status: completed
  - id: create-learning-roadmap-folder
    content: 创建 06-learning-roadmap 子文件夹，生成 README.md 索引和9个主题子文档(学习路径、技能清单、项目建议、面试准备等)
    status: completed
  - id: update-original-docs
    content: 更新原有6个章节文档，添加指向新子文件夹的重定向说明和导航链接
    status: completed
    dependencies:
      - create-gpu-hardware-folder
      - create-distributed-training-folder
      - create-inference-serving-folder
      - create-mlops-folder
      - create-cluster-scheduling-folder
      - create-learning-roadmap-folder
---

## 用户需求

将 AI Infra 知识库的 references 目录下的六个章节文档重构为更加详细的子文件夹结构，每个主题创建独立的子文件夹，包含更加深入和详细的子文档内容。

## 产品概述

基于现有的 AI Infra 技能知识库，将六个综合性的参考文档拆分为结构化的子文件夹，每个文件夹聚焦特定主题，包含多个详细的子文档，以便于更好的知识组织、查找和学习。

## 核心功能

1. **章节拆分**: 将每个现有章节文档转换为独立的主题文件夹
2. **内容深化**: 为每个子主题创建详细的独立文档，深入展开原有概要内容
3. **结构优化**: 每个子文件夹包含 README.md 索引文件和多个主题子文档
4. **知识关联**: 保持文档间的交叉引用和学习路径连贯性

## 章节结构规划

### 01-gpu-hardware/ (GPU/硬件基础)

- 为什么需要GPU、GPU架构演进、NVIDIA架构详解、CUDA编程模型、内存层次结构、Tensor Core、多卡互联、硬件选型

### 02-distributed-training/ (分布式训练)

- 分布式训练必要性、并行策略总览、数据并行(DDP/FSDP/ZeRO)、模型并行(张量/流水线)、3D并行、训练框架、通信优化、Checkpoint容错

### 03-inference-serving/ (模型推理部署)

- 推理与训练差异、推理优化技术(量化/剪枝/蒸馏)、推理引擎、LLM推理特性(KV Cache/PagedAttention/FlashAttention)、服务框架、部署架构、性能调优

### 04-mlops-llmops/ (MLOps/LLMOps)

- MLOps概念、成熟度模型、实验跟踪、模型版本管理、特征工程平台、CI/CD for ML、模型监控、LLMOps特殊考量、工具生态

### 05-cluster-scheduling/ (集群调度)

- AI工作负载调度挑战、Kubernetes基础、GPU资源管理、批调度器(Volcano/Yunikorn)、资源隔离配额、多租户管理、成本优化

### 06-learning-roadmap/ (学习路线图)

- 学习路径总览、后端工程师转型路径、ML工程师深入路径、新人从零路径、核心技能清单、推荐资源、动手项目、面试准备、社区学习

## Tech Stack

- 文档格式: Markdown
- 项目类型: 技术知识库/技能文档
- 文件组织: 目录结构化组织

## Implementation Approach

采用层次化目录结构组织知识内容，每个主题章节创建独立文件夹，包含:

1. **README.md**: 章节索引页，包含主题概述和子文档导航
2. **主题子文档**: 每个核心主题独立成文档，深入展开详细内容
3. **实战练习**: 包含代码示例和动手练习的独立文档

## Implementation Notes

- 保持与原文档的知识一致性，在此基础上扩展详细内容
- 每个子文档需包含目录、概述、核心内容、代码示例、延伸阅读
- 使用 ASCII 图表和 Mermaid 图增强可视化效果
- 代码示例需包含 Python/CUDA/YAML 等多种格式
- 保持跨文档的引用链接，确保知识的连贯性

## Directory Structure

```
/Users/weiquanguo/Documents/github/skills/skills/ai-infra/references/
├── 01-gpu-hardware/
│   ├── README.md                    # [NEW] 章节索引，GPU/硬件基础概述和子文档导航
│   ├── 01-why-gpu.md               # [NEW] 为什么需要GPU：CPU vs GPU设计哲学、AI对GPU的需求、计算特性对比
│   ├── 02-architecture-evolution.md # [NEW] GPU架构演进：从Volta到Blackwell的架构时间线、关键规格对比、性能飞跃原因
│   ├── 03-nvidia-architecture.md   # [NEW] NVIDIA GPU架构详解：层次结构、SM详解、Warp执行模型
│   ├── 04-cuda-programming.md      # [NEW] CUDA编程模型：基本概念映射、核函数编写、关键优化技术
│   ├── 05-memory-hierarchy.md      # [NEW] 内存层次结构：内存金字塔、HBM详解、内存优化策略
│   ├── 06-tensor-core.md           # [NEW] Tensor Core详解：MMA操作、数据类型支持、使用方法、Transformer Engine
│   ├── 07-multi-gpu-interconnect.md # [NEW] 多卡互联技术：PCIe/NVLink/NVSwitch/InfiniBand对比和架构
│   └── 08-hardware-selection.md    # [NEW] 硬件选型指南：场景选择、考量因素、显存需求估算
│
├── 02-distributed-training/
│   ├── README.md                    # [NEW] 章节索引，分布式训练概述和子文档导航
│   ├── 01-why-distributed.md       # [NEW] 为什么需要分布式训练：三大瓶颈、解决方案概述
│   ├── 02-parallelism-overview.md  # [NEW] 并行策略总览：四种并行方式对比、组合策略(3D/4D并行)
│   ├── 03-data-parallelism.md      # [NEW] 数据并行详解：DDP原理和使用、ZeRO优化器三阶段、FSDP实现
│   ├── 04-model-parallelism.md     # [NEW] 模型并行详解：张量并行(列切分/行切分)、Transformer层的张量并行
│   ├── 05-pipeline-parallelism.md  # [NEW] 流水线并行详解：按层切分原理、GPipe、1F1B调度
│   ├── 06-3d-parallelism.md        # [NEW] 3D并行实践：Megatron-LM配置、DeepSpeed 3D并行配置
│   ├── 07-training-frameworks.md   # [NEW] 训练框架对比：PyTorch/DeepSpeed/Megatron-LM/ColossalAI对比和选择建议
│   ├── 08-communication-optimization.md # [NEW] 通信优化：集合通信原语、NCCL优化、通信计算重叠
│   └── 09-checkpoint-fault-tolerance.md # [NEW] Checkpoint与容错：保存策略、分片checkpoint、弹性训练
│
├── 03-inference-serving/
│   ├── README.md                    # [NEW] 章节索引，推理部署概述和子文档导航
│   ├── 01-inference-vs-training.md # [NEW] 推理与训练的差异：关键差异对比、推理优化空间
│   ├── 02-quantization.md          # [NEW] 量化技术详解：量化类型对比、PTQ/QAT/GPTQ/AWQ/bitsandbytes
│   ├── 03-pruning-distillation.md  # [NEW] 剪枝与蒸馏：结构化/非结构化剪枝、知识蒸馏原理和实现
│   ├── 04-inference-engines.md     # [NEW] 推理引擎详解：TensorRT、TensorRT-LLM、ONNX Runtime对比
│   ├── 05-llm-inference-kv-cache.md # [NEW] LLM推理特性-KV Cache：自回归生成挑战、KV Cache原理和显存占用
│   ├── 06-llm-inference-batching.md # [NEW] LLM推理特性-Batching：Static vs Continuous Batching、PagedAttention原理
│   ├── 07-llm-inference-attention.md # [NEW] LLM推理特性-Attention优化：FlashAttention原理、Speculative Decoding
│   ├── 08-serving-frameworks.md    # [NEW] 服务框架详解：vLLM、TGI、Triton对比和使用示例
│   ├── 09-deployment-architecture.md # [NEW] 部署架构模式：单实例、多副本负载均衡、Prefill-Decode分离
│   └── 10-performance-tuning.md    # [NEW] 性能调优：关键指标(TTFT/TPS)、调优Checklist、监控可观测性
│
├── 04-mlops-llmops/
│   ├── README.md                    # [NEW] 章节索引，MLOps/LLMOps概述和子文档导航
│   ├── 01-what-is-mlops.md         # [NEW] 什么是MLOps：定义、生命周期、MLOps vs DevOps
│   ├── 02-maturity-model.md        # [NEW] MLOps成熟度模型：Google的三个等级详解
│   ├── 03-experiment-tracking.md   # [NEW] 实验跟踪：为什么需要、MLflow使用、W&B使用、最佳实践
│   ├── 04-model-registry.md        # [NEW] 模型版本管理：Model Registry概念、MLflow Registry、Hugging Face Hub
│   ├── 05-feature-store.md         # [NEW] 特征工程平台：Feature Store架构、Feast示例
│   ├── 06-cicd-for-ml.md           # [NEW] CI/CD for ML：ML Pipeline架构、GitHub Actions、Kubeflow Pipelines
│   ├── 07-model-monitoring.md      # [NEW] 模型监控与可观测性：三大监控维度、数据漂移检测、Prometheus+Grafana
│   ├── 08-llmops.md                # [NEW] LLMOps特殊考量：与传统MLOps区别、Prompt管理、LLM评估、成本优化
│   └── 09-tool-ecosystem.md        # [NEW] 工具生态：MLOps工具全景、工具选择建议
│
├── 05-cluster-scheduling/
│   ├── README.md                    # [NEW] 章节索引，集群调度概述和子文档导航
│   ├── 01-ai-workload-challenges.md # [NEW] AI工作负载的调度挑战：特殊性分析、调度架构演进
│   ├── 02-kubernetes-basics.md     # [NEW] Kubernetes基础：核心概念回顾、AI工作负载K8s配置
│   ├── 03-gpu-resource-management.md # [NEW] GPU资源管理：NVIDIA Device Plugin、MIG、GPU时间分片
│   ├── 04-batch-schedulers.md      # [NEW] 批调度器详解：Volcano核心能力和使用、Yunikorn配置
│   ├── 05-resource-isolation.md    # [NEW] 资源隔离与配额：ResourceQuota、LimitRange、Priority Class
│   ├── 06-multi-tenancy.md         # [NEW] 多租户管理：架构模式、RBAC配置
│   └── 07-cost-optimization.md     # [NEW] 成本优化策略：资源利用率优化、Spot实例使用、集群自动伸缩
│
├── 06-learning-roadmap/
│   ├── README.md                    # [NEW] 章节索引，学习路线图概述和子文档导航
│   ├── 01-overview.md              # [NEW] 学习路径总览：知识地图、学习时间估算
│   ├── 02-path-backend-engineer.md # [NEW] 路径A-后端/系统工程师转型：优势、需补充、4-6个月学习计划
│   ├── 03-path-ml-engineer.md      # [NEW] 路径B-AI/ML工程师深入底层：优势、需补充、3-4个月学习计划
│   ├── 04-path-beginner.md         # [NEW] 路径C-学生/新人从零开始：前置要求、6-9个月学习计划
│   ├── 05-core-skills.md           # [NEW] 核心技能清单：技能自评表、能力雷达图
│   ├── 06-recommended-resources.md # [NEW] 推荐资源汇总：必读书籍、推荐课程、必读论文、常用链接
│   ├── 07-hands-on-projects.md     # [NEW] 动手项目建议：入门/中级/高级项目、项目详细指南
│   ├── 08-interview-preparation.md # [NEW] 面试准备指南：常见面试题、面试准备Checklist
│   └── 09-community-learning.md    # [NEW] 社区与持续学习：活跃社区、持续学习建议、推荐关注
│
├── 01-gpu-hardware.md              # [MODIFY] 添加指向新子文件夹的重定向说明
├── 02-distributed-training.md      # [MODIFY] 添加指向新子文件夹的重定向说明
├── 03-inference-serving.md         # [MODIFY] 添加指向新子文件夹的重定向说明
├── 04-mlops-llmops.md              # [MODIFY] 添加指向新子文件夹的重定向说明
├── 05-cluster-scheduling.md        # [MODIFY] 添加指向新子文件夹的重定向说明
└── 06-learning-roadmap.md          # [MODIFY] 添加指向新子文件夹的重定向说明
```

## Agent Extensions

### Skill

- **skill-creator**
- Purpose: 参考现有skill文档结构和最佳实践，确保新创建的子文档符合skill知识库的规范和风格
- Expected outcome: 生成的文档结构和内容风格与现有AI-Infra skill保持一致