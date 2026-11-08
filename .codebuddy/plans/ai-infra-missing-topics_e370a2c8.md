---
name: ai-infra-missing-topics
overview: 为 AI Infra skill 补充 00-08 章节中遗漏的重要 AI 基建话题，包括现有章节内缺失的子话题补充，以及新增 09-18 共 10 个全新章节。
todos:
  - id: update-01-gpu
    content: 在 01-gpu-hardware 中新增 09-non-nvidia-accelerators.md 和 10-gpu-virtualization.md，并更新 README.md 和顶层 01-gpu-hardware.md 的导航
    status: completed
  - id: update-02-distributed
    content: 在 02-distributed-training 中新增 15-network-architecture.md 和 16-data-loading-pipeline.md，并更新 README.md 和顶层 md 导航
    status: completed
  - id: update-03-inference
    content: 在 03-inference-serving 中新增 11-speculative-decoding.md、12-multimodal-inference.md、13-edge-inference.md，并更新 README.md 和顶层 md 导航
    status: completed
  - id: update-04-mlops
    content: 在 04-mlops-llmops 中新增 10-data-management.md 和 11-ai-safety-guardrails.md，并更新 README.md 和顶层 md 导航
    status: completed
  - id: update-05-scheduling
    content: 在 05-cluster-scheduling 中新增 09-storage-systems.md 和 10-network-infrastructure.md，并更新 README.md 和顶层 md 导航
    status: completed
  - id: new-09-storage
    content: 创建 09-ai-storage 完整章节：顶层跳转页 + README.md + 6 篇子文档（存储基础、分布式文件系统、Checkpoint 存储、对象存储、模型仓库、存储架构设计）
    status: completed
  - id: new-10-networking
    content: 创建 10-ai-networking 完整章节：顶层跳转页 + README.md + 6 篇子文档（网络基础、RDMA 深入、网络拓扑、GPUDirect、故障排查、网络规划）
    status: completed
  - id: new-11-safety
    content: 创建 11-ai-safety-alignment 完整章节：顶层跳转页 + README.md + 6 篇子文档（对齐概述、RLHF/DPO、红队测试、Guardrails、安全评估、负责任 AI）
    status: completed
  - id: new-12-data
    content: 创建 12-data-engineering 完整章节：顶层跳转页 + README.md + 6 篇子文档（数据生命周期、采集清洗、标注、合成数据、版本管理、合规）
    status: completed
  - id: new-13-finetune
    content: 创建 13-finetuning-adaptation 完整章节：顶层跳转页 + README.md + 6 篇子文档（微调概述、LoRA 家族、SFT 流程、对齐训练、微调平台、最佳实践）
    status: completed
  - id: new-14-compiler
    content: 创建 14-compiler-observability 完整章节：顶层跳转页 + README.md + 6 篇子文档（编译器概述、XLA/TVM/Triton、算子优化、Profiling 工具、训练调试、生产可观测性）
    status: completed
  - id: update-skill-md
    content: 使用 [skill:skill-creator] 更新 SKILL.md 主文档，新增 09-14 章节到核心知识领域、文档索引表和学习路径指南中
    status: completed
    dependencies:
      - update-01-gpu
      - update-02-distributed
      - update-03-inference
      - update-04-mlops
      - update-05-scheduling
      - new-09-storage
      - new-10-networking
      - new-11-safety
      - new-12-data
      - new-13-finetune
      - new-14-compiler
---

## 用户需求

Review ai-infra skill 的 00-08 章节，找出 AI 基建领域中遗漏的重要话题，并为这些遗漏话题创建补充文档。

## 产品概述

对现有 AI Infrastructure 深入学习框架进行内容审计与扩展，补充遗漏的 AI 基建核心话题。分为两类补充：

1. **现有章节内补充子话题**：在已有章节中新增缺失的子文档
2. **全新章节**：新建 09-14 六个章节，覆盖存储、网络、安全对齐、数据工程、微调适配、AI编译器与可观测性等领域

## 核心补充内容

### A. 现有章节补充

- **01-GPU 硬件**：补充非 NVIDIA 加速器（AMD MI300、Google TPU、华为昇腾等）、GPU 虚拟化
- **02-分布式训练**：补充大规模训练网络架构、分布式数据加载与预处理
- **03-推理部署**：补充多模态推理、端侧推理、Speculative Decoding 深入
- **04-MLOps**：补充数据管理与质量、AI Safety 与 Guardrails
- **05-集群调度**：补充存储系统、网络基础设施

### B. 新增章节

- **09-AI 存储基础设施**：分布式文件系统、Checkpoint 存储、模型仓库、对象存储、数据湖
- **10-AI 网络基础设施**：RDMA/RoCE/InfiniBand 深入、集群网络拓扑、网络故障排查
- **11-AI 安全与对齐**：RLHF/DPO 对齐技术、红队测试、Guardrails、Responsible AI
- **12-数据工程与数据管线**：数据采集/清洗/去重/标注、DVC、合成数据、数据合规
- **13-微调与适配**：LoRA/QLoRA/Adapter、SFT/RLHF 流程、微调平台
- **14-AI 编译器与可观测性**：XLA/TVM/Triton 编译器、性能 Profiling、训练调试

## 技术栈

- 纯 Markdown 文档编写，无需代码框架
- 遵循现有 ai-infra skill 的文档结构和写作风格

## 实现方案

### 文档结构约定（基于现有项目）

每个章节需要三类文件：

1. **顶层跳转页** `references/XX-topic-name.md`：简短引导，指向子文件夹 README
2. **子文件夹 README** `references/XX-topic-name/README.md`：章节概述、学习目标、子文档导航表、知识地图、学习路径建议、相关章节链接、延伸阅读
3. **子文档** `references/XX-topic-name/NN-subtopic.md`：具体话题的深入讲解

### 写作风格约定（基于现有文档分析）

- 每篇文档开头有引用格式的概括语 `> ...`
- 使用 ASCII 艺术图表展示架构和对比
- 大量使用表格对比不同技术方案
- 用生活类比解释技术概念（如"学厨师"类比训练循环）
- 包含可执行的 Python/bash 代码示例
- 每篇末尾有延伸阅读和导航链接
- README 包含：📚 本章概述、学习目标、📖 子文档导航表、🗺️ 知识地图（ASCII 图）、🎯 学习路径建议、🔗 相关章节

### 编号规则

- 现有章节补充的子文档按原有编号续写（如 01-gpu-hardware 已有 01-08，新增从 09 开始）
- 新章节从 09 开始编号

## 实现说明

- 现有章节补充时需同步更新该章节的 README.md（导航表、知识地图等）和顶层 .md 文件
- 新章节创建后需同步更新 SKILL.md（核心知识领域、文档索引、学习路径等）
- 保持与现有文档一致的深度和详细程度（每篇子文档约 15-50KB）
- 每篇文档的阅读时间标注在 README 导航表中

## 目录结构

```
skills/ai-infra/
├── SKILL.md                                          # [MODIFY] 更新核心知识领域、文档索引表、学习路径中的章节引用
│
└── references/
    │
    │  # ===== 现有章节补充 =====
    │
    ├── 01-gpu-hardware/
    │   ├── README.md                                 # [MODIFY] 更新导航表、知识地图，新增 09-10 条目
    │   ├── 09-non-nvidia-accelerators.md             # [NEW] 非 NVIDIA 加速器对比：AMD MI300X/MI325X、Google TPU v5e/v6e、华为昇腾 910B、Intel Gaudi 3、寒武纪 MLU370。涵盖架构设计差异、软件生态（ROCm/JAX/CANN）、性能对比、选型建议
    │   └── 10-gpu-virtualization.md                  # [NEW] GPU 虚拟化技术：MIG 深入、vGPU（NVIDIA GRID）、时间分片 vs 空间分片、GPU 共享方案（MPS、GPU Operator）、容器化 GPU 管理、多租户隔离策略
    │
    ├── 01-gpu-hardware.md                            # [MODIFY] 更新子文档索引表，新增 09-10 链接
    │
    ├── 02-distributed-training/
    │   ├── README.md                                 # [MODIFY] 更新导航表、知识地图，新增 15-16 条目
    │   ├── 15-network-architecture.md                # [NEW] 大规模训练网络架构：RoCE vs InfiniBand 对比、RDMA 原理、Fat-tree/Dragonfly/Rail-optimized 拓扑、GPUDirect RDMA/Storage、网络带宽规划与瓶颈分析、实际集群网络设计案例
    │   └── 16-data-loading-pipeline.md               # [NEW] 分布式数据加载与预处理：DataLoader 瓶颈分析、WebDataset/Mosaic Streaming、多节点数据分片、数据预处理 GPU 加速（DALI）、IO 优化策略、训练数据格式选择
    │
    ├── 02-distributed-training.md                    # [MODIFY] 更新子文档索引表
    │
    ├── 03-inference-serving/
    │   ├── README.md                                 # [MODIFY] 更新导航表，新增 11-13 条目
    │   ├── 11-speculative-decoding.md                # [NEW] Speculative Decoding 深入：Draft-Verify 范式、Draft 模型选择、Tree-based Speculative Decoding、Medusa、Eagle、Self-Speculative Decoding、吞吐提升分析
    │   ├── 12-multimodal-inference.md                # [NEW] 多模态推理：视觉语言模型推理特性、图像/视频预处理 pipeline、多模态 KV Cache 管理、扩散模型推理优化（SDXL/Flux）、多模态服务架构
    │   └── 13-edge-inference.md                      # [NEW] 端侧与边缘推理：llama.cpp/MLC-LLM/Ollama、ONNX Runtime Mobile、NPU/DSP 加速、模型格式转换（GGUF/GGML）、手机/IoT 部署实践、On-device vs Cloud 决策
    │
    ├── 03-inference-serving.md                       # [MODIFY] 更新子文档索引表
    │
    ├── 04-mlops-llmops/
    │   ├── README.md                                 # [MODIFY] 更新导航表，新增 10-11 条目
    │   ├── 10-data-management.md                     # [NEW] 数据管理与质量：训练数据清洗/去重（MinHash/SimHash）、数据标注平台（Label Studio/Prodigy）、数据版本管理（DVC/LakeFS）、数据质量评估、数据合规（版权/隐私/PII）
    │   └── 11-ai-safety-guardrails.md                # [NEW] AI Safety 与 Guardrails：RLHF/DPO/PPO 安全对齐、红队测试方法论、NeMo Guardrails/Llama Guard、内容过滤、Prompt Injection 防护、安全评估基准
    │
    ├── 04-mlops-llmops.md                            # [MODIFY] 更新子文档索引表
    │
    ├── 05-cluster-scheduling/
    │   ├── README.md                                 # [MODIFY] 更新导航表，新增 09-10 条目
    │   ├── 09-storage-systems.md                     # [NEW] AI 存储系统：分布式文件系统（Lustre/GPFS/JuiceFS/CephFS）、Checkpoint 存储加速、对象存储（S3/MinIO）、数据湖架构、存储性能调优、存储与计算分离架构
    │   └── 10-network-infrastructure.md              # [NEW] 网络基础设施：数据中心网络架构、RDMA 网络配置、交换机选型、网络监控与故障排查、流量工程、网络安全策略
    │
    ├── 05-cluster-scheduling.md                      # [MODIFY] 更新子文档索引表
    │
    │  # ===== 新增章节 =====
    │
    ├── 09-ai-storage.md                              # [NEW] 顶层跳转页，指向 09-ai-storage/README.md
    ├── 09-ai-storage/
    │   ├── README.md                                 # [NEW] 章节概述、导航表、知识地图、学习路径
    │   ├── 01-storage-fundamentals.md                # [NEW] AI 存储基础：存储在 AI 工作负载中的角色、训练/推理/数据的不同存储需求、IOPS vs 吞吐 vs 延迟
    │   ├── 02-distributed-filesystems.md             # [NEW] 分布式文件系统：Lustre/GPFS/BeeGFS/JuiceFS/CephFS 架构对比、元数据管理、性能调优
    │   ├── 03-checkpoint-storage.md                  # [NEW] Checkpoint 存储：大模型 Checkpoint 挑战、异步 Checkpoint、分布式保存策略、存储加速方案
    │   ├── 04-object-storage.md                      # [NEW] 对象存储与数据湖：S3/MinIO/GCS、数据湖架构（Delta Lake/Iceberg）、训练数据管理
    │   ├── 05-model-repository.md                    # [NEW] 模型仓库：HuggingFace Hub、Model Registry、模型分发与缓存、大模型存储策略
    │   └── 06-storage-architecture.md                # [NEW] 存储架构设计：存算分离 vs 存算一体、分层存储、缓存策略、生产级存储方案设计
    │
    ├── 10-ai-networking.md                           # [NEW] 顶层跳转页
    ├── 10-ai-networking/
    │   ├── README.md                                 # [NEW] 章节概述、导航表、知识地图
    │   ├── 01-networking-fundamentals.md             # [NEW] AI 网络基础：为什么网络是大规模训练的瓶颈、通信带宽需求估算、网络延迟影响分析
    │   ├── 02-rdma-deep-dive.md                      # [NEW] RDMA 深入：RDMA 原理、InfiniBand vs RoCE v2、RDMA 编程模型（Verbs API）、NCCL 与 RDMA
    │   ├── 03-network-topology.md                    # [NEW] 网络拓扑设计：Fat-tree/Clos、Rail-optimized、Dragonfly、拓扑选择对训练性能的影响
    │   ├── 04-gpudirect-technologies.md              # [NEW] GPUDirect 技术族：GPUDirect RDMA/Storage/Peer、NVLink 与网络的协同、零拷贝通信
    │   ├── 05-network-troubleshooting.md             # [NEW] 网络故障排查：常见网络问题、性能诊断工具（perftest/ib_write_bw）、NCCL 调试、丢包分析
    │   └── 06-network-planning.md                    # [NEW] 网络规划与建设：带宽规划方法、交换机选型、布线设计、成本估算、云上网络 vs 自建
    │
    ├── 11-ai-safety-alignment.md                     # [NEW] 顶层跳转页
    ├── 11-ai-safety-alignment/
    │   ├── README.md                                 # [NEW] 章节概述、导航表、知识地图
    │   ├── 01-alignment-overview.md                  # [NEW] 对齐概述：什么是 AI 对齐、为什么需要对齐、对齐税、安全 vs 能力的平衡
    │   ├── 02-rlhf-dpo.md                            # [NEW] RLHF 与 DPO：人类反馈强化学习全流程、奖励模型训练、PPO/DPO/KTO 对比、基础设施需求
    │   ├── 03-red-teaming.md                         # [NEW] 红队测试：攻击向量分类、Prompt Injection、越狱技术、自动化红队测试工具
    │   ├── 04-guardrails.md                          # [NEW] Guardrails 实践：NeMo Guardrails、Llama Guard、内容过滤、输入输出安全检测、合规审计
    │   ├── 05-safety-evaluation.md                   # [NEW] 安全评估：评估基准（TruthfulQA/BBQ/ToxiGen）、安全评分体系、持续安全监控
    │   └── 06-responsible-ai.md                      # [NEW] 负责任 AI：伦理框架、偏见检测与缓解、可解释性、透明度报告、法规合规（EU AI Act）
    │
    ├── 12-data-engineering.md                        # [NEW] 顶层跳转页
    ├── 12-data-engineering/
    │   ├── README.md                                 # [NEW] 章节概述、导航表、知识地图
    │   ├── 01-data-lifecycle.md                      # [NEW] 数据生命周期：AI 训练数据全流程、数据飞轮、数据是新石油
    │   ├── 02-data-collection-cleaning.md            # [NEW] 数据采集与清洗：Web 爬取、Common Crawl、去重（MinHash/SimHash/SemDeDup）、质量过滤
    │   ├── 03-data-labeling.md                       # [NEW] 数据标注：标注平台（Label Studio/Scale AI）、主动学习、人机协同标注、标注质量控制
    │   ├── 04-synthetic-data.md                      # [NEW] 合成数据：LLM 生成训练数据、Self-Instruct、Evol-Instruct、数据增强、质量验证
    │   ├── 05-data-versioning.md                     # [NEW] 数据版本管理：DVC、LakeFS、数据血缘追踪、可复现训练
    │   └── 06-data-compliance.md                     # [NEW] 数据合规：版权问题、隐私保护（PII 检测/脱敏）、GDPR/CCPA、数据许可证
    │
    ├── 13-finetuning-adaptation.md                   # [NEW] 顶层跳转页
    ├── 13-finetuning-adaptation/
    │   ├── README.md                                 # [NEW] 章节概述、导航表、知识地图
    │   ├── 01-finetuning-overview.md                 # [NEW] 微调概述：全量微调 vs 参数高效微调、何时微调 vs RAG vs Prompt Engineering 决策树
    │   ├── 02-lora-family.md                         # [NEW] LoRA 家族：LoRA 原理（低秩分解）、QLoRA、DoRA、LoRA+ 、适配器合并策略
    │   ├── 03-sft-pipeline.md                        # [NEW] SFT 流程：监督微调全流程、数据准备、训练配置、评估方法、Chat Template
    │   ├── 04-alignment-training.md                  # [NEW] 对齐训练基础设施：RLHF/DPO 训练的硬件需求、TRL/OpenRLHF 框架、奖励模型训练
    │   ├── 05-finetuning-platforms.md                # [NEW] 微调平台：Axolotl、LLaMA-Factory、Unsloth、AutoTrain、云上微调服务对比
    │   └── 06-finetuning-best-practices.md           # [NEW] 微调最佳实践：超参数调优、过拟合防护、灾难性遗忘、评估与验证、成本优化
    │
    ├── 14-compiler-observability.md                  # [NEW] 顶层跳转页
    ├── 14-compiler-observability/
    │   ├── README.md                                 # [NEW] 章节概述、导航表、知识地图
    │   ├── 01-ai-compiler-overview.md                # [NEW] AI 编译器概述：为什么需要 AI 编译器、计算图优化、算子融合、与传统编译器的区别
    │   ├── 02-xla-tvm-triton.md                      # [NEW] 主流编译器：XLA（JAX/TF）、TVM/Apache TVM、Triton（OpenAI）、torch.compile/Inductor 对比
    │   ├── 03-operator-optimization.md               # [NEW] 算子优化：自定义 CUDA Kernel、FlashAttention 实现原理、Fused Kernel、内存访问优化
    │   ├── 04-profiling-tools.md                     # [NEW] 性能分析工具：PyTorch Profiler、NVIDIA Nsight Systems/Compute、TensorBoard Profiler、性能瓶颈定位方法
    │   ├── 05-training-debugging.md                  # [NEW] 训练调试：Loss 曲线分析、梯度/权重可视化、NaN/Inf 检测、分布式训练调试、常见训练问题排查
    │   └── 06-production-observability.md            # [NEW] 生产可观测性：推理服务监控、SLO 设计、告警策略、日志分析、全链路追踪
```

## Agent Extensions

### Skill

- **skill-creator**
- 用途：在新增章节完成后，用于更新 SKILL.md 主文档中的 skill 元信息（description）和核心知识领域描述，确保 skill 定义与扩展后的内容一致
- 预期结果：SKILL.md 的 frontmatter description 和核心知识领域部分准确反映所有 09-14 新章节

### SubAgent

- **code-explorer**
- 用途：在每个任务开始前，探索对应章节的现有文件结构和内容风格，确保新增/修改文档与现有文档保持一致
- 预期结果：获取目标章节的准确文件列表、README 格式、子文档结构，作为编写参考