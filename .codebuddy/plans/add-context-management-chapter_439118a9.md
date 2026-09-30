---
name: add-context-management-chapter
overview: 在 ai-infra skill 中新增顶层章节 `08-context-management`（上下文管理），系统性覆盖 LLM 上下文窗口基础、KV Cache 深度优化、Prefix Caching、长上下文推理、Chunked Prefill、Prefill/Decode 分离架构、上下文压缩与应用层优化等完整技术栈，含详细技术细节、代码示例、业界最佳实践。
todos:
  - id: create-index-and-readme
    content: 创建 08-context-management.md 顶层索引文件和 08-context-management/README.md 子目录导航，建立完整的章节框架和知识地图
    status: completed
  - id: write-context-fundamentals
    content: 编写 01-context-window-fundamentals.md：上下文窗口本质、有效上下文 vs 标称窗口、Lost in the Middle、显存与计算复杂度分析，使用 [subagent:code-explorer] 确认与现有 03 章引用关系
    status: completed
    dependencies:
      - create-index-and-readme
  - id: write-kv-cache-optimization
    content: 编写 02-kv-cache-optimization.md：KV Cache 量化（INT8/FP8）、淘汰策略（H2O/StreamingLLM Sink）、GQA/MQA 压缩量化分析、PagedAttention vs RadixAttention 深度对比
    status: completed
    dependencies:
      - create-index-and-readme
  - id: write-prefix-caching
    content: 编写 03-prefix-caching.md：vLLM APC 原理与实现、SGLang RadixAttention 前缀树复用、多轮对话和 Agent 场景缓存命中分析、多级缓存架构
    status: completed
    dependencies:
      - create-index-and-readme
  - id: write-long-context-and-chunked
    content: 编写 04-long-context-inference.md（RoPE 扩展全景 PI/NTK/YaRN、Lost in the Middle 缓解、长上下文训练工程）和 05-chunked-prefill.md（分块处理原理、Sarathi-Serve、vLLM 配置）
    status: completed
    dependencies:
      - create-index-and-readme
  - id: write-disaggregated-and-engineering
    content: 编写 06-disaggregated-serving.md（PD 分离深入、KV Cache 传输协议、DistServe/Splitwise/Mooncake 对比）和 07-context-engineering.md（上下文压缩 LLMLingua、StreamingLLM、应用层策略、技术栈选型决策树）
    status: completed
    dependencies:
      - create-index-and-readme
  - id: update-skill-md
    content: 更新 SKILL.md：新增第 8 章核心知识领域描述、更新文档索引表和学习路径推荐，使用 [skill:skill-creator] 验证规范
    status: completed
    dependencies:
      - create-index-and-readme
      - write-context-fundamentals
      - write-kv-cache-optimization
      - write-prefix-caching
      - write-long-context-and-chunked
      - write-disaggregated-and-engineering
---

## 用户需求

在 `skills/ai-infra/` 项目中新增第 8 章 "上下文管理（Context Management）"，作为一个完整的独立知识领域，与现有 8 个章节并列。

## 产品概述

上下文管理是 LLM 推理和应用中的核心挑战之一。当前项目中，KV Cache 基础、PagedAttention、FlashAttention、序列并行、Token 优化等内容分散在 03-inference-serving、02-distributed-training、07-knowledge-base 等章节中，但缺乏一个系统化的上下文管理专题来整合和深入讲解。本章将系统性覆盖从上下文窗口基础到前沿的无限上下文方案，填补以下关键缺失：Prefix Caching、Chunked Prefill、长上下文位置外推（YaRN/NTK-aware）、"Lost in the Middle" 问题、StreamingLLM、Prefill/Decode 分离深入讨论。

## 核心特性

### 1. 上下文窗口基础与演进

- 上下文窗口的本质（Token 序列长度限制）、主流模型对比（4K~2M）
- 上下文窗口 vs 有效上下文（"Lost in the Middle" 现象）
- 显存占用与计算复杂度的定量分析

### 2. KV Cache 深度优化

- 在已有 03 章基础上深入：KV Cache 量化（KV Cache INT8/FP8）、KV Cache 淘汰策略（H2O/Scissorhands/StreamingLLM Attention Sink）
- GQA/MQA 对 KV Cache 的压缩效果量化分析
- 框架级实现对比（vLLM PagedAttention vs SGLang RadixAttention）

### 3. Prefix Caching 技术

- vLLM Automatic Prefix Caching（APC）原理与实现
- SGLang RadixAttention（前缀树 KV Cache 复用）
- 多轮对话/Agent 场景的缓存命中率分析与最佳实践

### 4. 长上下文推理

- RoPE 扩展方案系统对比：PI（Position Interpolation）、NTK-aware、Dynamic NTK、YaRN、Code LLaMA 方案
- "Lost in the Middle" 问题的实验数据与缓解策略
- 长上下文模型训练与推理的工程实践（数据配比、渐进式扩展）

### 5. Chunked Prefill

- 长 Prompt 分块处理原理、与 Decode 请求交错调度
- 对 TTFT 和吞吐量的影响量化分析
- Sarathi-Serve/vLLM 的 Chunked Prefill 实现

### 6. Prefill/Decode 分离架构（Disaggregated Serving）

- 在已有 09-deployment-architecture 基础上深入：KV Cache 跨节点传输协议与优化
- DistServe/Splitwise/Mooncake 方案对比
- 异构 GPU 调度策略、网络带宽需求分析

### 7. 上下文压缩与优化

- Prompt Compression（LLMLingua/LongLLMLingua）
- StreamingLLM / Infinite Context 方案
- 应用层策略（滑动窗口、摘要压缩、RAG 替代长上下文）

## 技术栈

- 文件格式：Markdown (.md)
- 项目规范：遵循现有 Skill 规范结构（顶层索引 .md + 子目录/ + README.md 导航 + 编号子文件）
- 版本管理：Git（当前在 `ai-infra` 分支）

## 实现方案

### 整体策略

采用 **"顶层索引 + 子目录导航 + 7 个子文件"** 的三层结构，与现有 03-inference-serving、07-knowledge-base 等章节保持完全一致的文档架构。

核心原则：

1. **引用而不重复**：KV Cache 基础原理已在 `03-inference-serving/05-llm-inference-kv-cache.md` 详细讲解，本章引用并深入到优化层面（量化、淘汰、分页管理对比）；PD 分离基础已在 `09-deployment-architecture.md` 覆盖，本章深入到 KV Cache 传输协议和异构调度
2. **填补确认的缺失**：Prefix Caching、Chunked Prefill、RoPE 扩展（YaRN/NTK）、Lost in the Middle、StreamingLLM、KV Cache 量化/淘汰策略 -- 这些在现有文档中均未系统覆盖
3. **统一串联**：将分散在 03（推理）、02（训练/序列并行）、07（RAG/Token 优化）中的上下文相关知识统一到一个知识框架下

### 关键技术决策

1. **与 03-inference-serving 的关系**：08 章是上下文管理的"垂直深度"章节，03 章是推理部署的"水平广度"章节。03 章的 KV Cache / PagedAttention / FlashAttention 讲"是什么、为什么"，08 章讲"怎么在上下文维度做到极致"
2. **编号选择 `08`**：顺延现有 00-07 编号体系，与 `07-knowledge-base` 之后连续
3. **子文件数量 7 个**：覆盖完整的上下文管理技术栈，每个子文件 25-35 分钟阅读时间，总计约 3.5 小时

### 写作风格（复用现有规范）

- 每篇开头用生活类比建立直觉
- ASCII 图示说明架构和数据流
- 完整的数值计算示例（如 KV Cache 显存计算、缓存命中率估算）
- PyTorch/Python 代码示例
- 表格对比不同方案（优缺点、适用场景）
- 与相关章节交叉引用

## 实现注意事项

1. **数值准确性**：所有显存计算公式必须与 03 章已有的计算保持一致（如 KV Cache per token = 2 x n_layers x n_kv_heads x d_head x 2 bytes）
2. **避免内容膨胀**：对已有详细讲解的内容（如 FlashAttention 完整原理、PagedAttention 分页机制），采用"要点概述 + 链接跳转"方式引用，不复制
3. **代码示例可执行**：使用 vLLM、SGLang、HuggingFace Transformers 的真实 API，确保代码片段可复制运行
4. **交叉引用完整**：每个子文件都明确标注与其他章节的关联关系

## 架构设计

新增文件在现有结构内进行，不改变已有文件的组织方式：

```
skills/ai-infra/
├── SKILL.md                                    # [MODIFY] 新增第 8 章描述、更新文档索引
├── references/
│   ├── 08-context-management.md                # [NEW] 顶层索引文件（概述 + 快速导航 + 核心内容概览，约 800-1000 行）
│   │   包含：上下文管理全景图、各子主题概要、代码示例、技术栈对比表
│   │
│   └── 08-context-management/
│       ├── README.md                           # [NEW] 子目录导航（子文档表格、知识地图、学习路径、核心概念速览）
│       │
│       ├── 01-context-window-fundamentals.md   # [NEW] 上下文窗口基础
│       │   内容：窗口本质、主流模型对比、有效上下文 vs 标称窗口、Lost in the Middle、
│       │         显存/计算复杂度分析、Attention 的 O(n^2) 问题、位置编码基础
│       │   预计阅读：25 分钟
│       │
│       ├── 02-kv-cache-optimization.md         # [NEW] KV Cache 深度优化
│       │   内容：KV Cache 量化（INT8/FP8/INT4）、淘汰策略（H2O/Scissorhands/Attention Sink）、
│       │         GQA/MQA 压缩效果量化、PagedAttention vs RadixAttention 对比、
│       │         动态 KV Cache 管理（Eviction + Compression 联合策略）
│       │   预计阅读：30 分钟
│       │
│       ├── 03-prefix-caching.md                # [NEW] Prefix Caching 技术
│       │   内容：vLLM Automatic Prefix Caching（APC）原理、SGLang RadixAttention 前缀树复用、
│       │         多轮对话/Agent/RAG 场景缓存命中分析、System Prompt 缓存、
│       │         GPU/CPU/Disk 多级缓存架构、缓存一致性问题
│       │   预计阅读：30 分钟
│       │
│       ├── 04-long-context-inference.md        # [NEW] 长上下文推理
│       │   内容：RoPE 扩展全景（PI/NTK-aware/Dynamic NTK/YaRN/Code LLaMA），
│       │         Lost in the Middle 实验数据与缓解方案，长上下文训练工程实践（渐进式扩展、
│       │         数据配比、Packing 策略），长上下文推理性能分析（TTFT 与序列长度关系）
│       │   预计阅读：35 分钟
│       │
│       ├── 05-chunked-prefill.md               # [NEW] Chunked Prefill
│       │   内容：长 Prompt 阻塞问题、分块处理原理、与 Decode 交错调度、
│       │         对 TTFT/吞吐量影响量化、Sarathi-Serve 论文方案、vLLM 实现配置、
│       │         最优 Chunk Size 选择策略
│       │   预计阅读：25 分钟
│       │
│       ├── 06-disaggregated-serving.md         # [NEW] Prefill/Decode 分离架构
│       │   内容：PD 分离动机深入（Prefill compute-bound vs Decode memory-bound）、
│       │         KV Cache 传输协议（RDMA/NVLink/NIXL）、DistServe/Splitwise/Mooncake 方案对比、
│       │         异构 GPU 调度（Prefill 用 H100/Decode 用 L40S）、
│       │         网络带宽需求计算、生产环境部署案例
│       │   预计阅读：30 分钟
│       │
│       └── 07-context-engineering.md           # [NEW] 上下文工程与压缩
│           内容：Prompt Compression（LLMLingua/LongLLMLingua）、StreamingLLM（Attention Sink 机制）、
│                 Infinite Context 方案、应用层策略（滑动窗口、摘要链、RAG 替代长上下文）、
│                 上下文窗口分配最佳实践、完整技术栈选型决策树
│           预计阅读：30 分钟
```

### 需同步更新的现有文件

| 文件 | 修改内容 |
| --- | --- |
| `SKILL.md` | 在"核心知识领域"部分新增第 8 章描述；更新"文档索引"表格；更新学习路径中的推荐阅读 |


## Agent Extensions

### Skill

- **skill-creator**
- 用途：确保新增的 `08-context-management.md` 顶层索引文件和子目录结构符合 Skill 规范格式
- 预期结果：所有新增文件满足 Skill 规范要求，SKILL.md 更新后格式正确

### SubAgent

- **code-explorer**
- 用途：在编写每个子文件前，精确定位现有文档中已覆盖的相关内容（行号和上下文），确保引用准确、避免重复
- 预期结果：为每个子文件提供准确的交叉引用目标和需要避免重复的内容范围