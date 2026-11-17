# 上下文管理（Context Management）

> 上下文窗口是 LLM 的"工作记忆"——管理好它，决定了模型能力的上限和推理成本的下限。

## 📚 本章概述

随着 LLM 上下文窗口从 2K 飙升到 2M，"如何高效管理上下文"已成为 AI Infra 的核心挑战之一。本章系统性地覆盖上下文管理的完整技术栈：从底层的位置编码扩展，到 KV Cache 的压缩与淘汰，到 Prefix Caching 的复用策略，再到 Prefill/Decode 分离的架构设计，最后到应用层的上下文工程实践。

**核心比喻**：上下文管理 = 管理你的书桌。书桌（显存）有限，但你要处理的资料（上下文）越来越多——你需要决定哪些书留在桌上、哪些做成便签、哪些放回书架。

## 🎯 学习目标

- [ ] 理解上下文窗口的本质、演进趋势和实际有效利用范围
- [ ] 掌握 KV Cache 优化三大方向：量化压缩、淘汰策略、结构优化
- [ ] 理解 Prefix Caching 的两种实现（vLLM APC vs SGLang RadixAttention）
- [ ] 掌握长上下文推理的位置编码扩展方案（PI/NTK/YaRN）
- [ ] 理解 Chunked Prefill 如何解决长 Prompt 阻塞问题
- [ ] 掌握 Prefill/Decode 分离架构的设计与 KV Cache 传输优化
- [ ] 学会应用层的上下文工程策略（压缩、摘要、RAG 替代）

## 📑 子文档导航

| 序号 | 文档 | 核心内容 | 难度 |
|------|------|----------|------|
| 01 | [上下文窗口基础](01-context-window-fundamentals.md) | 窗口本质、模型对比、Lost in the Middle、显存/计算复杂度 | ⭐⭐ |
| 02 | [KV Cache 深度优化](02-kv-cache-optimization.md) | KV Cache 量化（INT8/FP8）、淘汰策略（H2O/Sink）、GQA/MQA 对比 | ⭐⭐⭐ |
| 03 | [Prefix Caching 技术](03-prefix-caching.md) | vLLM APC、SGLang RadixAttention、多轮/Agent 缓存命中分析 | ⭐⭐⭐ |
| 04 | [长上下文推理](04-long-context-inference.md) | RoPE 扩展全景（PI/NTK/YaRN）、Lost in the Middle 缓解、训练工程 | ⭐⭐⭐⭐ |
| 05 | [Chunked Prefill](05-chunked-prefill.md) | 分块 Prefill 原理、Decode 交错调度、TTFT/吞吐量影响、vLLM 配置 | ⭐⭐⭐ |
| 06 | [Prefill/Decode 分离架构](06-disaggregated-serving.md) | PD 分离动机、KV Cache 传输协议、DistServe/Mooncake 对比 | ⭐⭐⭐⭐ |
| 07 | [上下文工程与压缩](07-context-engineering.md) | LLMLingua、StreamingLLM、应用层策略、技术栈选型决策树 | ⭐⭐⭐ |

**总阅读时间**：约 3.5 小时

## 🗺️ 知识地图

```
                          上下文管理
                              │
           ┌──────────────────┼──────────────────┐
           │                  │                  │
      ┌────▼─────┐      ┌────▼─────┐      ┌────▼─────┐
      │ 01 基础   │      │ 模型层优化 │      │ 系统层优化 │
      │(窗口/位置)│      │          │      │          │
      └────┬─────┘      └────┬─────┘      └────┬─────┘
           │                  │                  │
      窗口演进          ┌─────┼─────┐      ┌─────┼─────┐
      有效上下文        │     │     │      │     │     │
      Lost in Middle  ┌▼──┐ ┌▼──┐ ┌▼──┐ ┌▼──┐ ┌▼──┐ ┌▼──┐
                      │02 │ │03 │ │04 │ │05 │ │06 │ │07 │
                      │KV │ │Pre│ │长  │ │Chk│ │PD │ │压  │
                      │优化│ │Cac│ │上下│ │Pre│ │分离│ │缩  │
                      │   │ │he │ │文  │ │fill│ │   │ │工程│
                      └───┘ └───┘ └───┘ └───┘ └───┘ └───┘

      模型层：02 KV Cache 优化 → 03 Prefix 复用 → 04 长上下文
      系统层：05 调度优化 → 06 架构优化 → 07 应用策略
```

## 📖 推荐学习路径

### 🔰 入门路径（1.5 小时）

适合想快速了解上下文管理全貌的读者：

1. [01-上下文窗口基础](01-context-window-fundamentals.md) — 建立直觉
2. [02-KV Cache 深度优化](02-kv-cache-optimization.md) — 理解核心挑战
3. [07-上下文工程与压缩](07-context-engineering.md) — 学会实用策略

### 🚀 进阶路径（3.5 小时）

适合需要深入理解和实践的 AI/ML 工程师：

按顺序阅读所有 7 篇文档，重点关注：
- KV Cache 量化和淘汰策略的取舍
- Prefix Caching 在不同框架的实现差异
- RoPE 扩展方案的数学直觉
- Chunked Prefill 的调度权衡

### 🎯 按需查阅

- **上下文窗口太小**：[04-长上下文推理](04-long-context-inference.md)（位置编码扩展）
- **显存不够用**：[02-KV Cache 优化](02-kv-cache-optimization.md)（量化/淘汰/GQA）
- **重复计算太多**：[03-Prefix Caching](03-prefix-caching.md)（前缀复用）
- **长 Prompt 延迟高**：[05-Chunked Prefill](05-chunked-prefill.md)（分块处理）
- **GPU 利用率低**：[06-PD 分离](06-disaggregated-serving.md)（异构调度）
- **Token 成本高**：[07-上下文压缩](07-context-engineering.md)（压缩策略）

## 🔗 与其他章节的关联

```
  ┌─────────────────┐     ┌──────────────────────┐
  │ 00 训练基础      │     │  02 分布式训练         │
  │ Transformer/RoPE │────→│  10-序列并行           │
  └────────┬────────┘     └──────────┬───────────┘
           │                         │
           ▼                         ▼
  ┌────────────────────────────────────────────────┐
  │            ★ 08 上下文管理 (本章) ★              │
  │  窗口基础 | KV 优化 | Prefix | 长上下文          │
  │  Chunked Prefill | PD 分离 | 压缩工程            │
  └──────────────┬────────────────┬────────────────┘
                 │                │
                 ▼                ▼
  ┌──────────────────┐  ┌─────────────────────┐
  │ 03 推理部署       │  │  07 知识库/RAG       │
  │ KV Cache 基础     │  │  10-Token 优化       │
  │ PagedAttention    │  │  Context 分配策略    │
  │ FlashAttention    │  │                     │
  └──────────────────┘  └─────────────────────┘
```

## 🔧 核心工具速览

| 领域 | 开源工具 | 商业工具 |
|------|---------|---------|
| 推理框架 | vLLM, SGLang, TGI | TensorRT-LLM, Azure AI |
| KV Cache 管理 | vLLM PagedAttention | TRT-LLM KV Cache Manager |
| Prefix Caching | vLLM APC, SGLang RadixAttention | Anthropic Prompt Caching |
| 长上下文训练 | DeepSpeed Ulysses, Ring Attention | - |
| Prompt 压缩 | LLMLingua, Selective Context | - |
| PD 分离 | vLLM (v0.8+), TRT-LLM | 月之暗面 Mooncake |
| 评测工具 | RULER, LongBench, NIAH | - |

## 📝 快速开始

### 环境准备

```bash
# 安装 vLLM (支持 Prefix Caching + Chunked Prefill)
pip install vllm>=0.6.0

# 安装 SGLang (支持 RadixAttention)
pip install sglang[all]

# 安装 LLMLingua (Prompt 压缩)
pip install llmlingua
```

### 最小化实践：体验 Prefix Caching 加速

```python
from vllm import LLM, SamplingParams
import time

llm = LLM(
    model="meta-llama/Llama-3.1-8B-Instruct",
    enable_prefix_caching=True,
)

system = "You are an expert AI infrastructure engineer. " * 100
params = SamplingParams(max_tokens=50)

# 第一次请求（冷启动）
t0 = time.time()
llm.generate([f"{system}\nQ: What is KV Cache?\nA:"], params)
t1 = time.time()
print(f"First request: {t1-t0:.3f}s")

# 第二次请求（命中 Prefix Cache）
t2 = time.time()
llm.generate([f"{system}\nQ: What is PagedAttention?\nA:"], params)
t3 = time.time()
print(f"Second request (cached): {t3-t2:.3f}s")
print(f"Speedup: {(t1-t0)/(t3-t2):.1f}x")
```

## 📚 延伸阅读

### 核心论文

- [PagedAttention (vLLM)](https://arxiv.org/abs/2309.06180) — KV Cache 分页管理
- [FlashAttention-2](https://arxiv.org/abs/2307.08691) — IO-Aware Attention
- [StreamingLLM](https://arxiv.org/abs/2309.17453) — Attention Sink + 无限上下文
- [YaRN](https://arxiv.org/abs/2309.00071) — RoPE 高效扩展
- [DistServe](https://arxiv.org/abs/2401.09670) — PD 分离架构
- [SGLang](https://arxiv.org/abs/2312.07104) — RadixAttention
- [LLMLingua](https://arxiv.org/abs/2310.05736) — Prompt 压缩

### 推荐博客

- [vLLM Blog: Automatic Prefix Caching](https://blog.vllm.ai/2024/01/prefix-caching.html)
- [Anthropic: Prompt Caching](https://docs.anthropic.com/en/docs/build-with-claude/prompt-caching)
- [Lilian Weng: Large Transformer Model Inference Optimization](https://lilianweng.github.io/posts/2023-01-10-inference-optimization/)

---

*开始学习：[01-上下文窗口基础](01-context-window-fundamentals.md)*

*上一章：[07-知识库与 RAG](../07-knowledge-base/README.md)*
