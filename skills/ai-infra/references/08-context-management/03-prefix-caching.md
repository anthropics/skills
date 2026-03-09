# Prefix Caching 技术

> 最好的计算是不用计算——如果两个请求共享相同的前缀，为什么要计算两次？

## 目录

- [为什么需要 Prefix Caching](#为什么需要-prefix-caching)
- [vLLM Automatic Prefix Caching (APC)](#vllm-automatic-prefix-caching-apc)
- [SGLang RadixAttention](#sglang-radixattention)
- [Anthropic Prompt Caching](#anthropic-prompt-caching)
- [缓存命中率分析](#缓存命中率分析)
- [多级缓存架构](#多级缓存架构)
- [最佳实践](#最佳实践)

---

## 为什么需要 Prefix Caching

### 核心观察：大量请求共享前缀

在实际 LLM 应用中，请求之间存在大量重复的前缀内容：

```
┌─────────────────────────────────────────────────────────────┐
│                  常见的前缀共享场景                            │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  场景 1: 多轮对话 (System Prompt 不变)                       │
│  ┌──────────────────────────────────────────────────┐       │
│  │ Turn 1: [System 2K] + [User: 你好]               │       │
│  │ Turn 2: [System 2K] + [H₁] + [User: 继续]       │       │
│  │ Turn 3: [System 2K] + [H₁] + [H₂] + [User: 总结]│       │
│  │          └── 共享 ──┘                              │       │
│  │                                                    │       │
│  │ 每轮对话都重复计算 System Prompt 的 KV Cache       │       │
│  │ → 2K tokens × 10 轮 = 20K tokens 的浪费计算       │       │
│  └──────────────────────────────────────────────────┘       │
│                                                              │
│  场景 2: RAG 应用 (相同文档被多次引用)                        │
│  ┌──────────────────────────────────────────────────┐       │
│  │ Req 1: [System] + [Doc A + B + C] + [Q1]         │       │
│  │ Req 2: [System] + [Doc A + B + C] + [Q2]         │       │
│  │ Req 3: [System] + [Doc A + B + D] + [Q3]         │       │
│  │                    └── 部分共享 ──┘                │       │
│  └──────────────────────────────────────────────────┘       │
│                                                              │
│  场景 3: Agent/Tool-use (工具描述每次都带)                    │
│  ┌──────────────────────────────────────────────────┐       │
│  │ 每次: [System] + [Tool₁ desc]...[Tool₂₀ desc]    │       │
│  │       + [History] + [Current Task]                 │       │
│  │       └────── 3K-8K tokens 工具描述 ──────┘       │       │
│  │                                                    │       │
│  │ 20 个工具描述 ≈ 5K tokens                          │       │
│  │ 每次调用都重新计算 → 极大浪费                       │       │
│  └──────────────────────────────────────────────────┘       │
│                                                              │
│  场景 4: Few-shot 推理 (示例不变)                             │
│  ┌──────────────────────────────────────────────────┐       │
│  │ 每次: [System] + [Example₁]...[Example₅]         │       │
│  │       + [New Input]                                │       │
│  │       └─── 完全相同的 Few-shot 示例 ───┘          │       │
│  └──────────────────────────────────────────────────┘       │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 性能影响量化

```
假设：System Prompt = 2000 tokens, 用户请求 = 200 tokens
模型：LLaMA-3.1 8B, A100 80GB

无 Prefix Caching:
  每次请求 Prefill: 2200 tokens → ~110ms
  100 个请求: 100 × 110ms = 11,000ms

有 Prefix Caching:
  第 1 次请求: 2200 tokens → 110ms (冷启动)
  第 2-100 次请求: 只需 Prefill 200 tokens → ~10ms
  100 个请求: 110 + 99 × 10 = 1,100ms

加速比: 10× (随前缀比例增加而增加)
```

---

## vLLM Automatic Prefix Caching (APC)

### 工作原理

vLLM 的 APC 基于 **Block 级 Hash 匹配**——将 KV Cache 按固定大小的 Block 存储，用 Token 内容的 Hash 作为缓存键。

```
APC 工作流程：

Step 1: Block 划分
  Input: "The quick brown fox jumps over the lazy dog"
  Block Size = 4 tokens
  
  Block 0: ["The", "quick", "brown", "fox"]
  Block 1: ["jumps", "over", "the", "lazy"]
  Block 2: ["dog"]  (不足一个 block，等待填充)

Step 2: Hash 计算
  Hash(Block 0) = hash(["The", "quick", "brown", "fox"]) 
                = hash(token_ids[0:4]) = 0xA3B2C1
  
  注意：Hash 包含完整的前缀信息（不只是当前 block）
  Hash(Block 1) = hash(token_ids[0:8])  ← 包含 Block 0 + Block 1
                = 0xD4E5F6

Step 3: 缓存查找
  新请求: "The quick brown fox runs fast"
  Block 0': ["The", "quick", "brown", "fox"] → Hash = 0xA3B2C1 → ✅ 命中!
  Block 1': ["runs", "fast", ...]            → Hash 不同 → ❌ 未命中
  
  → 复用 Block 0 的 KV Cache，只计算 Block 1' 之后

Step 4: 缓存管理
  ┌──────────────────────────────────────────┐
  │ GPU KV Cache Pool (Block 级管理)          │
  │                                           │
  │ [Block #0: 0xA3B2C1 ← 2 refs] [已分配]   │
  │ [Block #1: 0xD4E5F6 ← 1 ref ] [已分配]   │
  │ [Block #2: Free    ] [未分配]              │
  │ [Block #3: 0xF1F2F3 ← 0 refs] [可回收]   │
  │                                           │
  │ LRU 淘汰：ref_count=0 且最久未使用的先回收 │
  └──────────────────────────────────────────┘
```

### 使用方式

```python
# 方式 1: 命令行启动
# vllm serve meta-llama/Llama-3.1-8B-Instruct \
#     --enable-prefix-caching \
#     --gpu-memory-utilization 0.9

# 方式 2: Python API
from vllm import LLM, SamplingParams

llm = LLM(
    model="meta-llama/Llama-3.1-8B-Instruct",
    enable_prefix_caching=True,
    gpu_memory_utilization=0.9,    # 更多显存给 KV Cache Pool
    max_model_len=32768,           # 最大上下文长度
)

# 场景：多轮对话复用 System Prompt
system = """You are an AI infrastructure expert. You help engineers understand 
GPU hardware, distributed training, model serving, and MLOps. Always provide 
specific numbers, code examples, and best practices."""  # ~50 tokens

params = SamplingParams(max_tokens=200, temperature=0.7)

# 第 1 次请求（冷启动，完整 Prefill）
response1 = llm.generate(
    [f"{system}\n\nUser: What is KV Cache?\nAssistant:"],
    params,
)

# 第 2 次请求（System Prompt 命中缓存，只 Prefill 新增部分）
response2 = llm.generate(
    [f"{system}\n\nUser: How does PagedAttention work?\nAssistant:"],
    params,
)
# → response2 的 Prefill 延迟显著降低
```

### APC 的局限性

```
APC 的限制：

1. Block 对齐问题
   Block Size = 16 tokens
   前缀 A: 100 tokens → 6 个完整 Block + 4 tokens 余
   前缀 B: 100 tokens + 1 token 不同（第 97 个 token 不同）
   → Block 0-5 可以复用（96 tokens）
   → Block 6 因为有 1 个 token 不同而完全失效
   → 如果不同的 token 恰好在 Block 边界处，复用率更高

2. Hash 碰撞（极低概率）
   不同 Token 序列可能产生相同 Hash
   → vLLM 使用 SHA-256 级别的 Hash，碰撞概率可忽略

3. 显存压力
   缓存的 KV Block 占用显存
   → 如果活跃请求太多，缓存可能被频繁淘汰
   → 需要合理设置 gpu_memory_utilization

4. 不支持跨请求的部分匹配（只按前缀匹配）
   请求 A: [System] + [Doc 1] + [Q1]
   请求 B: [System] + [Doc 2] + [Q2]
   → 只有 [System] 部分可以复用，Doc 1 和 Doc 2 不同则后续全部重算
```

---

## SGLang RadixAttention

### Radix Tree 数据结构

SGLang 使用 **Radix Tree（基数树）** 来管理 KV Cache 的前缀复用，比 vLLM 的 Hash 方案更灵活：

```
Radix Tree（基数树）直觉：

想象一个字典的目录索引：
  "apple"  → 第 1 页
  "application" → 第 5 页
  "apply" → 第 8 页
  
  传统 Hash：每个词独立存储，无法利用 "appl" 的公共前缀
  
  Radix Tree：
          (root)
            │
          "appl"      ← 公共前缀（只存一份）
          / | \
        "e" "ication" "y"  ← 不同后缀
        │      │       │
       P1     P5      P8

  优势：自动发现任意长度的公共前缀，无需 Block 对齐
```

### SGLang 中的 RadixAttention

```
RadixAttention 如何管理 KV Cache：

假设有 3 个请求：
  R1: [Sys] + [Doc A] + [Q1]    (完成)
  R2: [Sys] + [Doc A] + [Q2]    (活跃)
  R3: [Sys] + [Doc B] + [Q3]    (活跃)

Radix Tree 状态：
                     (root)
                       │
                    [Sys] KV ← 3 个请求共享
                    /        \
            [Doc A] KV    [Doc B] KV
            /       \          \
      [Q1] KV    [Q2] KV    [Q3] KV
      (已完成)   (活跃)     (活跃)

内存管理：
  - [Sys] 的 KV Cache: 引用计数 = 3，保留
  - [Doc A] 的 KV Cache: 引用计数 = 2，保留
  - [Q1] 的 KV Cache: 引用计数 = 0 且已完成，标记为可回收
  - [Doc B] 的 KV Cache: 引用计数 = 1，保留

新请求 R4: [Sys] + [Doc A] + [Q4]
  → 沿树查找: [Sys] ✅ → [Doc A] ✅ → [Q4] ❌（新分支）
  → 只需计算 [Q4] 的 KV Cache
  → 复用 [Sys] + [Doc A] 的全部 KV

对比 vLLM APC：
  vLLM: [Sys] 命中（Hash 匹配）→ [Sys+Doc A] 需要整体匹配
        如果 Doc A 的 Block 边界恰好在中间某处，可能部分不匹配
  SGLang: Token 级精确匹配，不受 Block 边界限制
```

### 使用方式

```python
# SGLang 天然支持 RadixAttention（默认开启）
import sglang as sgl

@sgl.function
def chat(s, system_prompt, user_query):
    s += sgl.system(system_prompt)
    s += sgl.user(user_query)
    s += sgl.assistant(sgl.gen("response", max_tokens=200))

# 启动引擎
runtime = sgl.Runtime(
    model_path="meta-llama/Llama-3.1-8B-Instruct",
    tp_size=1,
)
sgl.set_default_backend(runtime)

# 相同 System Prompt 的多个请求 → 自动复用前缀 KV Cache
system = "You are an AI infrastructure expert..."

responses = []
questions = [
    "What is KV Cache?",
    "How does PagedAttention work?",
    "Explain FlashAttention.",
]

# 批量执行：SGLang 自动发现共享前缀
for q in questions:
    state = chat.run(system_prompt=system, user_query=q)
    responses.append(state["response"])
    
# 第 2、3 个请求的 Prefill 显著更快（前缀已缓存）
```

### SGLang 的 Fork 机制

SGLang 支持在 Radix Tree 中 **fork** 一个请求，特别适合需要多个变体的场景：

```python
@sgl.function
def multi_answer(s, question):
    s += sgl.system("You are a helpful assistant.")
    s += sgl.user(question)
    
    # Fork: 从同一前缀分出 3 个独立分支
    # 共享 System + User 的 KV Cache，只分别生成不同的回答
    forks = s.fork(3)
    for i, f in enumerate(forks):
        f += sgl.assistant(sgl.gen(f"answer_{i}", max_tokens=200, temperature=0.8))
    
    # 3 个回答共享前缀计算，只分别做 Decode
    s += sgl.select(forks, "best_answer")

# 应用场景：
# - Best-of-N 采样
# - Tree-of-Thought 推理
# - 多候选生成 + 重排
```

---

## Anthropic Prompt Caching

### 商业 API 的 Prefix Caching

Anthropic 的 Claude API 提供了显式的 Prompt Caching 功能：

```python
import anthropic

client = anthropic.Anthropic()

# 标记哪些部分需要缓存
response = client.messages.create(
    model="claude-sonnet-4-20250514",
    max_tokens=1024,
    system=[
        {
            "type": "text",
            "text": "You are an AI infrastructure expert...",  # 大段 System Prompt
            "cache_control": {"type": "ephemeral"}  # ← 标记为可缓存
        }
    ],
    messages=[
        {"role": "user", "content": "What is KV Cache?"}
    ]
)

# 查看缓存状态
print(f"Cache creation tokens: {response.usage.cache_creation_input_tokens}")
print(f"Cache read tokens: {response.usage.cache_read_input_tokens}")

# 第一次请求：cache_creation = 2000, cache_read = 0 (创建缓存)
# 第二次请求：cache_creation = 0, cache_read = 2000 (命中缓存)
# 
# 价格影响：
#   正常 input: $3.00 / 1M tokens
#   Cache write: $3.75 / 1M tokens (贵 25%)
#   Cache read:  $0.30 / 1M tokens (便宜 90%)
#
# 如果同一前缀被使用 3 次以上，就开始省钱
```

### 开源 vs 商业 Prefix Caching 对比

| 维度 | vLLM APC | SGLang RadixAttention | Anthropic Cache |
|------|---------|----------------------|----------------|
| 缓存粒度 | Block 级 | Token 级 | API 标记级 |
| 自动/手动 | 自动 | 自动 | 手动标记 |
| 缓存生命周期 | 显存内 (LRU) | 显存内 (LRU) | 5 分钟 TTL |
| 跨请求共享 | ✅ | ✅ | ✅ (相同 API Key) |
| 计费优惠 | 自部署无额外 | 自部署无额外 | 读取便宜 90% |
| 适用场景 | 自建服务 | 自建服务 | Claude API 用户 |

---

## 缓存命中率分析

### 不同场景的命中率

缓存命中率直接决定了 Prefix Caching 的收益：

```
缓存命中率计算：

  命中率 = 复用的 Token 数 / 总 Input Token 数

场景分析：

  多轮对话（固定 System Prompt = 2K tokens）：
  ┌─────────────────────────────────────────────────┐
  │ Turn 1: Sys(2K) + Q1(100)     → 命中率 0%       │
  │ Turn 2: Sys(2K) + H1(300) + Q2(100)              │
  │          ↑ 命中 2K                                │
  │          命中率 = 2000/2400 = 83%                 │
  │ Turn 5: Sys(2K) + H(1200) + Q5(100)              │
  │          ↑ 命中 2K + 部分 H                       │
  │          命中率 ≈ 2500/3300 = 76%                 │
  │                                                   │
  │ 平均命中率：~75-85%                                │
  └─────────────────────────────────────────────────┘

  Agent/Tool-use（固定工具描述 = 5K tokens）：
  ┌─────────────────────────────────────────────────┐
  │ 每次调用: Tools(5K) + History + Task(200)         │
  │ 命中率 = 5000 / (5000 + History + 200)            │
  │                                                   │
  │ 短 History: 5000/5500 ≈ 91%                       │
  │ 长 History: 5000/9000 ≈ 56%                       │
  │                                                   │
  │ 平均命中率：~60-90%                                │
  └─────────────────────────────────────────────────┘

  RAG 应用（不同查询，不同文档）：
  ┌─────────────────────────────────────────────────┐
  │ Req 1: Sys(500) + [Doc A, B, C](3K) + Q1        │
  │ Req 2: Sys(500) + [Doc A, D, E](3K) + Q2        │
  │ 命中: Sys(500) + Doc A 部分                       │
  │ 命中率 = 1500/3700 ≈ 41%                          │
  │                                                   │
  │ Req 3: Sys(500) + [Doc F, G, H](3K) + Q3        │
  │ 完全不同的文档 → 只命中 Sys                        │
  │ 命中率 = 500/3700 ≈ 14%                           │
  │                                                   │
  │ 平均命中率：~15-40% (取决于文档重复度)             │
  └─────────────────────────────────────────────────┘
```

### 提高命中率的策略

```
提高 Prefix Caching 命中率的技巧：

1. System Prompt 固定且放最前
   ✅ "System: You are..." + "User: ..."
   ❌ "User: ... System: You are..."  (前缀不一致)

2. 工具/文档按固定顺序排列
   ✅ [Tool A] [Tool B] [Tool C] — 每次相同顺序
   ❌ [Tool C] [Tool A] [Tool B] — 顺序不同前缀不匹配

3. Few-shot 示例放在 System Prompt 后面
   ✅ [System] [Example 1-5] [User Query]
   → 5 个 Example 的 KV Cache 可以被所有请求复用

4. RAG 文档排序一致
   ✅ 每次检索后按 doc_id 排序，再拼接
   → 相同文档组合在不同请求间更容易匹配

5. 使用固定的 Chat Template
   ✅ 模板中的固定部分（角色标记、分隔符）都是可复用前缀
```

---

## 多级缓存架构

### GPU 内缓存不够时怎么办

当 GPU 显存不足以缓存足够的 KV Block 时，可以构建多级缓存：

```
                    多级 KV Cache 架构

         延迟低 ←────────────────────────→ 延迟高
         容量小 ←────────────────────────→ 容量大
         
  ┌────────────┐   ┌────────────┐   ┌────────────┐
  │ L1: GPU     │   │ L2: CPU     │   │ L3: Disk   │
  │ HBM         │   │ DRAM        │   │ NVMe SSD   │
  │             │   │             │   │            │
  │ 延迟: ~μs   │   │ 延迟: ~ms   │   │ 延迟: ~10ms│
  │ 带宽: 3 TB/s│   │ 带宽: 50GB/s│   │ 带宽: 7GB/s│
  │ 容量: 80 GB │   │ 容量: 1 TB  │   │ 容量: 10TB │
  │             │   │             │   │            │
  │ 活跃请求的  │   │ 最近完成的   │   │ 历史会话的 │
  │ KV Cache    │   │ 请求 KV     │   │ KV 持久化  │
  └──────┬─────┘   └──────┬─────┘   └──────┬─────┘
         │                │                │
         ├─ Miss ────────→│                │
         │                ├─ Miss ────────→│
         │←── Prefetch ───┤                │
         │                │←── Prefetch ───┤

  查找顺序：GPU → CPU → Disk → 重新计算（Cache Miss）

实际效果（以 Agent 场景为例）：
  - 用户发起新的 Agent 任务
  - System + Tools 的 KV 在 GPU L1 中 → 命中 → 0 延迟
  - 5 分钟前的对话 KV 在 CPU L2 中 → 命中 → ~5ms 加载
  - 昨天的对话 KV 在 Disk L3 中 → 命中 → ~50ms 加载
  - 完全新的内容 → Cache Miss → 需要重新 Prefill
```

### 框架支持现状

| 功能 | vLLM | SGLang | TensorRT-LLM |
|------|------|--------|-------------|
| GPU 内缓存 | ✅ APC | ✅ RadixAttention | ✅ |
| GPU → CPU offload | ✅ (实验性) | ⚠️ 开发中 | ✅ |
| CPU → Disk 持久化 | ❌ | ❌ | ⚠️ |
| 跨实例共享 | ❌ | ❌ | ⚠️ (TRT-LLM Executor) |
| 分布式缓存 | ❌ | ❌ | ❌ |

> **前沿方向**：Mooncake（月之暗面）实现了 KV Cache 的分布式共享池，多个推理实例共享一个大容量 KV Cache 存储层。

---

## 最佳实践

### 选型建议

```
┌─────────────────────────────────────────────────────────────┐
│           Prefix Caching 选型决策树                           │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│                你的部署方式？                                  │
│                     │                                        │
│           ┌─────────┴──────────┐                             │
│           ▼                    ▼                              │
│      自建推理服务          使用商业 API                        │
│           │                    │                              │
│     ┌─────┴──────┐     ┌──────┴──────┐                      │
│     ▼            ▼     ▼             ▼                       │
│  通用服务     多轮/Agent  Claude      OpenAI                 │
│     │            │       API          API                    │
│     ▼            ▼       ▼            ▼                      │
│  vLLM APC    SGLang    Prompt       Prompt                  │
│  (简单好用)  RadixAttn  Caching     Caching                 │
│              (前缀复用  (手动标记)   (自动)                   │
│               更高效)                                        │
│                                                              │
│  性能优先：SGLang > vLLM > API                               │
│  易用优先：vLLM ≈ API > SGLang                               │
│  成本优先：自建 > Claude API > OpenAI API                    │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 优化 Checklist

```
Prefix Caching 部署 Checklist：

□ 确认场景有前缀共享（System Prompt / Few-shot / Tools）
□ 选择合适的框架（vLLM APC / SGLang RadixAttention）
□ System Prompt 放在 input 最前面
□ 工具描述/Few-shot 按固定顺序排列
□ 设置 gpu_memory_utilization=0.9（预留足够缓存空间）
□ 监控缓存命中率（vLLM metrics: cache_hit_rate）
□ 如果命中率 < 30%，考虑调整 Prompt 结构
□ 考虑 KV Cache 量化（FP8）进一步扩大缓存容量
□ 压测不同并发下的缓存淘汰率
```

### 监控指标

```python
# vLLM 的 Prefix Caching 监控指标（Prometheus 格式）

# 缓存命中率
vllm:prefix_cache_hit_rate           # 0-1, 越高越好
vllm:prefix_cache_queries_total      # 总查询次数
vllm:prefix_cache_hits_total         # 命中次数

# 缓存容量
vllm:prefix_cache_num_blocks         # 当前缓存的 Block 数
vllm:prefix_cache_utilization        # 缓存利用率

# 告警规则示例
# 如果命中率持续低于 30%，Prefix Caching 收益不大
# alert: PrefixCacheHitRateLow
# expr: vllm:prefix_cache_hit_rate < 0.3
# for: 10m
```

---

## 总结

```
┌─────────────────────────────────────────────────────────────┐
│             Prefix Caching 关键要点                          │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. 核心价值：避免重复计算共享前缀的 KV Cache                 │
│     → 加速 Prefill、降低延迟、提高吞吐                       │
│                                                              │
│  2. 两大实现：                                               │
│     vLLM APC: Block 级 Hash 匹配，简单可靠                   │
│     SGLang RadixAttention: Token 级前缀树，更灵活高效        │
│                                                              │
│  3. 命中率是关键：                                           │
│     多轮对话 ~80% | Agent ~70% | RAG ~20-40%                │
│     → 命中率 < 30% 时收益有限                                │
│                                                              │
│  4. 最佳实践：                                               │
│     System Prompt 放最前 + 固定排序 + 充足缓存空间           │
│                                                              │
│  5. 进阶方向：多级缓存（GPU→CPU→Disk）、分布式缓存           │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

*上一篇：[02-kv-cache-optimization.md](02-kv-cache-optimization.md) — KV Cache 深度优化*

*下一篇：[04-long-context-inference.md](04-long-context-inference.md) — 长上下文推理*

*返回目录：[README.md](README.md)*
