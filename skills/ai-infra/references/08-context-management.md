# 上下文管理（Context Management）详解

> 上下文窗口是 LLM 的"工作记忆"——管理好它，决定了模型能力的上限。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [08-context-management/](./08-context-management/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | 上下文窗口基础 | [01-context-window-fundamentals.md](./08-context-management/01-context-window-fundamentals.md) |
> | KV Cache 深度优化 | [02-kv-cache-optimization.md](./08-context-management/02-kv-cache-optimization.md) |
> | Prefix Caching 技术 | [03-prefix-caching.md](./08-context-management/03-prefix-caching.md) |
> | 长上下文推理 | [04-long-context-inference.md](./08-context-management/04-long-context-inference.md) |
> | Chunked Prefill | [05-chunked-prefill.md](./08-context-management/05-chunked-prefill.md) |
> | Prefill/Decode 分离架构 | [06-disaggregated-serving.md](./08-context-management/06-disaggregated-serving.md) |
> | 上下文工程与压缩 | [07-context-engineering.md](./08-context-management/07-context-engineering.md) |

---

## 目录

- [为什么需要上下文管理](#为什么需要上下文管理)
- [上下文窗口基础](#上下文窗口基础)
- [KV Cache：上下文的代价](#kv-cache上下文的代价)
- [Prefix Caching：复用是最好的优化](#prefix-caching复用是最好的优化)
- [长上下文推理](#长上下文推理)
- [Chunked Prefill](#chunked-prefill)
- [Prefill/Decode 分离](#prefill-decode-分离)
- [上下文压缩与工程实践](#上下文压缩与工程实践)
- [技术栈全景](#技术栈全景)
- [实战练习](#实战练习)

---

## 为什么需要上下文管理

### 核心矛盾

LLM 的上下文窗口就像人的"工作记忆"——你同时能记住的信息量是有限的。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       上下文管理的核心矛盾                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  用户需求                          系统约束                              │
│  ├── 更长的对话记忆               ├── 显存 = O(seq_len)                  │
│  ├── 更大的文档分析               ├── 计算 = O(seq_len²)                 │
│  ├── 更复杂的 Agent 任务          ├── 首 Token 延迟 ∝ seq_len            │
│  └── 更低的推理成本               └── 成本 ∝ input_tokens                │
│                                                                         │
│  矛盾：用户想要无限上下文，但每多一个 Token 都在增加显存和计算开销         │
│                                                                         │
│  ┌──────────────────────────────────────────────────┐                   │
│  │           上下文管理 = 在这两者之间找最优解          │                   │
│  │                                                    │                   │
│  │  • 怎么装更多？——长上下文技术、位置编码扩展          │                   │
│  │  • 怎么省显存？——KV Cache 优化、量化、淘汰           │                   │
│  │  • 怎么加速？  ——Chunked Prefill、PD 分离           │                   │
│  │  • 怎么复用？  ——Prefix Caching、Prompt 缓存        │                   │
│  │  • 怎么压缩？  ——Prompt 压缩、摘要、RAG 替代        │                   │
│  └──────────────────────────────────────────────────┘                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 生活类比：图书馆的阅览桌

想象你在图书馆做研究：

- **上下文窗口** = 你的阅览桌大小（能同时摊开多少本书）
- **KV Cache** = 桌上每本打开的书占用的面积
- **Prefix Caching** = 常用参考书一直留在桌上，不用每次都去书架取
- **Chunked Prefill** = 一本大书先翻目录，再按需翻到具体章节
- **PD 分离** = 让助手帮你翻书找页码（Prefill），你只负责阅读（Decode）
- **上下文压缩** = 把 3 本参考书的要点整理成一页便签

### 上下文管理在 AI Infra 中的位置

```
┌─────────────────────────────────────────────────────────────┐
│                     AI Infra 技术栈                          │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  应用层: ChatBot / Agent / RAG / Code Assistant              │
│           ▲                                                  │
│           │ 上下文窗口使用策略                                 │
│  ┌────────┴────────────────────────────────────────┐        │
│  │         ★ 上下文管理层 (本章)  ★                  │        │
│  │  Prefix Caching | KV Cache 优化 | 上下文压缩     │        │
│  │  长上下文推理 | Chunked Prefill | PD 分离         │        │
│  └────────┬────────────────────────────────────────┘        │
│           │                                                  │
│  推理服务层: vLLM / SGLang / TensorRT-LLM / TGI             │
│           │                                                  │
│  计算层:   GPU / Tensor Core / NVLink / InfiniBand           │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## 上下文窗口基础

### 什么是上下文窗口

上下文窗口（Context Window）是 LLM 单次能处理的最大 Token 数，包括输入（Prompt）和输出（Generation）。

```
┌─────────── 上下文窗口 (Context Window) ──────────────┐
│                                                        │
│  [System Prompt] [User History] [Documents] [Query]    │
│  ←──────────── Input Tokens ──────────────→ [Response] │
│                                              ←Output─→ │
│                                                        │
│  Input + Output ≤ Context Window Size                  │
└────────────────────────────────────────────────────────┘
```

### 主流模型上下文窗口对比

| 模型 | 上下文窗口 | 等价文本量 | 发布时间 |
|------|-----------|-----------|---------|
| GPT-3 | 2K | ~1,500 字 | 2020 |
| GPT-3.5 | 4K / 16K | ~12,000 字 | 2023 |
| GPT-4 | 8K / 128K | ~100,000 字 | 2023 |
| GPT-4o | 128K | ~100,000 字 | 2024 |
| Claude 3.5 Sonnet | 200K | ~150,000 字 | 2024 |
| Gemini 1.5 Pro | 1M / 2M | ~1,500,000 字 | 2024 |
| LLaMA 3.1 | 128K | ~100,000 字 | 2024 |
| Qwen2.5 | 128K (原生 32K) | ~100,000 字 | 2024 |
| DeepSeek-V3 | 128K | ~100,000 字 | 2024 |

> 📖 上下文窗口的演进历史和位置编码原理详见 [01-context-window-fundamentals.md](./08-context-management/01-context-window-fundamentals.md)

### 标称窗口 vs 有效上下文

**关键认知：模型声称支持 128K 上下文，不代表它能"均匀地利用"128K 上下文。**

```
                         "Lost in the Middle" 现象
  
  检索准确率
  100% ┤████                                             ████
       │████                                             ████
   80% ┤████                                             ████
       │████                                             ████
   60% ┤████  ▓▓▓▓                                ▓▓▓▓  ████
       │████  ▓▓▓▓  ░░░░                    ░░░░  ▓▓▓▓  ████
   40% ┤████  ▓▓▓▓  ░░░░  ░░░░  ░░░░  ░░░░  ░░░░  ▓▓▓▓  ████
       │████  ▓▓▓▓  ░░░░  ░░░░  ░░░░  ░░░░  ░░░░  ▓▓▓▓  ████
   20% ┤████  ▓▓▓▓  ░░░░  ░░░░  ░░░░  ░░░░  ░░░░  ▓▓▓▓  ████
       │████  ▓▓▓▓  ░░░░  ░░░░  ░░░░  ░░░░  ░░░░  ▓▓▓▓  ████
    0% ┼────┬──────┬──────┬──────┬──────┬──────┬──────┬────────
       开头  1/7   2/7   3/7   4/7   5/7   6/7  结尾
                        关键信息在上下文中的位置
  
  结论：模型对开头和结尾的信息记忆最好，中间的信息容易被"遗忘"
```

**实际影响**：

| 场景 | 标称窗口 | 实际有效利用 | 原因 |
|------|---------|-------------|------|
| 单轮 QA | 128K | ~80K | Lost in the Middle |
| 多轮对话 | 128K | ~32K | 历史累积噪声 |
| RAG 检索 | 128K | ~8K-16K | 塞太多 chunk 反而降质 |
| 代码补全 | 128K | ~16K-32K | 远处代码相关性低 |

### 显存与计算的代价

上下文不是免费的——每多一个 Token，都有成本：

```
显存成本：KV Cache = 2 × layers × kv_heads × head_dim × 2bytes × seq_len
                   = O(seq_len)

计算成本：Self-Attention = O(seq_len²) × head_dim
         （FlashAttention 不改变 FLOPs，只优化内存访问模式）

延迟成本：TTFT (Time to First Token) ∝ seq_len  (Prefill 阶段)
         TPS (Tokens per Second) 在长序列时下降（KV Cache 访问变慢）
```

**LLaMA-7B KV Cache 显存实例**（与 [03-inference-serving/05-kv-cache](./03-inference-serving/05-llm-inference-kv-cache.md) 一致）：

| 序列长度 | Batch=1 KV Cache | Batch=32 KV Cache | 占 80GB A100 比例 |
|---------|------------------|-------------------|------------------|
| 4K | 2 GB | 64 GB | 80% |
| 32K | 16 GB | 512 GB | 不可能单卡 |
| 128K | 64 GB | 2 TB | 不可能单卡 |

> 📖 KV Cache 计算公式推导和详细案例见 [03-inference-serving/05-llm-inference-kv-cache.md](./03-inference-serving/05-llm-inference-kv-cache.md)

---

## KV Cache：上下文的代价

KV Cache 是上下文管理中最核心的数据结构——它存储了模型"记住"上下文的全部信息。

> 📖 **前置知识**：KV Cache 的基础原理见 [03-inference-serving/05-llm-inference-kv-cache.md](./03-inference-serving/05-llm-inference-kv-cache.md)，PagedAttention 的分页管理见 [03-inference-serving/06-llm-inference-batching.md](./03-inference-serving/06-llm-inference-batching.md)。本节深入到**优化层面**。

### KV Cache 优化三板斧

```
                      KV Cache 优化策略全景
                              │
          ┌───────────────────┼───────────────────┐
          │                   │                   │
     ┌────▼─────┐       ┌────▼─────┐       ┌────▼─────┐
     │  量化压缩  │       │  淘汰策略  │       │ 结构优化  │
     │ (Quantize)│       │ (Evict)   │       │(Compress) │
     └────┬─────┘       └────┬─────┘       └────┬─────┘
          │                   │                   │
     FP16→INT8/FP8      H2O / Sink        GQA / MQA
     INT4 量化           Scissorhands       Cross-Layer
     ≈50-75% 压缩       保留关键 Token      Sharing
```

### 量化：用更少的 bit 存储 KV Cache

```python
# KV Cache 量化效果对比（LLaMA-7B, seq=4096, batch=1）
kv_cache_sizes = {
    "FP16 (原始)":    2 * 32 * 32 * 128 * 2 * 4096,  # 2 GB
    "INT8 (8-bit)":   2 * 32 * 32 * 128 * 1 * 4096,  # 1 GB  (-50%)
    "FP8 (8-bit)":    2 * 32 * 32 * 128 * 1 * 4096,  # 1 GB  (-50%)
    "INT4 (4-bit)":   2 * 32 * 32 * 128 * 0.5 * 4096, # 0.5 GB (-75%)
}

# vLLM 启用 FP8 KV Cache
# vllm serve meta-llama/Llama-3.1-8B --kv-cache-dtype fp8
```

### 淘汰：只保留"重要"的 Token

并非所有 Token 都同等重要——研究发现 Attention 呈现高度稀疏性：

```
H2O (Heavy-Hitter Oracle) 策略：
  ┌─────────────────────────────────────────────────┐
  │  Attention 分数分布（典型的一个 Head）              │
  │                                                   │
  │  Token:  [The] [cat] [sat] [on] [the] [mat] [.]  │
  │  Score:   0.35  0.02  0.01  0.01  0.01  0.58 0.02 │
  │           ████       ░░░░  ░░░░  ░░░░  █████      │
  │           ↑                              ↑         │
  │         Heavy Hitter                  Heavy Hitter │
  │                                                   │
  │  策略：只保留累积 Attention > 阈值的 Token           │
  │        丢弃"旁观者" Token → 显存减少 ~70%           │
  └─────────────────────────────────────────────────┘

StreamingLLM Attention Sink 策略：
  ┌─────────────────────────────────────────────────┐
  │  观察：前几个 Token 总是获得高 Attention（Sink）    │
  │                                                   │
  │  保留策略 = [前 4 个 Sink Token] + [最近 N 个 Token]│
  │                                                   │
  │  [Sink₁][Sink₂][Sink₃][Sink₄]...[T_{n-N}]...[Tₙ] │
  │   ████  ████  ████  ████  丢弃   ████████████████  │
  │                                                   │
  │  优势：支持"无限"上下文长度                          │
  │  代价：中间信息全部丢失                              │
  └─────────────────────────────────────────────────┘
```

### GQA/MQA：从架构层面减少 KV Cache

| 方案 | KV Head 数 | KV Cache 大小 | 质量影响 |
|------|-----------|--------------|---------|
| MHA (Multi-Head) | = Q Head 数 | 基准 (1×) | 最高 |
| GQA (Grouped-Query) | Q Head / G | 1/G × 基准 | 接近 MHA |
| MQA (Multi-Query) | 1 | 1/H × 基准 | 略有下降 |

**LLaMA 系列的 KV Cache 对比**：

| 模型 | Q Heads | KV Heads | GQA 比例 | 4K seq KV Cache |
|------|---------|----------|---------|----------------|
| LLaMA-7B (MHA) | 32 | 32 | 1:1 | 2 GB |
| LLaMA-2 70B (GQA) | 64 | 8 | 8:1 | 1.6 GB |
| LLaMA-3.1 8B (GQA) | 32 | 8 | 4:1 | 0.5 GB |

> 📖 KV Cache 优化的完整技术细节见 [02-kv-cache-optimization.md](./08-context-management/02-kv-cache-optimization.md)

---

## Prefix Caching：复用是最好的优化

### 核心观察

在实际应用中，大量请求共享相同的前缀：

```
场景 1：多轮对话（System Prompt 不变）
  请求 1: [System Prompt 2000 tokens] + [User: 你好]
  请求 2: [System Prompt 2000 tokens] + [User: 你好] + [Asst: ...] + [User: 继续]
  请求 3: [System Prompt 2000 tokens] + [User: 你好] + [Asst: ...] + [User: 继续] + [Asst: ...] + [User: 总结]
          └──────── 共享前缀 ────────┘

场景 2：RAG 应用（相同的检索结果被多次引用）
  请求 1: [System] + [Doc A + Doc B + Doc C] + [Question 1]
  请求 2: [System] + [Doc A + Doc B + Doc C] + [Question 2]
                      └──── 共享前缀 ─────┘

场景 3：Agent 工具调用（Tool 描述每次都带）
  每次调用: [System] + [Tool Desc × 20] + [History] + [Current Task]
                       └── 共享前缀 ──┘
```

**如果能缓存这些共享前缀的 KV Cache，就不需要每次重新计算。**

### vLLM Automatic Prefix Caching (APC)

```
# vLLM APC 工作原理

请求 1: "The quick brown fox" → 计算 KV Cache → 存入缓存
请求 2: "The quick brown fox jumps" 
         └─── 命中缓存 ───┘  └ 只算这个 ┘

实现方式：
  ┌────────────────────────────────────────────────┐
  │  Token Hash Table                               │
  │                                                 │
  │  hash("The quick brown") → Block #42 (KV)      │
  │  hash("The quick brown fox") → Block #43 (KV)  │
  │  hash("The quick brown fox jumps") → Block #44  │
  │                                                 │
  │  新请求 "The quick brown fox runs"               │
  │  → Block #42 ✅ 命中                             │
  │  → Block #43 ✅ 命中                             │
  │  → "runs" 只需计算 1 个新 block                   │
  └────────────────────────────────────────────────┘
```

```python
# vLLM 启用 Automatic Prefix Caching
from vllm import LLM, SamplingParams

llm = LLM(
    model="meta-llama/Llama-3.1-8B-Instruct",
    enable_prefix_caching=True,  # 开启 APC
    gpu_memory_utilization=0.9,
)

# System Prompt 只在第一次请求时计算，后续全部复用
system_prompt = "You are a helpful assistant specialized in AI infrastructure..."

# 第一次请求：Prefill System Prompt + User Query
response1 = llm.generate([f"{system_prompt}\nUser: What is KV Cache?"], 
                         SamplingParams(max_tokens=200))

# 第二次请求：System Prompt 部分直接复用缓存的 KV Cache
response2 = llm.generate([f"{system_prompt}\nUser: How does PagedAttention work?"],
                         SamplingParams(max_tokens=200))
# → response2 的 Prefill 速度显著加快
```

### SGLang RadixAttention

SGLang 使用 **Radix Tree（基数树）** 管理 KV Cache 的复用，相比 vLLM 的 Hash 方案有更高效的前缀匹配：

```
                    Radix Tree 结构
                        (root)
                       /      \
              "System prompt"   "Few-shot examples"
                /      \              \
           "User: Q1"  "User: Q2"   "User: Q3"
            /              \
        "Asst: A1"     "Asst: A2"

优势：
1. 自动发现最长公共前缀（不依赖固定 block 对齐）
2. 支持多分支共享（一棵树管理所有活跃请求）
3. LRU 淘汰策略：不活跃的分支自动回收
```

> 📖 Prefix Caching 的完整实现细节和性能分析见 [03-prefix-caching.md](./08-context-management/03-prefix-caching.md)

---

## 长上下文推理

### 核心挑战

从 4K 扩展到 128K 甚至 1M 上下文，面临三大挑战：

| 挑战 | 根因 | 量化影响 |
|------|------|---------|
| 位置编码外推失败 | 模型只见过训练长度内的位置 | PPL 在超过训练长度后剧增 |
| 显存爆炸 | KV Cache ∝ seq_len | 128K seq: 64GB KV Cache (LLaMA-7B) |
| 注意力稀释 | Softmax 在长序列上"平均化" | 关键信息被噪声淹没 |

### RoPE 扩展方案对比

RoPE（Rotary Position Embedding）是当前主流 LLM 使用的位置编码。扩展到更长上下文的关键是修改 RoPE 的频率：

```
原始 RoPE: θ_i = 10000^(-2i/d)    训练长度 = L

扩展方法：

1. PI (Position Interpolation)
   θ'_i = θ_i                       位置 m' = m × (L/L')
   原理：把新位置"压缩"到训练长度范围内
   缺点：高频信息丢失 → 短序列性能下降

2. NTK-aware Scaling
   θ'_i = (10000 × α)^(-2i/d)      α = (L'/L)^(d/(d-2))
   原理：修改基数，低频外推 + 高频保留
   优点：不需要微调即可使用

3. Dynamic NTK
   α 随实际序列长度动态调整
   短序列用原始 θ，长序列逐渐增大 α
   
4. YaRN (Yet another RoPE extensioN)
   结合 NTK + 注意力缩放 + 分段插值
   短距离精确 + 长距离外推
   效果：4K→128K 仅需少量微调数据

5. Code LLaMA 方案
   θ'_i = 10000000^(-2i/d) (直接增大基数到 10^7)
   大力出奇迹，但需要大量长序列微调
```

**方案对比**：

| 方案 | 需要微调 | 短序列影响 | 扩展倍数 | 代表模型 |
|------|---------|----------|---------|---------|
| PI | 少量 | 略有下降 | 4-8× | CodeLlama-PI |
| NTK-aware | 不需要 | 无 | 2-4× | 各开源社区 |
| Dynamic NTK | 不需要 | 无 | 4-8× | Qwen |
| YaRN | 少量 | 极小 | 16-64× | Yarn-LLaMA |
| 增大基数 | 大量 | 无 | 32× | LLaMA 3.1 |

> 📖 RoPE 扩展的数学推导和实验数据见 [04-long-context-inference.md](./08-context-management/04-long-context-inference.md)

---

## Chunked Prefill

### 问题：长 Prompt 阻塞推理

```
传统 Prefill 的问题：

时间线 ──────────────────────────────────────────────→

GPU:  [====== 128K Prompt Prefill (数十秒) ======][D][D][D]...
                                                   ↑
其他请求：                                      全部排队等待
       [请求B 等待...] [请求C 等待...] [请求D 等待...]

问题：一个 128K 的 Prefill 占满 GPU 数十秒，其他请求"饿死"
```

### 解决方案：分块处理

```
Chunked Prefill：把长 Prompt 分成小块，与 Decode 交替执行

时间线 ──────────────────────────────────────────────→

GPU:  [Chunk1][D][D][Chunk2][D][D][Chunk3][D][D]...

请求A: [===Prefill Chunk 1===]     [===Chunk 2===]     [===Chunk 3===]
请求B:                       [D][D]             [D][D]              [D][D]
请求C:                       [D]                [D]                 [D]

优势：
✅ 请求 B、C 不再被长 Prefill 阻塞
✅ GPU 利用率更高（Prefill + Decode 混合执行）
✅ P99 延迟大幅降低
```

```python
# vLLM 启用 Chunked Prefill
from vllm import LLM

llm = LLM(
    model="meta-llama/Llama-3.1-8B-Instruct",
    enable_chunked_prefill=True,    # 启用分块 Prefill
    max_num_batched_tokens=2048,    # 每个调度周期最多处理 2048 tokens
)
# max_num_batched_tokens 越小，公平性越好，但 Prefill 吞吐略降
```

> 📖 Chunked Prefill 的调度算法和最优 Chunk Size 分析见 [05-chunked-prefill.md](./08-context-management/05-chunked-prefill.md)

---

## Prefill/Decode 分离

### 为什么要分离

Prefill 和 Decode 的计算特征截然不同，混合调度效率低：

```
┌──────────────────────────────────────────────────────┐
│               Prefill vs Decode 特征对比              │
├──────────────────┬─────────────────┬─────────────────┤
│                  │    Prefill      │     Decode       │
├──────────────────┼─────────────────┼─────────────────┤
│ 计算模式         │ Compute-bound   │ Memory-bound     │
│ 并行度           │ 高（批量矩阵乘） │ 低（逐 Token）   │
│ GPU 利用率       │ ~70-90%         │ ~10-30%          │
│ 关键资源         │ FLOPS           │ 显存带宽          │
│ 理想 GPU         │ H100 (高算力)    │ L40S (大显存)    │
│ Batch 策略       │ 大 chunk         │ 大 batch          │
└──────────────────┴─────────────────┴─────────────────┘

混合调度的问题：
  Prefill 需要大量 FLOPS → 占满计算单元 → Decode 被阻塞
  Decode 需要大量带宽   → KV Cache 访问慢 → Prefill 等内存

分离后：
  Prefill 节点：高算力 GPU，专注计算 → 高 FLOPS 利用率
  Decode 节点： 大显存 GPU，专注服务 → 高带宽利用率
```

### PD 分离架构

```
┌─────────────────────────────────────────────────────────────┐
│                    PD 分离架构                                │
│                                                              │
│  Request ──→ [Router/Scheduler]                              │
│                    │                                         │
│          ┌─────────┴──────────┐                              │
│          ▼                    ▼                               │
│  ┌───────────────┐   ┌───────────────┐                      │
│  │ Prefill Pool  │   │ Decode Pool   │                      │
│  │ (H100 × N)    │   │ (L40S × M)   │                      │
│  │               │   │               │                      │
│  │ 计算 KV Cache │──→│ 接收 KV Cache │                      │
│  │               │ ↗ │ 逐 Token 生成  │                      │
│  └───────────────┘   └───────────────┘                      │
│                  KV Cache 传输                                │
│             (RDMA / NVLink / TCP)                             │
│                                                              │
│  关键挑战：KV Cache 传输延迟                                   │
│  LLaMA-70B, 4K seq: ~3.2 GB KV Cache                        │
│  需要 RDMA (200 Gbps) → 传输时间 ~128ms                      │
└─────────────────────────────────────────────────────────────┘
```

**业界方案对比**：

| 方案 | 传输方式 | 特点 | 开源 |
|------|---------|------|------|
| DistServe | RDMA | 学术方案，理论分析完善 | 论文 |
| Splitwise | RDMA | 微软方案，异构 GPU | 论文 |
| Mooncake | KVCache 共享池 | 月之暗面生产系统，分离式存储 | 论文 |
| TensorRT-LLM | NIXL | NVIDIA 官方，NVLink 优化 | ✅ |
| vLLM (v0.8+) | 支持 PD 分离 | 社区方案，持续迭代 | ✅ |

> 📖 PD 分离的网络带宽计算和部署案例见 [06-disaggregated-serving.md](./08-context-management/06-disaggregated-serving.md)

---

## 上下文压缩与工程实践

当上下文窗口不够用时，"压缩"比"扩展"往往更实用。

### 策略选择决策树

```
                  上下文不够用了？
                       │
              ┌────────┴─────────┐
              │                  │
         输入太长？           需要记忆？
              │                  │
    ┌─────────┼──────┐     ┌─────┼─────┐
    │         │      │     │           │
  文档类    对话类  代码类  多轮对话    Agent
    │         │      │     │           │
  RAG       摘要    相关   滑动窗口   工具描述
  替代      压缩    代码   + 摘要     缓存
                   检索
```

### Prompt 压缩

```python
# LLMLingua: 压缩 Prompt 但保留语义
from llmlingua import PromptCompressor

compressor = PromptCompressor(
    model_name="microsoft/llmlingua-2-bert-base-multilingual-cased-meetingbank",
    device_map="cuda"
)

# 原始 Prompt (3000 tokens)
original_prompt = """
[大量检索文档内容...]
Based on the above context, please answer: What is KV Cache?
"""

# 压缩到 ~900 tokens (压缩率 ~3x)
compressed = compressor.compress_prompt(
    original_prompt,
    rate=0.3,           # 保留 30% 的 token
    force_tokens=["KV Cache", "answer"],  # 强制保留关键词
)
print(f"原始: {compressed['origin_tokens']} tokens")
print(f"压缩后: {compressed['compressed_tokens']} tokens")
print(f"压缩率: {compressed['ratio']:.1f}x")
```

### StreamingLLM：无限上下文的近似方案

```
StreamingLLM 原理：

普通 LLM 的 KV Cache 管理：
  [T₁][T₂][T₃]...[T_{n-1}][Tₙ] ← 全部保留，显存持续增长

StreamingLLM 的滑动窗口：
  [Sink₁][Sink₂][Sink₃][Sink₄] + [T_{n-W}]...[T_{n-1}][Tₙ]
   └── 4 个 Attention Sink ──┘   └── 最近 W 个 Token ──┘

  关键发现："Attention Sink"——前几个 Token 在所有层的 Attention 中
           都获得异常高的分数，即使它们在语义上不重要。
           保留这些 Sink Token 是稳定推理的关键。

适用场景：
  ✅ 超长对话流（不需要精确回忆历史）
  ✅ 流式文本处理（日志分析、实时翻译）
  ❌ 需要精确检索历史信息的场景
```

### 应用层上下文管理最佳实践

```
┌─────────────────────────────────────────────────────────────┐
│              应用层上下文分配策略                               │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Context Window = 128K tokens                                │
│                                                              │
│  推荐分配：                                                   │
│  ┌──────────────┬──────┬──────────────────┬────────────┐    │
│  │ System Prompt │ RAG  │ Conversation     │ Generation │    │
│  │   (2-4K)     │(4-8K)│ History (8-16K)  │  (4-8K)    │    │
│  └──────────────┴──────┴──────────────────┴────────────┘    │
│                                                              │
│  最佳实践：                                                   │
│  1. System Prompt 放最前面（利用首位记忆优势）                  │
│  2. RAG 结果排序后只取 Top-K（质量 > 数量）                    │
│  3. 对话历史用滑动窗口 + 摘要（近期完整，远期摘要）             │
│  4. 预留足够的生成空间（避免截断）                              │
│  5. 关键信息放开头和结尾（避免 Lost in the Middle）            │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

> 📖 完整的上下文工程策略和技术栈选型决策树见 [07-context-engineering.md](./08-context-management/07-context-engineering.md)

---

## 技术栈全景

### 上下文管理完整技术栈

| 层级 | 技术 | 开源工具 | 作用 |
|------|------|---------|------|
| **位置编码** | RoPE / ALiBi / YaRN | HuggingFace Transformers | 支持长上下文 |
| **注意力优化** | FlashAttention / Ring Attention | flash-attn, DeepSpeed | 降低显存/提速 |
| **KV Cache 管理** | PagedAttention / RadixAttention | vLLM, SGLang | 显存效率最大化 |
| **KV Cache 压缩** | FP8 量化 / H2O 淘汰 / GQA | vLLM, TensorRT-LLM | 减少 KV 显存 |
| **前缀复用** | Prefix Caching / APC | vLLM, SGLang | 避免重复计算 |
| **长序列训练** | 序列并行 / Ring Attention | Megatron-LM, DeepSpeed | 训练长上下文模型 |
| **调度优化** | Chunked Prefill | vLLM, Sarathi | 降低 P99 延迟 |
| **架构优化** | PD 分离 | DistServe, TRT-LLM | 异构资源利用 |
| **上下文压缩** | LLMLingua / Prompt 压缩 | llmlingua | 减少 token 数 |
| **应用层** | RAG / 滑动窗口 / 摘要 | LangChain, LlamaIndex | 上层策略 |

### 选型决策树

```
                    你的场景？
                       │
        ┌──────────────┼──────────────┐
        │              │              │
    高吞吐服务      低延迟服务      成本敏感
        │              │              │
  ┌─────┴─────┐   ┌────┴────┐    ┌───┴───┐
  │           │   │         │    │       │
Prefix    PD 分离 Chunked  小窗口  KV     上下文
Caching          Prefill  模型   量化    压缩
```

---

## 实战练习

### 练习 1：测量 Prefix Caching 效果

```python
"""
测量 vLLM Prefix Caching 对延迟的影响
"""
import time
from vllm import LLM, SamplingParams

# 准备长 System Prompt
system_prompt = "You are an expert AI infrastructure engineer. " * 200  # ~1000 tokens

def benchmark(enable_prefix_caching: bool, num_requests: int = 10):
    llm = LLM(
        model="meta-llama/Llama-3.1-8B-Instruct",
        enable_prefix_caching=enable_prefix_caching,
        gpu_memory_utilization=0.9,
    )
    
    prompts = [
        f"{system_prompt}\nUser: Question {i}\nAssistant:"
        for i in range(num_requests)
    ]
    params = SamplingParams(max_tokens=100)
    
    start = time.time()
    outputs = llm.generate(prompts, params)
    elapsed = time.time() - start
    
    print(f"Prefix Caching={'ON' if enable_prefix_caching else 'OFF'}")
    print(f"  Total time: {elapsed:.2f}s")
    print(f"  Avg per request: {elapsed/num_requests:.3f}s")
    return elapsed

# 对比测试
t_off = benchmark(enable_prefix_caching=False)
t_on = benchmark(enable_prefix_caching=True)
print(f"\n加速比: {t_off/t_on:.2f}x")
```

### 练习 2：KV Cache 显存计算器

```python
"""
通用 KV Cache 显存计算器
"""
def kv_cache_memory(
    num_layers: int,
    num_kv_heads: int,
    head_dim: int,
    seq_length: int,
    batch_size: int = 1,
    dtype_bytes: int = 2,  # FP16=2, FP8=1, INT4=0.5
) -> dict:
    """计算 KV Cache 显存占用"""
    # 公式：2 × layers × kv_heads × head_dim × dtype × seq × batch
    kv_bytes = 2 * num_layers * num_kv_heads * head_dim * dtype_bytes * seq_length * batch_size
    
    return {
        "total_bytes": kv_bytes,
        "total_gb": kv_bytes / (1024**3),
        "per_token_bytes": 2 * num_layers * num_kv_heads * head_dim * dtype_bytes,
        "per_token_kb": 2 * num_layers * num_kv_heads * head_dim * dtype_bytes / 1024,
    }

# LLaMA-3.1 8B (GQA: 32 Q heads, 8 KV heads)
result = kv_cache_memory(
    num_layers=32, num_kv_heads=8, head_dim=128,
    seq_length=128_000, batch_size=1, dtype_bytes=2
)
print(f"LLaMA-3.1 8B, 128K context, FP16:")
print(f"  KV Cache = {result['total_gb']:.1f} GB")
print(f"  Per token = {result['per_token_kb']:.1f} KB")

# 对比 FP8 量化
result_fp8 = kv_cache_memory(
    num_layers=32, num_kv_heads=8, head_dim=128,
    seq_length=128_000, batch_size=1, dtype_bytes=1
)
print(f"\nLLaMA-3.1 8B, 128K context, FP8:")
print(f"  KV Cache = {result_fp8['total_gb']:.1f} GB  (节省 {(1-result_fp8['total_gb']/result['total_gb'])*100:.0f}%)")
```

---

## 🔗 相关章节

- **前置**：[03-inference-serving](./03-inference-serving/) — KV Cache 基础、PagedAttention、FlashAttention
- **前置**：[00-training-fundamentals/10-transformer-architecture](./00-training-fundamentals/10-transformer-architecture.md) — Transformer 架构、位置编码
- **相关**：[02-distributed-training/10-sequence-parallelism](./02-distributed-training/10-sequence-parallelism.md) — 序列并行（训练侧长上下文）
- **相关**：[07-knowledge-base/10-token-optimization](./07-knowledge-base/10-token-optimization.md) — Token 节省策略（应用层）
- **后续**：[06-learning-roadmap](./06-learning-roadmap/) — 学习路线图

---

## 📚 参考资料与引用

### 必读论文

1. Kwon, W., et al. (2023). *Efficient Memory Management for Large Language Model Serving with PagedAttention*. SOSP 2023. arXiv:2309.06180. https://arxiv.org/abs/2309.06180
2. Dao, T. (2023). *FlashAttention-2: Faster Attention with Better Parallelism and Work Partitioning*. arXiv:2307.08691. https://arxiv.org/abs/2307.08691
3. Xiao, G., et al. (2023). *Efficient Streaming Language Models with Attention Sinks*. arXiv:2309.17453. https://arxiv.org/abs/2309.17453
4. Zhang, Z., et al. (2023). *H2O: Heavy-Hitter Oracle for Efficient Generative Inference of Large Language Models*. arXiv:2306.14048. https://arxiv.org/abs/2306.14048
5. Peng, B., et al. (2023). *YaRN: Efficient Context Window Extension of Large Language Models*. arXiv:2309.00071. https://arxiv.org/abs/2309.00071
6. Zhong, Y., et al. (2024). *DistServe: Disaggregating Prefill and Decoding for Goodput-optimized Large Language Model Serving*. arXiv:2401.09670. https://arxiv.org/abs/2401.09670
7. Qin, R., et al. (2024). *Mooncake: A KVCache-centric Disaggregated Architecture for LLM Serving*. arXiv:2407.00079. https://arxiv.org/abs/2407.00079
8. Zheng, L., et al. (2023). *SGLang: Efficient Execution of Structured Language Model Programs*. arXiv:2312.07104. https://arxiv.org/abs/2312.07104
9. Jiang, H., et al. (2023). *LLMLingua: Compressing Prompts for Accelerated Inference of Large Language Models*. arXiv:2310.05736. https://arxiv.org/abs/2310.05736
10. Liu, N., et al. (2023). *Lost in the Middle: How Language Models Use Long Contexts*. arXiv:2307.03172. https://arxiv.org/abs/2307.03172
11. Agrawal, A., et al. (2024). *Sarathi-Serve: Chunked-Prefills for SLO-compliant LLM Serving*. arXiv:2403.02310. https://arxiv.org/abs/2403.02310
