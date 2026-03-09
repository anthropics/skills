# KV Cache 深度优化

> KV Cache 是 LLM 推理的"内存管家"——它记住了模型看过的所有内容，但如果管理不善，它会吃掉你所有的显存。

## 目录

- [KV Cache 回顾与瓶颈](#kv-cache-回顾与瓶颈)
- [优化方向一：量化压缩](#优化方向一量化压缩)
- [优化方向二：淘汰策略](#优化方向二淘汰策略)
- [优化方向三：结构优化](#优化方向三结构优化)
- [KV Cache 管理框架对比](#kv-cache-管理框架对比)
- [综合优化策略](#综合优化策略)

---

## KV Cache 回顾与瓶颈

> 📖 KV Cache 基础原理见 [03-inference-serving/05-llm-inference-kv-cache.md](../03-inference-serving/05-llm-inference-kv-cache.md)

### 为什么 KV Cache 是瓶颈

```
LLM 推理的两阶段：

Prefill 阶段（一次性计算）：
  Input: "The quick brown fox jumps over the lazy dog"
  → 对每个 Token 计算 Q, K, V
  → 存储所有 K, V 到 KV Cache
  → 计算 Self-Attention 得到第一个输出 Token
  → 瓶颈：计算量（Compute-bound）

Decode 阶段（逐 Token 生成）：
  每生成一个新 Token：
  → 只计算新 Token 的 Q, K, V
  → 新的 K, V 追加到 KV Cache
  → 用 Q 与 *所有* 历史 K 做 Attention
  → 瓶颈：KV Cache 读取带宽（Memory-bound）

关键洞察：Decode 阶段，每生成一个 Token 都要读取整个 KV Cache
         → KV Cache 越大，每个 Token 生成越慢
         → 这就是为什么长上下文推理变慢的根本原因
```

### KV Cache 的显存构成

以 LLaMA-3.1 8B（32 层, 8 KV Heads, head_dim=128）为例：

```
场景：128K 上下文，Batch=1，FP16

KV Cache = 2 × 32 × 8 × 128 × 2 × 128,000
         = 16,777,216,000 bytes
         ≈ 15.6 GB

模型参数 = 8B × 2 bytes = 16 GB

对比：
  ┌──────────────────────────────────────────┐
  │  80 GB A100 显存分配                      │
  │                                           │
  │  ┌────────────┬───────────┬───────────┐  │
  │  │ 模型 16GB  │KV Cache   │ 剩余      │  │
  │  │ (20%)      │15.6GB     │~48GB      │  │
  │  │            │(20%)      │(60%)      │  │
  │  └────────────┴───────────┴───────────┘  │
  │                                           │
  │  → 单用户 128K 上下文：显存还够            │
  │  → 但如果 Batch=4：KV Cache = 62.4 GB     │
  │  → 模型(16) + KV(62.4) = 78.4 GB → 几乎满│
  │  → Batch=8：已经装不下！                   │
  │                                           │
  │  ★ 优化 KV Cache = 提高并发 = 降低成本 ★  │
  └──────────────────────────────────────────┘
```

---

## 优化方向一：量化压缩

### 核心思路

KV Cache 中每个元素默认用 FP16（2 bytes）存储，但实验表明 K/V 的数值范围有限，可以用更少的 bit 表示。

### INT8 / FP8 量化

```
KV Cache 量化的直觉：

FP16 (16 bit): ████████████████  → 精度高，显存大
FP8  (8 bit):  ████████          → 精度够用，显存减半
INT8 (8 bit):  ████████          → 精度够用，显存减半
INT4 (4 bit):  ████              → 精度有损，显存减 75%

量化公式（Per-channel INT8）：
  K_int8 = round(K_fp16 / scale) + zero_point
  scale = (K_max - K_min) / 255
  
  解量化：
  K_fp16 ≈ (K_int8 - zero_point) × scale
```

```python
# vLLM 启用 FP8 KV Cache（推荐方式）
# 命令行：
# vllm serve meta-llama/Llama-3.1-8B-Instruct \
#     --kv-cache-dtype fp8 \
#     --gpu-memory-utilization 0.9

# Python API：
from vllm import LLM, SamplingParams

llm = LLM(
    model="meta-llama/Llama-3.1-8B-Instruct",
    kv_cache_dtype="fp8",          # FP8 KV Cache
    gpu_memory_utilization=0.9,
)

# 效果：显存减少 ~50%，吞吐量提升 ~1.5-2x
# 质量：大多数任务几乎无损（<0.5% PPL 增加）
```

### INT4 量化：更激进的压缩

```
INT4 KV Cache 量化：

优势：显存减少 75%（128K seq: 15.6 GB → 3.9 GB）

挑战：
  - 4 bit 只有 16 个离散值，动态范围有限
  - K 和 V 的数值分布不同，需要分别处理
  - 某些层/头对量化更敏感

解决方案：
  1. Per-Head 量化（每个 Head 独立 scale/zero_point）
  2. 混合精度：敏感层用 INT8，其他层用 INT4
  3. 残差量化：先 INT8，再对残差 INT4
```

### 量化方案对比

| 方案 | 压缩率 | 质量影响 | 计算开销 | 框架支持 |
|------|--------|---------|---------|---------|
| FP16 (基准) | 1× | 无 | 无 | 所有 |
| FP8 (E4M3) | 2× | 几乎无损 | 极低 | vLLM, TRT-LLM |
| INT8 (Per-channel) | 2× | 几乎无损 | 低 | vLLM, TRT-LLM |
| INT4 (Per-group) | 4× | 轻微下降 | 中 | KIVI, TRT-LLM |
| 混合 INT4/INT8 | 2-4× | 可控 | 中 | 研究阶段 |

> **最佳实践**：生产环境推荐 **FP8 KV Cache**——压缩率 2×，质量几乎无损，主流框架原生支持。

---

## 优化方向二：淘汰策略

### 核心观察：Attention 是稀疏的

研究发现，在大多数 Attention Head 中，只有少数 Token 获得了大部分的 Attention 权重：

```
典型的 Attention 权重分布（一个 Head，一行）：

Token:   [The] [cat] [sat] [on]  [a]  [red] [mat] [and] [it] [was] [soft] [.]
Score:   0.31  0.02  0.01  0.01  0.01  0.02  0.55  0.01  0.02 0.01  0.02  0.01
         ████  ░░░░  ░░░░  ░░░░  ░░░░  ░░░░  ████  ░░░░  ░░░░ ░░░░  ░░░░  ░░░░
          ↑                                    ↑
       Heavy Hitter                     Heavy Hitter

发现：~5% 的 Token 集中了 ~80% 的 Attention 权重
含义：大部分 Token 的 KV Cache 在 Decode 时几乎没有被"看到"
结论：可以安全地淘汰低 Attention Token 的 KV Cache
```

### H2O (Heavy-Hitter Oracle)

```
H2O 算法：

核心策略：保留累积 Attention 权重最高的 Top-K Token

步骤：
  1. 维护一个"热度表"：记录每个 Token 被所有后续 Token 关注的总分数
  2. 当 KV Cache 达到预算上限时：
     - 计算所有 Token 的累积 Attention Score
     - 淘汰分数最低的 Token
     - 释放对应的 KV Cache 显存

示例（Budget = 6 tokens，当前 10 tokens）：

Token:        [A] [B] [C] [D] [E] [F] [G] [H] [I] [J]
累积 Score:   0.8 0.1 0.3 0.05 0.1 0.02 0.7 0.04 0.6 0.3

排序后：      A(0.8) > G(0.7) > I(0.6) > C(0.3) = J(0.3) > B(0.1) = E(0.1) > D(0.05) > H(0.04) > F(0.02)

保留 Top-6:   [A] ··· [C] ··· ··· ··· [G] ··· [I] [J]
淘汰 4 个:        [B]     [D] [E] [F]     [H]

效果：
  - KV Cache 减少 40%（10 → 6 tokens）
  - 输出质量几乎不变（因为淘汰的都是低权重 Token）
```

```python
# H2O 的简化实现思路
import torch

class H2OKVCache:
    """Heavy-Hitter Oracle KV Cache Manager"""
    
    def __init__(self, budget: int, num_layers: int, num_heads: int):
        self.budget = budget  # 最多保留多少个 token 的 KV
        self.cumulative_scores = {}  # {layer: {head: scores}}
    
    def update_scores(self, layer: int, head: int, attention_weights: torch.Tensor):
        """更新每个 token 的累积 attention score"""
        # attention_weights: [seq_len] (当前 token 对所有历史 token 的注意力)
        if (layer, head) not in self.cumulative_scores:
            self.cumulative_scores[(layer, head)] = torch.zeros(attention_weights.shape)
        self.cumulative_scores[(layer, head)] += attention_weights
    
    def evict(self, layer: int, head: int, k_cache: torch.Tensor, v_cache: torch.Tensor):
        """淘汰低分 token 的 KV Cache"""
        scores = self.cumulative_scores[(layer, head)]
        if len(scores) <= self.budget:
            return k_cache, v_cache
        
        # 保留分数最高的 Top-K
        _, top_indices = torch.topk(scores, self.budget)
        top_indices = top_indices.sort().values
        
        return k_cache[top_indices], v_cache[top_indices]
```

### StreamingLLM Attention Sink

```
StreamingLLM 的关键发现：

观察：无论输入多长，前几个 Token 总是获得异常高的 Attention 权重

Attention 热力图（一个 Head）：
  Query ↓  Key →  [T₁] [T₂] [T₃] [T₄] [T₅] ... [Tₙ₋₁] [Tₙ]
  [T₅]            0.3   0.0  0.0  0.0  0.7  ...   0.0    0.0
  [T₆]            0.2   0.0  0.0  0.0  0.0  ...   0.0    0.8
  ...
  [Tₙ]            0.15  0.0  0.0  0.0  0.0  ...   0.05   0.8
                   ↑                                       ↑
              "Sink Token"                          "Local Window"
              永远被关注                             最近的几个 Token

原因：
  Softmax 需要一个"垃圾桶"来放无关 Token 的注意力
  → 第一个 Token 天然成为"注意力汇点"（Attention Sink）
  → 即使语义上 [BOS] token 不重要，它在 Attention 中也承担了"稳定器"角色

StreamingLLM 策略：
  ┌─────────────────────────────────────────────────────┐
  │ 保留 = [前 4 个 Sink Token] + [最近 N 个 Token]      │
  │                                                      │
  │ 窗口大小 = 4 + N                                     │
  │                                                      │
  │ 时间步 t=100, N=32:                                  │
  │ [T₁][T₂][T₃][T₄] | [T₆₅][T₆₆]...[T₉₉][T₁₀₀]    │
  │ ←── Sink ──→        ←──── Recent Window ────→        │
  │                                                      │
  │ 时间步 t=10000, N=32:                                │
  │ [T₁][T₂][T₃][T₄] | [T₉₉₆₅]...[T₉₉₉₉][T₁₀₀₀₀]  │
  │ ←── Sink ──→        ←──── Recent Window ────→        │
  │                                                      │
  │ → KV Cache 大小永远 = 36 个 Token，无论对话多长       │
  └─────────────────────────────────────────────────────┘
```

```python
# StreamingLLM 的核心逻辑
class StreamingKVCache:
    """StreamingLLM: Attention Sink + Sliding Window"""
    
    def __init__(self, sink_size: int = 4, window_size: int = 1024):
        self.sink_size = sink_size      # 保留前几个 Sink Token
        self.window_size = window_size  # 滑动窗口大小
        self.k_cache = None
        self.v_cache = None
    
    def update(self, new_k: "Tensor", new_v: "Tensor"):
        """添加新 token 的 KV，并维持窗口大小"""
        if self.k_cache is None:
            self.k_cache = new_k
            self.v_cache = new_v
            return
        
        # 追加新 token
        self.k_cache = torch.cat([self.k_cache, new_k], dim=-2)
        self.v_cache = torch.cat([self.v_cache, new_v], dim=-2)
        
        total = self.k_cache.shape[-2]
        max_size = self.sink_size + self.window_size
        
        if total > max_size:
            # 保留 Sink + 最近 Window
            sink_k = self.k_cache[..., :self.sink_size, :]
            window_k = self.k_cache[..., -(self.window_size):, :]
            self.k_cache = torch.cat([sink_k, window_k], dim=-2)
            
            sink_v = self.v_cache[..., :self.sink_size, :]
            window_v = self.v_cache[..., -(self.window_size):, :]
            self.v_cache = torch.cat([sink_v, window_v], dim=-2)
```

### Scissorhands

```
Scissorhands 的核心发现：

"重要 Token 在过去的窗口中也曾经是重要的"
→ 一个 Token 如果在最近几步中从未获得高 Attention，未来也大概率不重要

策略：
  1. 维护一个"历史重要性窗口"（最近 H 步）
  2. 在每个窗口内，标记获得过高 Attention 的 Token
  3. 只保留在窗口内至少出现过一次的"重要 Token"
  
与 H2O 的区别：
  H2O: 看累积总分 → 偏向"永远重要的老 Token"
  Scissorhands: 看最近历史 → 更好地适应"动态重要性"
```

### 淘汰策略对比

| 策略 | KV Cache 减少 | 质量影响 | 适用场景 |
|------|-------------|---------|---------|
| 无淘汰（全保留） | 0% | 无 | 短上下文 |
| 滑动窗口 | 可控 | 丢失远期记忆 | 流式场景 |
| StreamingLLM | 90%+ | 丢失中间信息 | 超长对话流 |
| H2O | 50-80% | 极小 | 通用推理 |
| Scissorhands | 50-80% | 极小 | 动态上下文 |
| 混合（Sink + H2O） | 70-90% | 小 | 最佳综合 |

---

## 优化方向三：结构优化

### GQA (Grouped-Query Attention)

GQA 从模型架构层面减少 KV Cache——不是压缩已有的 KV，而是从根本上减少 KV Head 数。

```
MHA (Multi-Head Attention) — 传统方案：
  Q: 32 heads    K: 32 heads    V: 32 heads
  每个 Q head 对应独立的 K/V head
  KV Cache = 32 × head_dim × 2 (K+V) × dtype × seq_len

GQA (Grouped-Query Attention) — 主流方案：
  Q: 32 heads    K: 8 heads     V: 8 heads (4 Q heads 共享 1 KV head)
  每组 4 个 Q head 共享同一对 K/V
  KV Cache = 8 × head_dim × 2 (K+V) × dtype × seq_len → 减少 4×

MQA (Multi-Query Attention) — 极致压缩：
  Q: 32 heads    K: 1 head      V: 1 head (所有 Q 共享 1 KV)
  KV Cache = 1 × head_dim × 2 (K+V) × dtype × seq_len → 减少 32×
  代价：质量有一定下降
```

**GQA 在主流模型中的应用**：

| 模型 | Q Heads | KV Heads | GQA 比 | KV Cache vs MHA |
|------|---------|----------|--------|----------------|
| LLaMA-7B | 32 | 32 (MHA) | 1:1 | 1× (基准) |
| LLaMA-2 70B | 64 | 8 (GQA) | 8:1 | 0.125× |
| LLaMA-3.1 8B | 32 | 8 (GQA) | 4:1 | 0.25× |
| Mistral 7B | 32 | 8 (GQA) | 4:1 | 0.25× |
| Qwen2.5 72B | 64 | 8 (GQA) | 8:1 | 0.125× |
| DeepSeek-V3 | 128 | MLA | - | ~0.06× |

### MLA (Multi-Head Latent Attention)

DeepSeek-V2/V3 提出了 MLA——比 GQA 更激进的 KV Cache 压缩方案：

```
MLA 核心思路：

传统 GQA：
  存储 K: [layers × kv_heads × head_dim × seq]
  存储 V: [layers × kv_heads × head_dim × seq]

MLA：
  不直接存储 K 和 V，而是存储一个低秩压缩向量 c：
  c = compress(K, V)    # c 的维度远小于 K+V
  K, V = decompress(c)  # 推理时实时解压

  存储: [layers × compressed_dim × seq]  
  compressed_dim << 2 × kv_heads × head_dim

  DeepSeek-V3 (236B):
    KV Cache 压缩到 GQA 的 ~50%（相比 MHA 减少 ~93%）
    质量：优于 GQA（更高效地利用压缩维度）

代价：
  - 解压需要额外计算（但远小于 KV Cache 读取节省的带宽）
  - 模型架构绑定（只有 DeepSeek 系列使用）
```

### Cross-Layer KV Sharing

```
观察：相邻 Transformer 层的 KV Cache 高度相似

策略：让多层共享同一份 KV Cache

  传统：Layer 1 KV | Layer 2 KV | Layer 3 KV | Layer 4 KV  (4份)
  共享：Layer 1 KV = Layer 2 KV | Layer 3 KV = Layer 4 KV  (2份)

  进阶：每隔 N 层才计算新的 KV，中间层复用
  
  效果：KV Cache 减少 50-75%
  代价：质量略有下降，需要专门训练
```

---

## KV Cache 管理框架对比

### PagedAttention vs RadixAttention

```
┌────────────────────────────────────────────────────────────────┐
│              PagedAttention (vLLM)                               │
├────────────────────────────────────────────────────────────────┤
│                                                                 │
│  类比：OS 的虚拟内存分页管理                                      │
│                                                                 │
│  传统方式：为每个请求预分配最大长度的连续显存                       │
│  → 大量碎片和浪费                                                │
│                                                                 │
│  PagedAttention：                                               │
│  → 将 KV Cache 分成固定大小的 Block（如 16 tokens/block）         │
│  → Block 可以在物理显存中不连续                                   │
│  → 按需分配，用多少分多少                                        │
│  → 支持 Copy-on-Write（Beam Search 共享 Block）                  │
│                                                                 │
│  逻辑地址:  [0][1][2][3][4]        Block Table                   │
│              │  │  │  │  │         [0] → 物理 Block #7           │
│  物理显存:   不连续分布             [1] → 物理 Block #2           │
│  [#0][#1][#2][#3][#4][#5][#6][#7]  [2] → 物理 Block #5           │
│              ↑        ↑   ↑                                      │
│              [1]      [2] [0]                                    │
│                                                                 │
│  效果：显存利用率从 ~60% 提升到 ~95%                               │
└────────────────────────────────────────────────────────────────┘

┌────────────────────────────────────────────────────────────────┐
│              RadixAttention (SGLang)                             │
├────────────────────────────────────────────────────────────────┤
│                                                                 │
│  类比：文件系统的 Trie（前缀树）                                   │
│                                                                 │
│  在 PagedAttention 基础上，增加了 Prefix 复用：                    │
│  → 用 Radix Tree 管理所有活跃请求的 KV Cache                     │
│  → 自动发现最长公共前缀                                          │
│  → 公共前缀的 KV Block 在多个请求间共享                           │
│                                                                 │
│  Radix Tree:                                                    │
│              (root)                                              │
│             /      \                                             │
│       "System"    "Few-shot"                                    │
│       /     \          \                                        │
│   "Q: A"  "Q: B"    "Q: C"                                     │
│                                                                 │
│  共享 "System" 前缀 → 只存一份 → 3 个请求共享                    │
│                                                                 │
│  效果：在多轮对话/RAG 场景下，比 PagedAttention 快 2-5×           │
└────────────────────────────────────────────────────────────────┘
```

### 对比总结

| 维度 | PagedAttention (vLLM) | RadixAttention (SGLang) |
|------|----------------------|------------------------|
| 核心思路 | 分页管理，消除碎片 | 前缀树复用 |
| 显存利用率 | ~95% | ~95% + 前缀共享 |
| Prefix 复用 | APC (Hash 匹配) | Radix Tree（自动前缀匹配） |
| 复用粒度 | Block 级（需 Block 对齐） | Token 级（更灵活） |
| 适用场景 | 通用推理 | 多轮对话/Agent/RAG |
| 成熟度 | 生产就绪 | 生产就绪 |
| 社区活跃度 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |

---

## 综合优化策略

### 实际部署建议

```
┌─────────────────────────────────────────────────────────────┐
│             KV Cache 优化组合推荐                              │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  场景 1：通用 LLM 服务 (上下文 ≤ 32K)                        │
│  → PagedAttention + FP8 KV Cache + Prefix Caching            │
│  → 工具：vLLM                                                │
│  → 命令：vllm serve MODEL --kv-cache-dtype fp8               │
│          --enable-prefix-caching                              │
│                                                              │
│  场景 2：长上下文服务 (32K - 128K)                            │
│  → RadixAttention + FP8 KV Cache + GQA 模型                  │
│  → 工具：SGLang                                              │
│  → 选择 GQA 模型（如 LLaMA-3.1 而非 LLaMA-7B）               │
│                                                              │
│  场景 3：超长上下文/流式 (>128K 或无限)                       │
│  → StreamingLLM (Sink + Window) + FP8 量化                    │
│  → 适用于：日志分析、实时翻译、超长对话                       │
│  → 注意：会丢失中间历史信息                                   │
│                                                              │
│  场景 4：成本敏感 (最大化 batch/GPU)                          │
│  → INT4 KV Cache + H2O 淘汰 + Prefix Caching                │
│  → 组合可节省 80%+ KV Cache 显存                              │
│  → 需要验证质量在可接受范围内                                  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 优化效果汇总

| 优化技术 | KV Cache 节省 | 质量影响 | 实现难度 |
|---------|-------------|---------|---------|
| FP8 量化 | 50% | 几乎无损 | ★☆☆ (框架原生) |
| INT4 量化 | 75% | 轻微 | ★★☆ |
| H2O 淘汰 | 50-80% | 极小 | ★★☆ |
| StreamingLLM | 90%+ | 丢失中间 | ★★☆ |
| GQA (模型选择) | 75-87.5% | 无 | ★☆☆ (选模型) |
| MLA (DeepSeek) | 93%+ | 无 | N/A (模型内置) |
| Prefix Caching | 场景相关 | 无 | ★☆☆ (框架原生) |
| FP8 + GQA + APC | 87%+ | 几乎无损 | ★☆☆ |

---

*上一篇：[01-context-window-fundamentals.md](01-context-window-fundamentals.md) — 上下文窗口基础*

*下一篇：[03-prefix-caching.md](03-prefix-caching.md) — Prefix Caching 技术*

*返回目录：[README.md](README.md)*
