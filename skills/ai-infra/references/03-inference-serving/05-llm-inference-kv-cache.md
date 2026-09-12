# LLM 推理特性 - KV Cache

> 理解 KV Cache 的原理和显存占用 — LLM 推理的核心优化。

## 为什么需要 KV Cache

```
  类比: 重复考试

  没有 KV Cache (朴素自回归):
    第 1 步: 读题目 "What"                    → 答 "is"
    第 2 步: 重新读 "What is"                  → 答 "the"
    第 3 步: 重新读 "What is the"              → 答 "capital"
    第 4 步: 重新读 "What is the capital"      → 答 "of"
    → 每一步都要从头读所有已有的内容! 第 100 步要读 100 遍前面的!

  有 KV Cache:
    第 1 步: 读 "What" → 记住它的 K,V → 答 "is"
    第 2 步: 只读 "is"，前面的从笔记里查 → 答 "the"
    第 3 步: 只读 "the"，前面的从笔记里查 → 答 "capital"
    → 每步只处理 1 个新 token!

  计算量对比 (生成 N 个 token):
    无 Cache: 1 + 2 + 3 + ... + N = N(N+1)/2 ≈ O(N²)
    有 Cache: 1 + 1 + 1 + ... + 1 = N         ≈ O(N)
    → 生成 1000 token: 无 Cache 50 万次 vs 有 Cache 1000 次!
```

## KV Cache 原理

### Attention 中 K 和 V 的角色

```
  Attention(Q, K, V) = softmax(Q × K^T / √d) × V

  Q (Query)  = "我要找什么" — 当前 token 的提问
  K (Key)    = "我有什么标签" — 每个历史 token 的标签
  V (Value)  = "我的内容" — 每个历史 token 的信息

  类比: 图书馆找书
    Q = 你想找的主题 ("量子力学入门")
    K = 每本书封面的标签 (书名/关键词)
    V = 书的实际内容

    Q × K^T = 用主题去匹配每本书的标签 → 得到相关度分数
    softmax = 把分数变成概率 (最相关的书权重最大)
    × V     = 按权重加权读取各本书的内容 → 得到综合信息

  关键发现:
    历史 token 的 K 和 V 不会变! (因为权重固定，输入固定)
    只有新 token 需要新计算 Q, K, V
    → 把历史 K, V 缓存起来，每步只计算新 token 的 Q, K, V
```

### 工作机制

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  Prefill 阶段 (处理 prompt, 并行, Compute-bound):                │
  │                                                                  │
  │  Input: [t1, t2, t3, t4, t5]  (5 个 prompt token)               │
  │                                                                  │
  │  并行计算所有 token 的 Q, K, V:                                  │
  │  Q_all = [Q1, Q2, Q3, Q4, Q5]                                   │
  │  K_cache = [K1, K2, K3, K4, K5]  ← 缓存!                      │
  │  V_cache = [V1, V2, V3, V4, V5]  ← 缓存!                      │
  │                                                                  │
  │  做完整的 Attention → 输出第 6 个 token 的预测                   │
  │                                                                  │
  ├──────────────────────────────────────────────────────────────────┤
  │  Decode 阶段 (逐 token 生成, 串行, Memory-bound):                │
  │                                                                  │
  │  Step 1: 只计算新 token 的 Q6                                   │
  │    Q6 × [K1,K2,K3,K4,K5]^T → attention scores                  │
  │    scores × [V1,V2,V3,V4,V5] → 输出 → t6                       │
  │    追加: K_cache = [..., K6], V_cache = [..., V6]               │
  │                                                                  │
  │  Step 2: 只计算 Q7                                              │
  │    Q7 × [K1,...,K6]^T → scores → × [V1,...,V6] → t7             │
  │    追加: K_cache = [..., K7], V_cache = [..., V7]               │
  │                                                                  │
  │  → 每步只需 1 个新 Q，和缓存中所有的 K, V 做 Attention          │
  │  → 避免了对历史 token 的重复计算                                 │
  └──────────────────────────────────────────────────────────────────┘
```

## KV Cache 显存占用

### 计算公式

```
  KV Cache 大小 = 2 × batch × seq × layers × heads × head_dim × dtype

  LLaMA-7B (32 layers, 32 heads, head_dim=128, FP16):

  batch=1, seq=4096:
    = 2 × 1 × 4096 × 32 × 32 × 128 × 2 bytes
    = 2 GB

  batch=32, seq=4096:
    = 2 × 32 × 4096 × 32 × 32 × 128 × 2 bytes
    = 64 GB  ← 比模型本身 (14GB) 还大!

  ┌──────────────────────────────────────────────────────────────────┐
  │  LLaMA-7B 推理显存分布:                                          │
  │                                                                  │
  │  batch=1:                     batch=32:                          │
  │  ┌────────────────────┐      ┌────────────────────┐             │
  │  │ 模型: 14 GB (82%) │      │ 模型:  14 GB (18%) │             │
  │  │ KV:    2 GB (12%) │      │ KV:   64 GB (80%) │             │
  │  │ 其他:  1 GB (6%)  │      │ 其他:  2 GB (2%)  │             │
  │  │ 总计: 17 GB       │      │ 总计: 80 GB       │             │
  │  └────────────────────┘      └────────────────────┘             │
  │                                                                  │
  │  → 高并发场景下，KV Cache 才是显存杀手!                          │
  │  → 这就是 PagedAttention 和 GQA 存在的原因                      │
  └──────────────────────────────────────────────────────────────────┘
```

### 为什么 KV Cache 是推理显存管理的核心

```
  问题 1: KV Cache 大小不可预测
    用户 A: "Hi" → seq=2, KV ~1MB
    用户 B: 贴了一篇论文 → seq=4000, KV ~2GB
    → 无法预分配固定显存

  问题 2: KV Cache 持续增长
    每生成一个 token，KV Cache 就增大一行
    如果预分配最大长度 → 大量浪费
    如果动态分配 → 显存碎片

  问题 3: 高并发下 KV Cache 挤压显存
    32 路并发 × 2GB = 64GB KV Cache
    → 80GB A100 只剩 16GB 给模型

  → 这就是 PagedAttention (见 06-batching) 要解决的问题
  → 也是 GQA/MQA (见 07-attention) 要减少的东西
```

```python
def kv_cache_memory(
    batch_size: int,
    seq_length: int,
    num_layers: int = 32,      # LLaMA-7B
    num_kv_heads: int = 32,    # MHA=32, GQA 可能=8
    head_dim: int = 128,
    dtype_bytes: int = 2       # FP16
) -> float:
    """计算 KV Cache 显存 (GB)"""
    kv_cache_bytes = (
        2 *             # K 和 V
        batch_size *
        seq_length *
        num_layers *
        num_kv_heads *
        head_dim *
        dtype_bytes
    )
    return kv_cache_bytes / 1e9

# LLaMA-7B (MHA, 32 KV heads)
print(f"bs=1,  seq=4096:  {kv_cache_memory(1, 4096):.1f} GB")
print(f"bs=32, seq=4096:  {kv_cache_memory(32, 4096):.1f} GB")

# LLaMA-2 70B (GQA, 8 KV groups)
print(f"bs=1,  seq=4096 (GQA-8): {kv_cache_memory(1, 4096, 80, 8, 128):.1f} GB")
# GQA 把 64 head → 8 group → KV Cache 减少 8 倍!
```

---

*下一篇：[06-llm-inference-batching.md](06-llm-inference-batching.md) - Batching 优化*

---

## 参考资料与引用

1. **Kwon, W., et al. (2023).** *Efficient Memory Management for Large Language Model Serving with PagedAttention.* SOSP 2023. — PagedAttention / vLLM  
   https://arxiv.org/abs/2309.06180

2. **Pope, R., et al. (2023).** *Efficiently Scaling Transformer Inference.* MLSys 2023. — KV Cache 显存分析  
   https://arxiv.org/abs/2211.05102

3. **Shazeer, N. (2019).** *Fast Transformer Decoding: One Write-Head is All You Need.* — Multi-Query Attention 减少 KV Cache  
   https://arxiv.org/abs/1911.02150

4. **Ainslie, J., et al. (2023).** *GQA: Training Generalized Multi-Query Transformer Models.* — Grouped-Query Attention  
   https://arxiv.org/abs/2305.13245
