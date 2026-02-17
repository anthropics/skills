# LLM 推理特性 - KV Cache

> 理解 KV Cache 的原理和显存占用。

## 自回归生成的挑战

### 重复计算问题

```
生成 "The capital of France is Paris"

Step 1: Q="The" → K,V 计算 → "capital"
Step 2: Q="The capital" → K,V 重新计算 → "of"
Step 3: Q="The capital of" → K,V 重新计算 → "France"
...

问题: 每步都要重新计算前面所有 token 的 K,V
解决: 缓存已计算的 K,V
```

## KV Cache 原理

### 工作机制

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        KV Cache 工作原理                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Prefill 阶段 (处理 prompt):                                           │
│   Input: [t1, t2, t3, t4, t5]                                          │
│   计算并缓存: K_cache = [K1, K2, K3, K4, K5]                            │
│              V_cache = [V1, V2, V3, V4, V5]                            │
│                                                                         │
│   Decode 阶段 (生成新 token):                                           │
│   Step 1: 只计算新 token 的 Q6                                          │
│           从 cache 读取 K_cache, V_cache                                │
│           Attention(Q6, K_cache, V_cache) → t6                         │
│           追加: K_cache = [..., K6], V_cache = [..., V6]               │
│                                                                         │
│   Step 2: 只计算 Q7                                                     │
│           Attention(Q7, K_cache, V_cache) → t7                         │
│           追加: K_cache = [..., K7], V_cache = [..., V7]               │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## KV Cache 显存占用

### 计算公式

```python
def kv_cache_memory(
    batch_size: int,
    seq_length: int,
    num_layers: int,
    num_heads: int,
    head_dim: int,
    dtype_bytes: int = 2  # FP16
) -> float:
    """
    KV Cache 显存 = 2 × batch × seq × layers × heads × head_dim × dtype
    """
    kv_cache_bytes = (
        2 *  # K 和 V
        batch_size *
        seq_length *
        num_layers *
        num_heads *
        head_dim *
        dtype_bytes
    )
    return kv_cache_bytes / 1e9  # GB

# LLaMA-7B: 32 layers, 32 heads, 128 head_dim
print(f"KV Cache (bs=1, seq=4096): {kv_cache_memory(1, 4096, 32, 32, 128):.1f} GB")
# 输出: ~2 GB
```

### 显存分配

```
LLaMA-7B 推理显存分布:
├── 模型权重: ~14 GB (FP16)
├── KV Cache: ~2 GB (seq=4096)
└── 其他: ~1 GB
总计: ~17 GB
```

---

*下一篇：[06-llm-inference-batching.md](06-llm-inference-batching.md) - Batching 优化*
