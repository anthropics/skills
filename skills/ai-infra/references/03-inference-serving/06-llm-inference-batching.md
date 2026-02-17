# LLM 推理特性 - Batching

> 理解 Static Batching 和 Continuous Batching 的区别。

## Static vs Continuous Batching

### Static Batching

```
请求队列: [Req1(长), Req2(短), Req3(中)]

处理: 等待凑齐一批后一起处理
      所有请求按最长的对齐

问题:
- 短请求等待长请求完成
- GPU 利用率低
- 首 token 延迟高
```

### Continuous Batching

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     Continuous Batching                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Time →                                                                │
│   Step 1: [Req1, Req2, Req3]  处理中                                    │
│   Step 2: [Req1, Req2, Req3]  Req2 完成 → 移除                          │
│   Step 3: [Req1, Req4, Req3]  Req4 加入                                 │
│   Step 4: [Req1, Req4, Req5]  Req3 完成, Req5 加入                      │
│   ...                                                                   │
│                                                                         │
│   优势:                                                                  │
│   - 短请求快速返回                                                       │
│   - GPU 利用率高                                                        │
│   - 首 token 延迟低                                                     │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## PagedAttention

### 问题

```
传统 KV Cache: 连续内存分配
- 预分配最大长度
- 碎片化严重
- 显存利用率低
```

### 解决方案

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        PagedAttention                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   将 KV Cache 分成固定大小的 Block (如 16 tokens)                        │
│                                                                         │
│   物理内存:                                                              │
│   ┌────┬────┬────┬────┬────┬────┬────┬────┐                           │
│   │ B0 │ B1 │ B2 │ B3 │ B4 │ B5 │ B6 │ B7 │                           │
│   └────┴────┴────┴────┴────┴────┴────┴────┘                           │
│                                                                         │
│   Req1 (seq=50): Block Table → [B0, B1, B3, B5]                        │
│   Req2 (seq=20): Block Table → [B2, B6]                                │
│   Req3 (seq=30): Block Table → [B4, B7]                                │
│                                                                         │
│   优势:                                                                  │
│   - 按需分配，无预留浪费                                                  │
│   - 非连续存储，减少碎片                                                  │
│   - 显存利用率提升 2-4 倍                                                │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### vLLM 使用

```python
from vllm import LLM, SamplingParams

llm = LLM(
    model="meta-llama/Llama-2-7b-hf",
    gpu_memory_utilization=0.9,  # PagedAttention 允许更高利用率
)

sampling_params = SamplingParams(temperature=0.8, max_tokens=100)
outputs = llm.generate(prompts, sampling_params)
```

---

*下一篇：[07-llm-inference-attention.md](07-llm-inference-attention.md) - Attention 优化*
