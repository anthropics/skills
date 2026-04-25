# LLM 推理特性 - Batching

> Static Batching 到 Continuous Batching 的演进 — 以及 PagedAttention 如何改变一切。

## 为什么 Batching 对 LLM 推理至关重要

```
  LLM Decode 是 Memory-bound (瓶颈在读权重，不在算)
  → batch=1 时，读完 14GB 权重只算了 1 个 token → GPU 空转 99%
  → batch=32 时，读完 14GB 权重算了 32 个 token → 利用率提升 32 倍!

  类比: 公交车
    batch=1 = 出租车专送 1 人 (昂贵)
    batch=32 = 公交车送 32 人 (经济)
    → 但公交车需要等人凑齐 (延迟) vs 随到随走 (这就是 Continuous Batching 要解决的)
```

## Static Batching — 最朴素的方式

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  Static Batching: 凑齐一批 → 统一处理 → 全部完成才释放           │
  │                                                                  │
  │  请求:                                                           │
  │    Req1: "写一首诗" → 需要生成 200 token                         │
  │    Req2: "1+1=?"   → 需要生成 3 token                           │
  │    Req3: "翻译一段话" → 需要生成 50 token                       │
  │                                                                  │
  │  处理过程:                                                       │
  │  Step 1-3:   [Req1, Req2, Req3]  全部在跑                       │
  │  Step 4:     [Req1, pad, Req3]   Req2 完成了，但位置空着!        │
  │  Step 5-50:  [Req1, pad, Req3]   Req2 的位置持续浪费             │
  │  Step 51:    [Req1, pad, pad]    Req3 完成，还在等               │
  │  Step 52-200:[Req1, pad, pad]    只有 Req1 在跑，2/3 算力浪费!  │
  │                                                                  │
  │  问题:                                                           │
  │  1. Req2 3 步就完成了，但 Req1 的 200 步都没结束，Req2 无法返回  │
  │  2. Req2/Req3 完成后 GPU 白白空转                                │
  │  3. 新来的 Req4, Req5 必须等这一整批结束                         │
  │                                                                  │
  │  类比: 旅游大巴                                                  │
  │    所有人必须等最后一个人拍完照才能走                             │
  │    → 有人 5 分钟就拍完了，有人要拍 1 小时                        │
  └──────────────────────────────────────────────────────────────────┘
```

## Continuous Batching — 请求完成立即让位

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  Continuous Batching (也叫 In-flight Batching):                   │
  │  某个请求完成 → 立即移除 → 新请求立即填入                        │
  │                                                                  │
  │  Time →                                                          │
  │  Step 1:   [Req1, Req2, Req3]    三个请求并行处理                │
  │  Step 3:   [Req1, ────, Req3]    Req2 完成! → 立即返回给用户    │
  │  Step 4:   [Req1, Req4, Req3]    Req4 立即加入 (不用等整批)     │
  │  Step 50:  [Req1, Req4, ────]    Req3 完成 → 立即返回           │
  │  Step 51:  [Req1, Req4, Req5]    Req5 加入                      │
  │  ...                                                             │
  │                                                                  │
  │  优势:                                                           │
  │  1. 短请求快速返回 (不用等长请求)                                │
  │  2. GPU 始终满载 (空位立即被填充)                                │
  │  3. 吞吐量提升 2-5x (vs Static Batching)                        │
  │                                                                  │
  │  类比: 理发店                                                    │
  │    Static = 理发师等所有顾客都理完才接下一批                     │
  │    Continuous = 一个顾客理完走了，下一个立马坐下                  │
  │    → 理发师永远不闲着!                                           │
  └──────────────────────────────────────────────────────────────────┘
```

### Continuous Batching 的实现挑战

```
  挑战 1: 每个请求的序列长度不同
    Req1 已经生成了 100 token, KV Cache 很大
    Req4 刚开始, KV Cache 为空
    → 不能用简单的矩阵拼 batch (不对齐!)

  挑战 2: Prefill 和 Decode 混合
    新加入的 Req4 需要做 Prefill (处理 prompt, Compute-bound)
    正在进行的 Req1 在做 Decode (逐 token, Memory-bound)
    → 两种计算特征完全不同，如何混合调度？

  挑战 3: KV Cache 动态管理
    请求完成后要释放 KV Cache
    新请求进来要分配 KV Cache
    → 显存碎片化严重

  → 这些挑战催生了 PagedAttention!
```

## PagedAttention — 借鉴操作系统的智慧

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  核心思想: 像操作系统管理内存一样管理 KV Cache                    │
  │                                                                  │
  │  类比: 图书馆书架                                                │
  │                                                                  │
  │  传统方式: 给每本书预留一整排书架                                 │
  │    "这本可能写到 500 页" → 预留 500 格                           │
  │    实际只写了 50 页 → 450 格浪费!                                │
  │    → 这就是传统 KV Cache 的显存浪费                              │
  │                                                                  │
  │  PagedAttention: 按需分配"页"                                    │
  │    每"页" = 16 个 token 的 KV Cache                              │
  │    写了 50 个 token → 分配 4 页                                  │
  │    写到 51 个 → 再加 1 页                                        │
  │    页不需要连续! (通过 Block Table 记录位置)                      │
  │                                                                  │
  ├──────────────────────────────────────────────────────────────────┤
  │                                                                  │
  │  物理显存 (分成固定大小的 Block):                                 │
  │  ┌────┬────┬────┬────┬────┬────┬────┬────┐                     │
  │  │ B0 │ B1 │ B2 │ B3 │ B4 │ B5 │ B6 │ B7 │                     │
  │  └────┴────┴────┴────┴────┴────┴────┴────┘                     │
  │                                                                  │
  │  Block Table (类似操作系统的页表):                                │
  │  Req1 (50 tokens): [B0, B1, B3, B5]  → 4 个 Block, 不连续!     │
  │  Req2 (20 tokens): [B2, B6]          → 2 个 Block               │
  │  Req3 (30 tokens): [B4, B7]          → 2 个 Block               │
  │  空闲: 无  → 利用率接近 100%!                                    │
  │                                                                  │
  │  Req2 完成 → 释放 B2, B6 → 新请求可以复用                       │
  │  → 显存碎片几乎为零!                                             │
  │                                                                  │
  ├──────────────────────────────────────────────────────────────────┤
  │  效果:                                                           │
  │  传统连续分配: 显存利用率 ~30-50% (大量预留浪费)                 │
  │  PagedAttention: 显存利用率 ~90%+                                │
  │  → 同样的 GPU，能服务 2-4 倍的并发请求!                          │
  │                                                                  │
  │  这就是 vLLM 论文的核心贡献，也是 vLLM 比其他框架快的关键原因   │
  └──────────────────────────────────────────────────────────────────┘
```

### 使用

```python
from vllm import LLM, SamplingParams

llm = LLM(
    model="meta-llama/Llama-2-7b-hf",
    gpu_memory_utilization=0.9,  # PagedAttention 允许更高利用率 (90%)
    max_model_len=4096,          # 最大序列长度
    # block_size=16,             # 默认每个 Block 16 token
)

# Continuous Batching 自动启用
sampling_params = SamplingParams(temperature=0.8, max_tokens=100)
outputs = llm.generate(prompts, sampling_params)
```

---

*下一篇：[07-llm-inference-attention.md](07-llm-inference-attention.md) - Attention 优化*

---

## 参考资料与引用

1. **Yu, G., et al. (2022).** *Orca: A Distributed Serving System for Transformer-Based Generative Models.* OSDI 2022. — Continuous Batching / Iteration-level Scheduling  
   https://www.usenix.org/conference/osdi22/presentation/yu

2. **Kwon, W., et al. (2023).** *Efficient Memory Management for Large Language Model Serving with PagedAttention.* — vLLM continuous batching 实现  
   https://arxiv.org/abs/2309.06180

3. **Agrawal, A., et al. (2024).** *Sarathi: Efficient LLM Inference by Piggybacking Decodes with Chunked Prefills.*  
   https://arxiv.org/abs/2308.16369
