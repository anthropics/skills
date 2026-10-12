# Chunked Prefill

> 一个 128K 的 Prefill 请求独占 GPU 30 秒——其他用户全部排队等候。分块 Prefill 让每个人都能"插队"。

## 目录

- [问题：长 Prompt 阻塞推理](#问题长-prompt-阻塞推理)
- [Chunked Prefill 原理](#chunked-prefill-原理)
- [调度策略详解](#调度策略详解)
- [性能影响分析](#性能影响分析)
- [框架实现与配置](#框架实现与配置)
- [最佳实践](#最佳实践)

---

## 问题：长 Prompt 阻塞推理

### 传统 Prefill 的"霸道"行为

在传统的 LLM 推理引擎中，Prefill 和 Decode 共享 GPU——而 Prefill 是"计算密集型"操作，一旦开始就会独占 GPU 资源：

```
传统调度（无 Chunked Prefill）：

时间轴 ─────────────────────────────────────────────────────→

GPU:  [======= 128K Prompt Prefill (30s) =======][D][D][D][D]...
       ↑                                          ↑
       请求 A 开始 Prefill                         请求 A 开始 Decode

请求 B (100 tokens):  [等待... 等待... 等待...]→[P][D][D]...
请求 C (50 tokens):   [等待... 等待... 等待... 等待...]→[P][D]...
请求 D (200 tokens):  [等待... 等待... 等待... 等待... 等待]→...

问题：
  ✗ 请求 A 的 128K Prefill 独占 GPU 30 秒
  ✗ 请求 B/C/D 即使只有几十个 token，也必须等 30 秒
  ✗ P99 延迟被最长的 Prefill 请求主导
  ✗ 用户体验：所有人都感觉系统"卡住了"
```

### 类比：餐厅的大桌问题

```
想象一个只有一个厨师的餐厅：

传统方式：
  桌 A 点了 20 道菜 → 厨师做完所有 20 道才接下一桌
  桌 B 只点了 1 碗面 → 等 2 小时
  桌 C 只点了 1 杯饮料 → 等 2 小时
  
  所有人都在等一桌大单

Chunked Prefill 方式：
  桌 A 的菜分批做：先做 2 道 → 给 B 做面 → 再做 A 的 2 道 → 给 C 做饮料 → ...
  
  桌 B 等 5 分钟就拿到面
  桌 C 等 3 分钟就拿到饮料
  桌 A 总时间稍长，但不影响其他人
```

---

## Chunked Prefill 原理

### 核心思路：把大 Prefill 拆成小块

```
Chunked Prefill 工作流程：

Step 1: 将长 Prompt 分成固定大小的 Chunk
  
  128K Prompt → [Chunk 1: 2K] [Chunk 2: 2K] ... [Chunk 64: 2K]
                 每个 Chunk = max_num_batched_tokens

Step 2: 每个调度周期，混合执行 Prefill Chunk + Decode Token

  周期 1: [Chunk 1 of A (2K tokens)] + [Decode B (1 token)] + [Decode C (1 token)]
  周期 2: [Chunk 2 of A (2K tokens)] + [Decode B (1 token)] + [Decode C (1 token)]
  周期 3: [Chunk 3 of A (2K tokens)] + [Decode B (1 token)] + [Decode C (1 token)]
  ...
  周期 64: [Chunk 64 of A] + [Decode B] + [Decode C]
  周期 65: [Decode A (1 token)] + [Decode B] + [Decode C]  ← A 开始 Decode

图示：
时间轴 ────────────────────────────────────────────────────→

GPU:  [C1+D][C2+D][C3+D]...[C64+D][D+D+D][D+D+D]...
       ↑                     ↑      ↑
       A 的 Chunk 1          A 完成   A/B/C 混合 Decode
       B/C 同时 Decode      Prefill

请求 B:  [P][D][D][D][D][D][D]...  ← 几乎不受影响！
请求 C:    [P][D][D][D][D][D]...   ← 几乎不受影响！
请求 A:  [C1][C2]...[C64]→[D][D]  ← Prefill 分散在多个周期
```

### 关键参数：Chunk Size

```
max_num_batched_tokens = 单个调度周期最多处理的 token 数

Chunk Size 的权衡：
  
  小 Chunk (如 512):
  ✅ 公平性极好 — 短请求几乎零等待
  ✅ P99 延迟最低
  ❌ Prefill 吞吐量下降 — GPU 矩阵乘法效率低（batch 太小）
  ❌ 调度开销增加
  
  大 Chunk (如 8192):
  ✅ Prefill 吞吐量高 — GPU 计算效率好
  ✅ 调度开销低
  ❌ 其他请求等待时间增加
  ❌ P99 延迟更高
  
  ┌─────────────────────────────────────────┐
  │     Chunk Size vs 延迟/吞吐量权衡        │
  │                                          │
  │  P99延迟  ████                           │
  │  (ms)    ████                            │
  │          ████  ▓▓▓▓                      │
  │          ████  ▓▓▓▓  ░░░░  ░░░░         │
  │          ████  ▓▓▓▓  ░░░░  ░░░░  ░░░░   │
  │          ────┬──────┬──────┬──────┬───── │
  │             512   1024   2048   4096     │
  │                                          │
  │  吞吐量   ░░░░  ░░░░  ▓▓▓▓  ████  ████  │
  │                                          │
  │  推荐：2048 tokens（延迟/吞吐量最佳平衡） │
  └─────────────────────────────────────────┘
```

---

## 调度策略详解

### Sarathi-Serve 的调度方案

Sarathi-Serve（论文：Sarathi-Serve: Chunked-Prefills for SLO-compliant LLM Serving）提出了系统化的 Chunked Prefill 调度策略：

```
Sarathi-Serve 的核心设计：

1. Stall-Free Batching（无阻塞批处理）
   ┌──────────────────────────────────────────────────┐
   │ 每个调度周期构建一个"混合 Batch"：                  │
   │                                                    │
   │ Batch = [Prefill Chunk(s)] + [Decode Token(s)]    │
   │                                                    │
   │ 约束：总 token 数 ≤ max_num_batched_tokens         │
   │                                                    │
   │ 示例 (max=2048):                                   │
   │ Batch 1: [A_chunk1: 1024 tokens] + [B_decode: 1]  │
   │          + [C_decode: 1] + ... (共 ~1026 tokens)   │
   │                                                    │
   │ 如果还有空间：                                      │
   │ Batch 2: [A_chunk2: 1024] + [D_prefill: 512]      │
   │          + [B_decode: 1] + [C_decode: 1]           │
   │          (混合多个请求的 Prefill + Decode)           │
   └──────────────────────────────────────────────────┘

2. 优先级调度
   优先级：Decode > Prefill Chunk
   
   原因：
   - Decode 请求已经在"进行中"（用户在等待流式输出）
   - Prefill Chunk 是"准备中"（用户还没看到任何输出）
   - 先保证正在 Decode 的请求不卡顿，再处理新的 Prefill

3. SLO-aware 调度
   根据每个请求的 SLO (Service Level Objective) 动态调整：
   - 低延迟 SLO：小 Chunk Size (512)
   - 高吞吐 SLO：大 Chunk Size (4096)
```

### 与 Continuous Batching 的关系

```
调度策略演进：

1. Static Batching（原始）
   → 等一批请求凑齐再一起处理
   → 最长的请求决定整个 batch 的延迟

2. Continuous Batching（vLLM 默认）
   → 请求随到随处理，完成后立即被新请求替换
   → 但 Prefill 仍然是"原子操作"——一个大 Prefill 阻塞一整个周期

3. Chunked Prefill（进阶）
   → 在 Continuous Batching 基础上，允许 Prefill 被拆分
   → Prefill Chunk 和 Decode Token 混合在同一个 Batch 中
   → 最精细的调度粒度

  Static → Continuous → Chunked Prefill
  (粗)      (中等)       (精细)
```

---

## 性能影响分析

### TTFT 影响

```
Chunked Prefill 对 TTFT 的影响：

场景：128K prompt，Chunk Size = 2048

无 Chunked Prefill:
  TTFT = Prefill(128K tokens) = ~1800ms
  → 快，因为一次性计算完

有 Chunked Prefill:
  TTFT = 64 chunks × (chunk_compute + scheduling_overhead)
       ≈ 64 × (30ms + 1ms) ≈ 1984ms
  → 稍慢 (~10%)，因为有调度开销和 Decode 交错

但是！对其他请求的 TTFT 影响：

无 Chunked Prefill:
  请求 B 的 TTFT = 等待 A 完成 + 自己的 Prefill
                 = 1800ms + 50ms = 1850ms  ← 被阻塞

有 Chunked Prefill:
  请求 B 的 TTFT = 等待 1 个 Chunk + 自己的 Prefill
                 ≈ 30ms + 50ms = 80ms  ← 几乎不受影响！

总结：
  长请求自身 TTFT: 略增 (~10%)
  短请求 TTFT:     大幅降低 (90%+)
  P99 TTFT:        大幅降低 (因为短请求不再被阻塞)
```

### 吞吐量影响

```
吞吐量对比：

场景：混合负载（10% 长请求 128K + 90% 短请求 2K）

无 Chunked Prefill:
  吞吐量受限于长 Prefill 的阻塞效应
  实际吞吐: ~800 tokens/s

有 Chunked Prefill:
  GPU 持续忙碌（Prefill + Decode 混合）
  实际吞吐: ~1200 tokens/s (+50%)

原因：
  1. 长 Prefill 期间，Decode 请求也在产出 → 总输出 token 增加
  2. GPU 不会出现"只有 1 个请求在 Prefill，其他全空闲"的浪费
  3. 矩阵乘法批量更大（混合 batch）→ 计算效率更高
```

---

## 框架实现与配置

### vLLM 配置

```python
# vLLM 启用 Chunked Prefill
from vllm import LLM, SamplingParams

llm = LLM(
    model="meta-llama/Llama-3.1-8B-Instruct",
    
    # Chunked Prefill 核心配置
    enable_chunked_prefill=True,        # 启用分块 Prefill
    max_num_batched_tokens=2048,        # 每个调度周期最多处理 token 数
    
    # 相关配置
    max_num_seqs=256,                   # 最大并发请求数
    gpu_memory_utilization=0.9,         # GPU 显存利用率
    
    # 可选：同时启用 Prefix Caching
    enable_prefix_caching=True,         # Chunked Prefill + Prefix Caching 可以组合
)

# vLLM 服务器模式
# vllm serve meta-llama/Llama-3.1-8B-Instruct \
#     --enable-chunked-prefill \
#     --max-num-batched-tokens 2048 \
#     --enable-prefix-caching
```

### max_num_batched_tokens 调优指南

```
max_num_batched_tokens 选择：

┌──────────┬────────────────────────────────────────────┐
│ 值        │ 适用场景                                    │
├──────────┼────────────────────────────────────────────┤
│ 512      │ 极低延迟要求（交互式聊天）                    │
│          │ → P99 最低，但吞吐量损失 ~20%                │
├──────────┼────────────────────────────────────────────┤
│ 1024     │ 延迟敏感场景（在线服务）                      │
│          │ → 延迟/吞吐量平衡点                          │
├──────────┼────────────────────────────────────────────┤
│ 2048     │ ★ 推荐默认值                                │
│          │ → 多数场景的最优平衡                          │
├──────────┼────────────────────────────────────────────┤
│ 4096     │ 吞吐量优先（批处理、离线推理）                │
│          │ → 吞吐量最高，但短请求延迟增加                │
├──────────┼────────────────────────────────────────────┤
│ 8192+    │ 纯离线场景                                   │
│          │ → 几乎等于不分块                              │
└──────────┴────────────────────────────────────────────┘

调优方法：
1. 先用默认值 2048 跑基准
2. 观察 P99 TTFT 和吞吐量
3. 如果 P99 TTFT > SLO → 减小值
4. 如果吞吐量不足 → 增大值
5. 如果有长请求 (>32K) → 建议 ≤ 2048
```

### SGLang 配置

```python
# SGLang 默认支持 Chunked Prefill
import sglang as sgl

runtime = sgl.Runtime(
    model_path="meta-llama/Llama-3.1-8B-Instruct",
    chunked_prefill_size=2048,   # Chunk 大小
    tp_size=1,
)
```

---

## 最佳实践

### 什么时候开启 Chunked Prefill

```
决策矩阵：

┌──────────────────────┬───────────┬─────────────────────────┐
│ 场景                  │ 建议      │ 原因                     │
├──────────────────────┼───────────┼─────────────────────────┤
│ 在线服务 + 混合负载   │ ✅ 强烈推荐│ 长请求不会阻塞短请求      │
│ 在线服务 + 短请求为主 │ ⚠️ 可选   │ 收益不大（没有长 Prefill） │
│ 离线批处理            │ ❌ 不推荐  │ 吞吐量略有下降            │
│ 长上下文服务 (128K+)  │ ✅ 强烈推荐│ 必须，否则 P99 爆炸       │
│ 实时对话              │ ✅ 推荐    │ 保证响应速度稳定          │
└──────────────────────┴───────────┴─────────────────────────┘
```

### Chunked Prefill + 其他优化的组合

```
推荐组合方案：

基础方案（适用于大多数在线服务）：
  Chunked Prefill + Continuous Batching + Prefix Caching
  → vLLM 一行配置搞定

进阶方案（高性能在线服务）：
  Chunked Prefill + FP8 KV Cache + Prefix Caching + 适当的 Chunk Size
  → 延迟低 + 吞吐高 + 显存省

极致方案（超大规模服务）：
  Chunked Prefill + PD 分离 + Prefix Caching + FP8 KV Cache
  → Prefill 节点专门做分块 Prefill
  → Decode 节点专门做高并发 Decode
  → 见 06-disaggregated-serving.md
```

---

## 总结

```
┌─────────────────────────────────────────────────────────────┐
│              Chunked Prefill - 关键要点                       │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. 解决什么：长 Prompt Prefill 独占 GPU 阻塞其他请求        │
│                                                              │
│  2. 原理：把大 Prefill 拆成小 Chunk，与 Decode 交错执行      │
│                                                              │
│  3. 核心参数：max_num_batched_tokens                         │
│     推荐默认值 2048，根据 SLO 调优                           │
│                                                              │
│  4. 效果：                                                   │
│     短请求 TTFT 降低 90%+                                    │
│     长请求 TTFT 增加 ~10%                                    │
│     总吞吐量提升 ~50% (混合负载)                              │
│                                                              │
│  5. 在线服务 + 混合负载场景：强烈推荐开启                     │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

*上一篇：[04-long-context-inference.md](04-long-context-inference.md) — 长上下文推理*

*下一篇：[06-disaggregated-serving.md](06-disaggregated-serving.md) — Prefill/Decode 分离架构*

*返回目录：[README.md](README.md)*

---

## 参考资料与引用

1. **Agrawal, A., et al. (2024).** *Sarathi: Efficient LLM Inference by Piggybacking Decodes with Chunked Prefills.*  
   https://arxiv.org/abs/2308.16369

2. **Agrawal, A., et al. (2024).** *Taming Throughput-Latency Tradeoff in LLM Inference with Sarathi-Serve.*  
   https://arxiv.org/abs/2403.02310
