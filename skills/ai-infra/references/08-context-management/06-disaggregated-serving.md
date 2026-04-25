# Prefill/Decode 分离架构（Disaggregated Serving）

> Prefill 像厨房备菜（计算密集），Decode 像上菜服务（带宽密集）——让专业的人做专业的事。

## 目录

- [为什么要分离 Prefill 和 Decode](#为什么要分离-prefill-和-decode)
- [PD 分离架构设计](#pd-分离架构设计)
- [KV Cache 传输：核心挑战](#kv-cache-传输核心挑战)
- [业界方案对比](#业界方案对比)
- [异构 GPU 调度](#异构-gpu-调度)
- [部署实践](#部署实践)

---

## 为什么要分离 Prefill 和 Decode

### Prefill vs Decode 的本质差异

> 📖 Prefill/Decode 两阶段基础见 [03-inference-serving/05-llm-inference-kv-cache.md](../03-inference-serving/05-llm-inference-kv-cache.md)

```
┌─────────────────────────────────────────────────────────────────┐
│              Prefill vs Decode 深度对比                           │
├──────────────────┬─────────────────────┬────────────────────────┤
│                  │      Prefill        │       Decode           │
├──────────────────┼─────────────────────┼────────────────────────┤
│ 输入             │ 全部 Input Token    │ 1 个新 Token            │
│ 计算模式         │ 大矩阵乘法          │ 向量-矩阵乘法          │
│ 瓶颈             │ Compute-bound       │ Memory-bound           │
│ GPU 利用率       │ 70-90%              │ 10-30%                 │
│ 算术强度*        │ 高 (~100 FLOPs/byte)│ 低 (~1 FLOPs/byte)    │
│ 主要消耗         │ FLOPS (算力)        │ 带宽 (HBM 读 KV Cache) │
│ 延迟特征         │ TTFT (一次性)       │ TPS (持续性)           │
│ Batch 策略       │ 大 seq_len          │ 大 batch_size           │
│ 理想硬件         │ 高 FLOPS GPU        │ 高带宽/大显存 GPU       │
├──────────────────┴─────────────────────┴────────────────────────┤
│ *算术强度 = FLOPs / Bytes (越高越适合 compute, 越低越适合 memory) │
└─────────────────────────────────────────────────────────────────┘
```

### 混合调度的低效

```
混合调度（传统方式）的问题：

GPU 资源利用率时间线：

Compute 利用率:
100% ┤████████          ░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
     │████████          ░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
 50% ┤████████          ░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
     │████████          ░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
  0% ┼────────┬─────────────────────────────────────────
     │Prefill │          Decode (每步生成 1 token)
     
带宽利用率:
100% ┤░░░░░░░░          ████████████████████████████████
     │░░░░░░░░          ████████████████████████████████
 50% ┤░░░░░░░░          ████████████████████████████████
     │░░░░░░░░          ████████████████████████████████
  0% ┼────────┬─────────────────────────────────────────
     │Prefill │          Decode

问题：
  Prefill 阶段：算力用满，带宽闲置
  Decode 阶段：带宽用满，算力闲置
  → 无论哪个阶段，都有一半资源在浪费
  → GPU 的综合利用率只有 ~40-50%

分离后：
  Prefill GPU: 专注计算 → 算力利用率 80%+
  Decode GPU:  专注带宽 → 带宽利用率 80%+
  → 综合利用率提升到 70-80%
```

---

## PD 分离架构设计

### 整体架构

```
┌─────────────────────────────────────────────────────────────────┐
│                     PD 分离整体架构                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Client ──→ [Load Balancer / API Gateway]                       │
│                        │                                         │
│                  ┌─────▼──────┐                                  │
│                  │  Scheduler  │ ← 核心调度器                     │
│                  │  / Router   │   决定请求发给哪个 Pool           │
│                  └──┬──────┬──┘                                  │
│                     │      │                                     │
│          ┌──────────▼──┐  ┌▼───────────┐                        │
│          │ Prefill Pool │  │ Decode Pool │                       │
│          │              │  │             │                       │
│          │ ┌──────────┐ │  │ ┌─────────┐│                       │
│          │ │ P-Node 1 │ │  │ │ D-Node 1││                       │
│          │ │ (H100)   │ │  │ │ (L40S)  ││                       │
│          │ └──────────┘ │  │ └─────────┘│                       │
│          │ ┌──────────┐ │  │ ┌─────────┐│                       │
│          │ │ P-Node 2 │ │  │ │ D-Node 2││                       │
│          │ │ (H100)   │ │  │ │ (L40S)  ││                       │
│          │ └──────────┘ │  │ └─────────┘│                       │
│          │ ...          │  │ ...        │                       │
│          └──────┬───────┘  └──────┬─────┘                       │
│                 │                 │                               │
│                 └────────┬────────┘                               │
│                          │                                       │
│                    KV Cache 传输通道                              │
│                 (RDMA / NVLink / TCP)                             │
│                                                                  │
│  数据流：                                                        │
│  1. Client → Scheduler: 发送请求                                 │
│  2. Scheduler → P-Node: 分配 Prefill 任务                       │
│  3. P-Node 完成 Prefill: 计算 KV Cache                          │
│  4. P-Node → D-Node: 传输 KV Cache                              │
│  5. D-Node: 接收 KV Cache，开始逐 Token Decode                  │
│  6. D-Node → Client: 流式返回生成结果                            │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Scheduler 设计

```
调度策略：

1. 请求路由
   新请求 → 选择负载最低的 Prefill 节点
   
   路由策略：
   - Round Robin: 简单但不考虑负载
   - Least Queue: 选队列最短的节点
   - Prefix-Aware: 选已有对应前缀缓存的节点（结合 Prefix Caching）

2. Prefill → Decode 匹配
   P-Node 完成后 → 选择最优的 D-Node
   
   选择依据：
   - 显存空间（能容纳 KV Cache）
   - 当前 Decode 负载（避免过载）
   - 网络距离（尽量同机架/同 Switch）

3. 弹性伸缩
   监控指标 → 动态调整 P/D 节点比例
   
   Prefill 队列长 → 扩 P-Node
   Decode 延迟高 → 扩 D-Node
   低峰期 → 缩减节点
```

---

## KV Cache 传输：核心挑战

### 传输数据量计算

```
KV Cache 传输数据量：

公式: KV_size = 2 × layers × kv_heads × head_dim × dtype_bytes × seq_len

LLaMA-3.1 8B (32 layers, 8 KV heads, head_dim=128, FP16):
  per_token = 2 × 32 × 8 × 128 × 2 = 131,072 bytes = 128 KB/token
  
  ┌──────────┬──────────┬───────────────┬────────────────┐
  │ seq_len  │ KV 大小  │ 传输 @100Gbps │ 传输 @200Gbps  │
  ├──────────┼──────────┼───────────────┼────────────────┤
  │ 2K       │ 256 MB   │ 20 ms         │ 10 ms          │
  │ 4K       │ 512 MB   │ 41 ms         │ 20 ms          │
  │ 32K      │ 4 GB     │ 328 ms        │ 164 ms         │
  │ 128K     │ 16 GB    │ 1,310 ms      │ 655 ms         │
  └──────────┴──────────┴───────────────┴────────────────┘

LLaMA-3.1 70B (80 layers, 8 KV heads, head_dim=128, FP16):
  per_token = 2 × 80 × 8 × 128 × 2 = 327,680 bytes = 320 KB/token
  
  ┌──────────┬──────────┬───────────────┬────────────────┐
  │ seq_len  │ KV 大小  │ 传输 @100Gbps │ 传输 @200Gbps  │
  ├──────────┼──────────┼───────────────┼────────────────┤
  │ 2K       │ 640 MB   │ 52 ms         │ 26 ms          │
  │ 4K       │ 1.28 GB  │ 105 ms        │ 52 ms          │
  │ 32K      │ 10 GB    │ 819 ms        │ 410 ms         │
  │ 128K     │ 40 GB    │ 3,277 ms      │ 1,638 ms       │
  └──────────┴──────────┴───────────────┴────────────────┘

关键约束：
  KV Cache 传输时间 < Prefill 计算时间 → 传输不是瓶颈
  KV Cache 传输时间 > Prefill 计算时间 → 传输成为瓶颈（需要更快的网络）
  
  一般规律：
  短序列 (≤4K): 传输 < Prefill → OK
  长序列 (≥32K): 传输可能 > Prefill → 需要高带宽网络
```

### 传输协议对比

| 协议 | 带宽 | 延迟 | 适用场景 | 硬件需求 |
|------|------|------|---------|---------|
| TCP/IP | 25-100 Gbps | ~100μs | 跨机架 | 标准网卡 |
| RDMA (RoCE v2) | 100-400 Gbps | ~5μs | 同机架 | RDMA 网卡 |
| RDMA (InfiniBand) | 200-400 Gbps | ~1μs | 高性能集群 | IB 交换机 |
| NVLink (同机) | 600-900 GB/s | ~ns | 同机多卡 | NVLink Bridge |
| NIXL (NVIDIA) | 专有优化 | 极低 | TensorRT-LLM | NVIDIA 生态 |

```
传输优化策略：

1. 流水线传输（Pipeline Transfer）
   不等 Prefill 全部完成再传输
   → 每完成一层的 KV Cache，立即开始传输该层
   → Prefill 计算和 KV 传输重叠

   Prefill: [Layer 1] [Layer 2] [Layer 3] ... [Layer N]
   Transfer:          [L1 send] [L2 send] [L3 send] ...
   Decode:                                           [Start!]
   
   → 总延迟 ≈ max(Prefill, Transfer) 而非 Prefill + Transfer

2. KV Cache 压缩传输
   传输前将 KV Cache 量化 (FP16 → FP8)
   → 传输量减半
   → 接收端解压（额外计算但很小）

3. 异步预取（Async Prefetch）
   根据请求队列预测即将需要的 KV Cache
   → 提前开始传输，减少等待时间
```

---

## 业界方案对比

### DistServe (学术)

```
DistServe 的核心设计：

1. Prefill-Decode 分离 + 独立资源池
2. 基于 SLO 的调度
   → 每个请求有 TTFT SLO 和 TPS SLO
   → Scheduler 确保两个 SLO 都满足

3. Goodput 优化
   Goodput = 满足 SLO 的请求比例
   → 传统混合方式：Goodput ~60-70%
   → DistServe：Goodput ~90-95%

4. KV Cache 传输
   使用 RDMA 在 P/D 节点间传输
   流水线方式（边算边传）
```

### Splitwise (Microsoft)

```
Splitwise 的特色：

1. 异构 GPU 支持
   Prefill: 用高算力 GPU (如 A100 80GB)
   Decode:  用高性价比 GPU (如 A10, L40S)
   → 成本降低 20-40%

2. 智能分配策略
   根据请求的 input/output 比例动态分配：
   - 长输入短输出：Prefill 密集 → 分配更多 P 节点
   - 短输入长输出：Decode 密集 → 分配更多 D 节点

3. 混合模式
   允许同一 GPU 在低负载时同时做 P 和 D
   高负载时自动切换到纯 P 或纯 D 模式
```

### Mooncake (月之暗面)

```
Mooncake 的创新：KVCache-centric 架构

传统 PD 分离：
  P-Node ─── KV Cache 直传 ───→ D-Node
  问题：P 和 D 紧耦合，传输路径固定

Mooncake 的分离式存储：
  ┌─────────────────────────────────────────┐
  │                                          │
  │  P-Node₁ ──→ ┌──────────────┐ ←── D-Node₁
  │  P-Node₂ ──→ │ KV Cache Pool │ ←── D-Node₂
  │  P-Node₃ ──→ │ (分布式存储)  │ ←── D-Node₃
  │               └──────────────┘           │
  │                                          │
  │  KV Cache Pool 特点：                    │
  │  - 独立于计算节点的共享存储              │
  │  - 支持多个 D-Node 读取同一份 KV Cache   │
  │  - 支持 KV Cache 的持久化和复用          │
  │  - 使用 CXL/RDMA 高速访问               │
  └─────────────────────────────────────────┘

优势：
  1. P/D 完全解耦 → 独立扩缩容
  2. KV Cache 共享 → 一次 Prefill 多次 Decode（如 Best-of-N）
  3. 故障恢复 → KV Cache 不随 P-Node 故障丢失
  4. 调度灵活 → 任意 P-Node 的结果可以发给任意 D-Node

实际效果（据论文）：
  vs 混合部署：吞吐量提升 525%
  vs 简单 PD 分离：吞吐量提升 30%
```

### 方案对比总结

| 维度 | DistServe | Splitwise | Mooncake | vLLM PD |
|------|----------|-----------|----------|---------|
| P/D 耦合 | 直连 | 直连 | 分离存储 | 直连 |
| 异构 GPU | ❌ | ✅ | ✅ | ⚠️ 有限 |
| KV 传输 | RDMA | RDMA | Pool 读取 | TCP/RDMA |
| 共享 KV | ❌ | ❌ | ✅ | ❌ |
| 开源 | 论文 | 论文 | 论文 | ✅ |
| 生产验证 | 学术 | 微软内部 | 月之暗面 | 社区 |
| 成熟度 | ★★☆ | ★★☆ | ★★★ | ★★★ |

---

## 异构 GPU 调度

### 为什么要异构

```
成本分析：Prefill 和 Decode 对硬件的需求不同

Prefill 需要：高 FLOPS
  H100 (80GB, 989 TFLOPS FP16): ~$30/h (云)
  适合 Prefill（高计算利用率）

Decode 需要：大显存 + 高带宽
  L40S (48GB, 362 TFLOPS FP16): ~$8/h (云)
  适合 Decode（大显存放 KV Cache）

  同构方案（全 H100）：
    8 × H100 = $240/h

  异构方案（4P + 8D）：
    4 × H100 (Prefill) + 8 × L40S (Decode)
    = 4 × $30 + 8 × $8 = $184/h  → 节省 23%

  而且 Decode 节点的 48GB 显存可以容纳更多并发请求
  → 等效吞吐量更高 → 单位成本更低
```

### 异构调度策略

```
P/D 节点比例确定：

核心公式：
  P_count / D_count = avg_prefill_time / avg_decode_time

示例：
  平均 Prefill 时间 = 200ms (2K tokens)
  平均 Decode 时间 = 5000ms (生成 250 tokens × 20ms/token)
  
  P:D = 200:5000 = 1:25
  → 每 1 个 P 节点配 25 个 D 节点

  但考虑突发流量和排队：
  → 实际建议 P:D = 1:10 ~ 1:20

  动态调整：
  if prefill_queue_length > threshold:
      scale_up_prefill_nodes()
  if decode_latency > slo:
      scale_up_decode_nodes()
```

---

## 部署实践

### vLLM PD 分离部署

```bash
# vLLM 0.8+ 支持 PD 分离（实验性）

# 启动 Prefill Worker
vllm serve meta-llama/Llama-3.1-8B-Instruct \
    --worker-type prefill \
    --host 0.0.0.0 --port 8100

# 启动 Decode Worker
vllm serve meta-llama/Llama-3.1-8B-Instruct \
    --worker-type decode \
    --host 0.0.0.0 --port 8200

# 启动 Router（调度器）
vllm-router \
    --prefill-workers http://prefill-node:8100 \
    --decode-workers http://decode-node:8200 \
    --host 0.0.0.0 --port 8000
```

### 监控指标

```
PD 分离的关键监控指标：

Prefill 节点：
  - prefill_queue_length:     Prefill 排队长度
  - prefill_compute_util:     GPU 计算利用率（目标 >80%）
  - prefill_latency_p99:      Prefill P99 延迟
  - kv_transfer_time:         KV Cache 传输时间

Decode 节点：
  - decode_batch_size:        当前 Decode batch 大小
  - decode_memory_util:       KV Cache 显存利用率
  - decode_tps:               Tokens per second
  - decode_latency_p99:       Decode P99 延迟

全局：
  - e2e_latency_p50/p99:      端到端延迟
  - throughput:                总吞吐量 (tokens/s)
  - slo_attainment:           SLO 达标率
  - kv_transfer_bandwidth:    KV 传输带宽利用率
```

### 适用场景判断

```
PD 分离 vs 混合部署 决策：

┌────────────────────────────┬────────┬─────────────────────┐
│ 条件                       │ 混合    │ PD 分离              │
├────────────────────────────┼────────┼─────────────────────┤
│ GPU 数量 < 8               │ ✅      │ ❌ 开销不值得        │
│ 请求量 < 100 QPS           │ ✅      │ ❌ 复杂度不值得      │
│ 纯短请求 (< 2K)           │ ✅      │ ❌ Prefill 不是瓶颈  │
│ 混合负载 (短+长)           │ ⚠️     │ ✅ 避免长 Prefill 阻塞│
│ 高并发 (>500 QPS)         │ ❌      │ ✅ 独立扩缩容         │
│ 严格 SLO (P99 < 200ms)   │ ❌      │ ✅ 更好的尾延迟控制   │
│ 有异构 GPU                 │ ❌      │ ✅ 充分利用异构资源   │
│ 长上下文 (>32K)           │ ⚠️     │ ✅ KV 传输可优化      │
└────────────────────────────┴────────┴─────────────────────┘

总结：小规模用混合，大规模/高要求用 PD 分离
```

---

## 总结

```
┌─────────────────────────────────────────────────────────────┐
│          Prefill/Decode 分离 - 关键要点                       │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. 核心动机：Prefill (Compute) 和 Decode (Memory)          │
│     的硬件需求截然不同，混合调度效率低                        │
│                                                              │
│  2. 架构：独立的 Prefill Pool + Decode Pool + Scheduler     │
│     KV Cache 通过网络传输                                    │
│                                                              │
│  3. 核心挑战：KV Cache 传输延迟                              │
│     解决方案：RDMA + 流水线传输 + 压缩 + 分离存储           │
│                                                              │
│  4. 业界方案：                                               │
│     DistServe (SLO 优化) | Splitwise (异构)                 │
│     Mooncake (KV Pool 分离) | vLLM PD (开源)                │
│                                                              │
│  5. 适用场景：高并发 + 混合负载 + 异构 GPU + 严格 SLO       │
│     小规模/简单场景不推荐（复杂度开销不值得）                 │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

*上一篇：[05-chunked-prefill.md](05-chunked-prefill.md) — Chunked Prefill*

*下一篇：[07-context-engineering.md](07-context-engineering.md) — 上下文工程与压缩*

*返回目录：[README.md](README.md)*

---

## 参考资料与引用

1. **Zhong, Y., et al. (2024).** *DistServe: Disaggregating Prefill and Decoding for Goodput-optimized Large Language Model Serving.* OSDI 2024.  
   https://arxiv.org/abs/2401.09670

2. **Patel, P., et al. (2024).** *Splitwise: Efficient Generative LLM Inference Using Phase Splitting.*  
   https://arxiv.org/abs/2311.18677

3. **Qin, R., et al. (2024).** *Mooncake: A KVCache-centric Disaggregated Architecture for LLM Serving.*  
   https://arxiv.org/abs/2407.00079
