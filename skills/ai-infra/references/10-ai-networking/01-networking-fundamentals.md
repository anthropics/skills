# AI 网络基础

> 当一个训练 step 中 GPU 计算只需 0.5 秒，但梯度同步却需要 2 秒时，网络就是你的首要瓶颈。

## 目录

- [为什么网络是大规模训练的瓶颈](#为什么网络是大规模训练的瓶颈)
- [AI 训练的通信模式](#ai-训练的通信模式)
- [通信带宽需求估算](#通信带宽需求估算)
- [网络延迟影响分析](#网络延迟影响分析)
- [AI 网络 vs 传统数据中心网络](#ai-网络-vs-传统数据中心网络)
- [延伸阅读](#延伸阅读)

---

## 为什么网络是大规模训练的瓶颈

### 生活类比：工厂流水线

```
分布式训练就像一条跨工厂的流水线:

  每个工厂(节点) = 8 条生产线(GPU)
  产品(梯度) = 每轮生产完要汇总到总部再分发

  工厂内部: NVLink 高速传送带 (900 GB/s)
    → 同一工厂内的传送带又宽又快

  工厂之间: InfiniBand/RoCE 公路 (50 GB/s)
    → 工厂间的公路窄得多

  问题:
    256 条生产线同时完工 → 所有产品同时上路
    如果公路不够宽 → 大堵车 → 所有工厂等待
    → GPU 利用率从 100% 降到 30%
```

### 通信 vs 计算时间占比

```
┌─────────────────────────────────────────────────────────────────┐
│              通信与计算的时间占比（不同规模）                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  8 GPU (单机, NVLink):                                           │
│  ████████████████████████████░░  通信占比: ~10%                  │
│  计算                        通信                                │
│                                                                 │
│  64 GPU (8 节点, IB/RoCE):                                       │
│  █████████████████████░░░░░░░░░  通信占比: ~30%                  │
│  计算                  通信                                      │
│                                                                 │
│  256 GPU (32 节点):                                               │
│  ██████████████░░░░░░░░░░░░░░░░  通信占比: ~45%                  │
│  计算            通信                                            │
│                                                                 │
│  1024 GPU (128 节点):                                             │
│  █████████░░░░░░░░░░░░░░░░░░░░░  通信占比: ~60%                  │
│  计算      通信                                                  │
│                                                                 │
│  随着规模增大，通信占比急剧上升                                   │
│  → 网络带宽直接决定了训练的线性扩展效率                           │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## AI 训练的通信模式

### 主要通信原语

```
┌─────────────────────────────────────────────────────────────────┐
│                AI 训练核心通信原语                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. AllReduce (最常用)                                            │
│     场景: 数据并行 — 梯度聚合                                    │
│     流程: 每个 GPU 的梯度 → 求和/平均 → 分发回所有 GPU           │
│     通信量: 2 × model_size (Ring AllReduce)                      │
│     70B 模型: 2 × 140 GB = 280 GB/step                          │
│                                                                 │
│  2. AllGather                                                    │
│     场景: ZeRO Stage 3 — 前向传播时收集完整参数                  │
│     流程: 每个 GPU 的参数分片 → 拼接为完整参数                   │
│     通信量: model_size × (N-1)/N ≈ model_size                   │
│                                                                 │
│  3. ReduceScatter                                                │
│     场景: ZeRO Stage 3 — 反向传播时分散梯度                      │
│     流程: 梯度求和 → 每个 GPU 只保留自己负责的分片               │
│     通信量: model_size × (N-1)/N                                 │
│                                                                 │
│  4. Point-to-Point (Send/Recv)                                   │
│     场景: 流水线并行 — 层间激活值传递                             │
│     流程: 上一阶段 GPU → 下一阶段 GPU                            │
│     通信量: activation_size × micro_batch_size                    │
│                                                                 │
│  5. AlltoAll                                                     │
│     场景: 专家并行 (MoE) — Token 到专家的路由                    │
│     流程: 每个 GPU 发送部分 token 到对应专家所在 GPU              │
│     通信量: batch_size × hidden_size × expert_ratio               │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 不同并行策略的通信模式

| 并行策略 | 主要通信原语 | 通信量 | 通信模式 | 网络需求 |
|---------|------------|--------|---------|---------|
| **数据并行 (DP)** | AllReduce | 2 × model_size/step | All-to-All | 高带宽 |
| **ZeRO Stage 3** | AllGather + ReduceScatter | ~3 × model_size/step | All-to-All | 极高带宽 |
| **张量并行 (TP)** | AllReduce | 较小(每层) | 节点内 | NVLink |
| **流水线并行 (PP)** | P2P Send/Recv | activation_size | 相邻节点 | 低延迟 |
| **专家并行 (EP)** | AlltoAll | 动态 | All-to-All | 高带宽+低延迟 |

---

## 通信带宽需求估算

### 估算公式

```python
"""AI 训练网络带宽需求估算"""

def estimate_bandwidth_requirement(
    model_params_b: float,    # 模型参数量（十亿）
    precision_bytes: int = 2, # 精度（BF16=2, FP32=4）
    num_gpus: int = 256,
    num_nodes: int = 32,
    gpus_per_node: int = 8,
    target_step_time_s: float = 1.0,
    parallel_strategy: str = "dp",  # dp, zero3, tp+dp
):
    """估算分布式训练所需的网络带宽"""
    
    model_size_gb = model_params_b * precision_bytes
    
    if parallel_strategy == "dp":
        # 数据并行: AllReduce 通信量 = 2 × model_size (Ring)
        comm_volume_gb = 2 * model_size_gb
    elif parallel_strategy == "zero3":
        # ZeRO-3: AllGather + ReduceScatter
        comm_volume_gb = 3 * model_size_gb
    elif parallel_strategy == "tp+dp":
        # 张量并行在节点内（NVLink），数据并行在节点间
        tp_size = gpus_per_node
        dp_size = num_gpus // tp_size
        comm_volume_gb = 2 * model_size_gb / tp_size  # DP AllReduce
    
    # 所需带宽
    required_bw_gbs = comm_volume_gb / target_step_time_s
    
    # 通信效率（考虑协议开销、拓扑效率）
    efficiency = 0.7
    actual_bw_needed = required_bw_gbs / efficiency
    
    # 每链路所需带宽
    per_link_bw = actual_bw_needed / num_nodes
    
    print(f"=== 网络带宽需求估算 ===")
    print(f"模型: {model_params_b}B, 精度: {'BF16' if precision_bytes == 2 else 'FP32'}")
    print(f"集群: {num_gpus} GPU ({num_nodes} 节点)")
    print(f"并行策略: {parallel_strategy}")
    print(f"")
    print(f"每 step 通信量: {comm_volume_gb:.0f} GB")
    print(f"目标 step 时间: {target_step_time_s}s")
    print(f"所需网络带宽: {required_bw_gbs:.0f} GB/s")
    print(f"考虑效率后: {actual_bw_needed:.0f} GB/s")
    print(f"")
    
    # 推荐网络方案
    ib_hdr_bw = 25  # GB/s (200 Gbps)
    ib_ndr_bw = 50  # GB/s (400 Gbps)
    roce_100g = 12.5  # GB/s
    
    print(f"--- 网络方案推荐 ---")
    print(f"InfiniBand HDR (200G): 需要 {actual_bw_needed/ib_hdr_bw:.0f} 条链路")
    print(f"InfiniBand NDR (400G): 需要 {actual_bw_needed/ib_ndr_bw:.0f} 条链路")
    print(f"RoCE 100G:            需要 {actual_bw_needed/roce_100g:.0f} 条链路")

# 估算示例
estimate_bandwidth_requirement(
    model_params_b=70,
    num_gpus=256,
    num_nodes=32,
    parallel_strategy="dp",
)
```

---

## 网络延迟影响分析

### 延迟组成

```
AI 训练中的网络延迟组成:

  软件栈:
    应用层 (PyTorch/NCCL)    ~1 μs
    内核网络栈 (TCP/IP)       ~10-50 μs
    RDMA bypass (Verbs API)   ~1 μs
    驱动层                    ~1 μs

  硬件:
    HCA/NIC 处理              ~1 μs
    交换机转发 (每跳)          ~0.1-0.5 μs
    光纤传播 (每100m)          ~0.5 μs
    序列化延迟                 取决于消息大小

  总延迟对比:
    TCP/IP (以太网):          ~50-100 μs
    RoCE v2 (RDMA):           ~2-5 μs
    InfiniBand (RDMA):        ~1-2 μs
    NVLink (节点内):          ~0.1-0.5 μs

  对训练的影响:
    大消息 (AllReduce): 带宽主导，延迟影响小
    小消息 (P2P, AlltoAll): 延迟主导，影响大
    流水线并行: 每个 micro-batch 都有延迟开销
    → 流水线并行对网络延迟更敏感
```

---

## AI 网络 vs 传统数据中心网络

| 维度 | 传统数据中心 | AI 训练网络 |
|------|------------|------------|
| **流量模式** | 客户端-服务器（南北） | GPU-GPU（东西向） |
| **带宽需求** | 10-100 Gbps | 200-800 Gbps |
| **延迟要求** | ~1 ms 可接受 | < 5 μs |
| **传输协议** | TCP/IP | RDMA (IB/RoCE) |
| **流量特征** | 异步、突发 | 同步、周期性、爆发 |
| **可靠性** | 重传机制 | 无损网络 (PFC/ECN) |
| **拥塞控制** | TCP 拥塞控制 | DCQCN / 硬件流控 |
| **多播** | 较少使用 | 广泛使用 (AllReduce) |
| **成本/端口** | ~$100-500 | ~$2,000-5,000 |

---

## 延伸阅读

- [NVIDIA NCCL Documentation](https://docs.nvidia.com/deeplearning/nccl/)
- [InfiniBand Architecture Specification](https://www.infinibandta.org/)
- 论文: *Scaling Distributed Machine Learning with the Parameter Server* (OSDI '14)
- 论文: *Efficient Large-Scale Language Model Training on GPU Clusters* (SC '21)

---

*下一篇：[02-rdma-deep-dive.md](02-rdma-deep-dive.md)*

*返回：[README.md](README.md) - 章节索引*
