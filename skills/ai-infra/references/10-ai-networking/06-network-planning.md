# 网络规划与建设

> 好的网络规划在建设之初就决定了集群的性能上限——网络一旦铺好，改造成本比重新建设还高。

## 目录

- [带宽规划方法](#带宽规划方法)
- [交换机选型](#交换机选型)
- [布线设计](#布线设计)
- [成本估算](#成本估算)
- [云上网络 vs 自建](#云上网络-vs-自建)
- [分阶段建设方案](#分阶段建设方案)
- [延伸阅读](#延伸阅读)

---

## 带宽规划方法

### 从训练需求推导网络需求

```python
"""AI 集群网络带宽规划"""

def plan_network_bandwidth(
    model_params_b: float,
    num_gpus: int,
    gpus_per_node: int = 8,
    target_mfu: float = 0.5,     # 目标 MFU (Model FLOPS Utilization)
    gpu_tflops: float = 989,      # H100 BF16 TFLOPS
):
    """从训练需求推导网络带宽需求"""
    
    num_nodes = num_gpus // gpus_per_node
    model_size_gb = model_params_b * 2  # BF16
    
    # AllReduce 通信量 (Ring)
    allreduce_gb = 2 * model_size_gb
    
    # 计算时间估算 (一个 step)
    # 简化: 70B 模型在 H100 上约 0.5s/step (batch=4096)
    compute_time_s = (model_params_b / 70) * 0.5
    
    # 通信时间需要 < 计算时间 (实现重叠)
    # 否则通信成为瓶颈
    target_comm_time_s = compute_time_s
    
    # 所需网络带宽
    required_bw_gbs = allreduce_gb / target_comm_time_s
    required_bw_gbps = required_bw_gbs * 8
    
    print(f"=== 网络带宽规划 ===")
    print(f"模型: {model_params_b}B, 集群: {num_gpus} GPU ({num_nodes} 节点)")
    print(f"")
    print(f"每 step AllReduce: {allreduce_gb:.0f} GB")
    print(f"计算时间估算: {compute_time_s:.2f}s")
    print(f"所需聚合带宽: {required_bw_gbs:.0f} GB/s ({required_bw_gbps:.0f} Gbps)")
    print(f"每节点所需: {required_bw_gbs/num_nodes:.0f} GB/s "
          f"({required_bw_gbps/num_nodes:.0f} Gbps)")
    print(f"")
    
    # 推荐方案
    ib_ndr = 400  # Gbps per port
    ib_hdr = 200
    roce_100 = 100
    
    per_node_gbps = required_bw_gbps / num_nodes
    
    print(f"--- 推荐配置 ---")
    if per_node_gbps <= 400:
        print(f"方案: 每节点 1× NDR 400G InfiniBand")
    elif per_node_gbps <= 800:
        print(f"方案: 每节点 2× NDR 400G InfiniBand")
    elif per_node_gbps <= 3200:
        print(f"方案: 每节点 8× NDR 400G InfiniBand (Rail-optimized)")
    
    print(f"Rail-opt: {gpus_per_node}× NDR 400G = {gpus_per_node * 50} GB/s/节点")

plan_network_bandwidth(model_params_b=70, num_gpus=256)
```

---

## 交换机选型

### InfiniBand 交换机

| 交换机 | 速率 | 端口数 | 特点 | 参考价格 |
|--------|------|--------|------|---------|
| **QM9700** (NVIDIA) | NDR 400G | 64 | 最新一代，AI 集群首选 | ~$30,000 |
| **QM8700** (NVIDIA) | HDR 200G | 40 | 上一代，性价比高 | ~$15,000 |
| **QM9790** (NVIDIA) | NDR 400G | 128 | 大端口数，减少层级 | ~$60,000 |

### RoCE 以太网交换机

| 交换机 | 速率 | 端口数 | 特点 | 参考价格 |
|--------|------|--------|------|---------|
| **SN5600** (NVIDIA) | 400G | 64 | 支持 RoCE，AI 优化 | ~$25,000 |
| **SN4700** (NVIDIA) | 400G | 32 | 中型集群 | ~$15,000 |
| **Arista 7800R** | 400G | 高密度 | 企业级，功能丰富 | ~$35,000 |
| **Juniper QFX** | 400G | 可变 | 企业级 | ~$30,000 |

---

## 布线设计

```
布线设计要点:

  线缆类型选择:
  ┌──────────┬─────────┬──────────┬───────────┬─────────┐
  │ 类型      │ 距离    │ 速率     │ 成本/根   │ 适用     │
  ├──────────┼─────────┼──────────┼───────────┼─────────┤
  │ DAC 铜缆  │ < 3m   │ 400G    │ ~$100     │ 机柜内   │
  │ AOC 有源  │ < 100m │ 400G    │ ~$300-500 │ 跨机柜   │
  │ 光纤+模块│ < 2km  │ 400G    │ ~$800+    │ 跨机房   │
  └──────────┴─────────┴──────────┴───────────┴─────────┘

  布线原则:
    1. 机柜内使用 DAC（最便宜、最低延迟）
    2. 跨机柜使用 AOC（性价比）
    3. 预留 20% 冗余端口
    4. 线缆长度留 10% 余量
    5. 做好标签管理（两端标注）
    6. 分离管理网/计算网/存储网

  机柜布局:
    每机柜: 4 个 GPU 节点 + 1-2 个 Leaf 交换机
    交换机放在机柜中间（减少线缆长度）
    注意散热和功耗规划
```

---

## 成本估算

### 不同规模的网络成本

```
网络成本估算 (IB NDR 400G, Rail-optimized):

  64 GPU (8 节点):
    Leaf 交换机: 8 × QM9700 = $240,000
    线缆: 64 × DAC/AOC = $32,000
    管理网: 1 × 以太网交换机 = $5,000
    ──────────────────────────
    总计: ~$277,000 ($4,328/GPU)

  256 GPU (32 节点):
    Leaf 交换机: 8 × QM9700 = $240,000
    线缆: 256 × AOC = $128,000
    管理网: 2 × 以太网交换机 = $10,000
    ──────────────────────────
    总计: ~$378,000 ($1,477/GPU)

  1024 GPU (128 节点):
    Leaf 交换机: 8 × QM9700 = $240,000
    Spine 交换机: 4 × QM9790 = $240,000
    线缆: 1024 + spine连线 = $600,000
    管理网: 4 × 以太网交换机 = $20,000
    ──────────────────────────
    总计: ~$1,100,000 ($1,074/GPU)

  网络成本占 GPU 集群总成本: 约 5-15%
  (H100 GPU 服务器约 $300,000-400,000/节点)
```

---

## 云上网络 vs 自建

| 维度 | 云上网络 | 自建网络 |
|------|---------|---------|
| **带宽** | 受限于云实例类型 | 完全可控 |
| **延迟** | 中 (~5-10 μs) | 低 (~1-2 μs) |
| **灵活性** | 弹性伸缩 | 固定规模 |
| **成本(短期)** | 低 | 高(前期投入) |
| **成本(长期)** | 高 | 低(摊销后) |
| **运维** | 免运维 | 需专业团队 |
| **拓扑控制** | 有限 | 完全可控 |

```
决策建议:
  训练 < 3 个月 → 云上 (弹性，免运维)
  训练 3-12 个月 → 混合 (部分自建+部分云)
  训练 > 12 个月 → 自建 (成本更优)
  
  关键: 云上多节点训练的网络性能
        通常比自建差 20-40%
        部分云商提供高性能集群实例(如 AWS p5, GCP a3)
```

---

## 分阶段建设方案

```
AI 集群网络分阶段建设:

  Phase 1: MVP (8-32 GPU)
    网络: 以太网 100G RoCE 或小型 IB
    目标: 验证训练流程
    预算: $50,000-100,000

  Phase 2: 扩展 (64-256 GPU)  
    网络: IB NDR 400G Rail-optimized
    目标: 正式训练中大模型
    预算: $300,000-500,000

  Phase 3: 规模化 (512-2048 GPU)
    网络: IB NDR/XDR + Spine 层
    目标: 训练超大模型
    预算: $1M-3M

  每阶段注意:
    设备选型兼容下一阶段
    预留上联端口和机柜空间
    布线基础设施一次到位
```

---

## 延伸阅读

- [NVIDIA DGX SuperPOD Network Design](https://docs.nvidia.com/dgx-superpod/)
- [Data Center Network Design Guides](https://www.nvidia.com/en-us/networking/)
- [AI Cluster Networking Best Practices](https://docs.nvidia.com/networking/)

---

*上一篇：[05-network-troubleshooting.md](05-network-troubleshooting.md)*

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **NVIDIA.** *DGX SuperPOD Reference Architecture.*  
   https://docs.nvidia.com/dgx-superpod/

2. **NVIDIA.** *Spectrum-X Ethernet for AI.*  
   https://www.nvidia.com/en-us/networking/spectrumx/
