# 网络拓扑设计

> 网络拓扑决定了数据在 GPU 之间的流动路径——选对拓扑，训练效率事半功倍。

## 目录

- [拓扑基础概念](#拓扑基础概念)
- [Fat-tree/Clos 拓扑](#fat-treeclos-拓扑)
- [Rail-optimized 拓扑](#rail-optimized-拓扑)
- [Dragonfly 拓扑](#dragonfly-拓扑)
- [拓扑选择对训练性能的影响](#拓扑选择对训练性能的影响)
- [实际集群拓扑设计案例](#实际集群拓扑设计案例)
- [延伸阅读](#延伸阅读)

---

## 拓扑基础概念

### 生活类比：城市交通网络

```
不同拓扑 = 不同的城市交通设计:

  Fat-tree = 树状高速公路网
    乡村小路 → 省道 → 国道 → 高速 → 国道 → 省道 → 小路
    任何两地都能到达，但经过多层换乘
    每层道路越来越宽（Fat = 上层越胖）

  Rail-optimized = 轨道交通网
    每条地铁线连接同一"位置"的站点
    同一条线上的站点通信快
    不同线之间需要换乘

  Dragonfly = 航空网络
    每个城市群内部公路相连
    城市群之间有直飞航线
    长距离通信走"直飞"
```

---

## Fat-tree/Clos 拓扑

### 架构详解

```
┌─────────────────────────────────────────────────────────────────┐
│                 Fat-tree (3 层 Clos) 拓扑                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Core Layer (核心层):                                            │
│     ┌───┐  ┌───┐  ┌───┐  ┌───┐                                 │
│     │ C1│  │ C2│  │ C3│  │ C4│   核心交换机                     │
│     └─┬─┘  └─┬─┘  └─┬─┘  └─┬─┘                                 │
│       │╲  ╱│  │╲  ╱│  │╲  ╱│                                    │
│       │ ╲╱ │  │ ╲╱ │  │ ╲╱ │   全互联                          │
│       │ ╱╲ │  │ ╱╲ │  │ ╱╲ │                                    │
│       │╱  ╲│  │╱  ╲│  │╱  ╲│                                    │
│     ┌─┴─┐  ┌─┴─┐  ┌─┴─┐  ┌─┴─┐                                │
│  Spine│S1│  │S2│  │S3│  │S4│  Spine/汇聚层交换机                │
│     └─┬─┘  └─┬─┘  └─┬─┘  └─┬─┘                                │
│       │      │      │      │                                    │
│     ┌─┴─┐  ┌─┴─┐  ┌─┴─┐  ┌─┴─┐                                │
│  Leaf│L1│  │L2│  │L3│  │L4│  Leaf/接入层交换机                  │
│     └─┬─┘  └─┬─┘  └─┬─┘  └─┬─┘                                │
│     ┌─┴─┐  ┌─┴─┐  ┌─┴─┐  ┌─┴─┐                                │
│     │N1 │  │N2 │  │N3 │  │N4 │  计算节点(GPU)                   │
│     │N2 │  │N4 │  │N6 │  │N8 │                                  │
│     └───┘  └───┘  └───┘  └───┘                                  │
│                                                                 │
│  特点:                                                           │
│    ✓ 任意两个节点间等带宽（非阻塞）                              │
│    ✓ 多路径冗余，故障自动切换                                    │
│    ✓ 成熟的设计，广泛使用                                        │
│    ✗ 交换机数量多（成本高）                                      │
│    ✗ 布线复杂                                                    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Fat-tree 的关键参数

| 参数 | 说明 | AI 集群推荐 |
|------|------|------------|
| **层数** | 2层/3层 | < 256节点用2层，>256用3层 |
| **超额比(Oversubscription)** | 上行/下行带宽比 | AI训练: 1:1 (无超额) |
| **径向度(Radix)** | 交换机端口数 | 64口常见 |
| **ECMP** | 等价多路径路由 | 必须启用 |

---

## Rail-optimized 拓扑

### 架构详解

```
┌─────────────────────────────────────────────────────────────────┐
│                 Rail-optimized 拓扑                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  核心思想: 每个 GPU "轨道"(Rail) 连接独立的网络平面              │
│                                                                 │
│  节点 1          节点 2          节点 3          节点 4           │
│  ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐    │
│  │GPU0 GPU1│   │GPU0 GPU1│   │GPU0 GPU1│   │GPU0 GPU1│    │
│  │GPU2 GPU3│   │GPU2 GPU3│   │GPU2 GPU3│   │GPU2 GPU3│    │
│  │GPU4 GPU5│   │GPU4 GPU5│   │GPU4 GPU5│   │GPU4 GPU5│    │
│  │GPU6 GPU7│   │GPU6 GPU7│   │GPU6 GPU7│   │GPU6 GPU7│    │
│  └──┬┬┬┬┬┬┬┘   └──┬┬┬┬┬┬┬┘   └──┬┬┬┬┬┬┬┘   └──┬┬┬┬┬┬┬┘    │
│     ││││││││       ││││││││       ││││││││       ││││││││       │
│     ││││││││       ││││││││       ││││││││       ││││││││       │
│  Rail 0: GPU0─────GPU0─────GPU0─────GPU0  → Switch 0           │
│  Rail 1: GPU1─────GPU1─────GPU1─────GPU1  → Switch 1           │
│  Rail 2: GPU2─────GPU2─────GPU2─────GPU2  → Switch 2           │
│  Rail 3: GPU3─────GPU3─────GPU3─────GPU3  → Switch 3           │
│  Rail 4: GPU4─────GPU4─────GPU4─────GPU4  → Switch 4           │
│  Rail 5: GPU5─────GPU5─────GPU5─────GPU5  → Switch 5           │
│  Rail 6: GPU6─────GPU6─────GPU6─────GPU6  → Switch 6           │
│  Rail 7: GPU7─────GPU7─────GPU7─────GPU7  → Switch 7           │
│                                                                 │
│  每个 GPU 位置相同的 GPU 连接到同一个交换机                      │
│  节点内 GPU 之间通过 NVLink 通信                                 │
│                                                                 │
│  优势:                                                           │
│    ✓ 交换机数量少（8 个，vs Fat-tree 可能需 20+）                │
│    ✓ 布线简单（每个 GPU 只连一条网络线）                         │
│    ✓ 成本低 30-50%                                               │
│    ✓ 特别适合 AllReduce 通信模式                                 │
│                                                                 │
│  劣势:                                                           │
│    ✗ 跨 Rail 通信需要经过节点内 NVLink（增加延迟）               │
│    ✗ 不适合 AlltoAll 等随机通信模式                               │
│    ✗ 对 NCCL 拓扑感知优化有依赖                                  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Dragonfly 拓扑

```
Dragonfly 拓扑:

  核心思想: 分组(Group) + 组间直连

  ┌──────────┐     ┌──────────┐     ┌──────────┐
  │ Group 1  │←───→│ Group 2  │←───→│ Group 3  │
  │ ┌──┐┌──┐│     │ ┌──┐┌──┐│     │ ┌──┐┌──┐│
  │ │S1││S2││     │ │S1││S2││     │ │S1││S2││
  │ └┬─┘└┬─┘│     │ └┬─┘└┬─┘│     │ └┬─┘└┬─┘│
  │  │N1 │N2│     │  │N5 │N6│     │  │N9 │N10│
  │  │N3 │N4│     │  │N7 │N8│     │  │N11│N12│
  └──────────┘     └──────────┘     └──────────┘
       ↕                ↕                ↕
   组间全互联（每组有直连到其他每个组的链路）

  特点:
    ✓ 组内通信延迟极低（1 跳）
    ✓ 组间通信最多 3 跳
    ✓ 交换机数量少于 Fat-tree
    ✗ 组间带宽可能不足
    ✗ 设计和路由更复杂

  适用: 超大规模集群 (10000+ 节点, HPC)
  AI 场景: 较少单独使用，部分超大集群采用
```

---

## 拓扑选择对训练性能的影响

| 拓扑 | AllReduce 效率 | AlltoAll 效率 | 成本 | 适用规模 |
|------|---------------|--------------|------|---------|
| **Fat-tree 1:1** | 最优 | 最优 | 最高 | 任意 |
| **Fat-tree 2:1** | 好 | 中 | 高 | 中大规模 |
| **Rail-optimized** | 优秀 | 差 | 低 | 中大规模 |
| **Dragonfly** | 好 | 中 | 中 | 超大规模 |

### 选型建议

```
拓扑选型决策:

  使用 Fat-tree 1:1 (无超额):
    ✓ 需要 AlltoAll (MoE 模型)
    ✓ 多租户共享集群
    ✓ 预算充足

  使用 Rail-optimized:
    ✓ 主要做数据并行/张量并行 (AllReduce)
    ✓ 成本敏感
    ✓ DGX SuperPOD / HGX 架构
    ★ 目前最主流的大规模 AI 训练拓扑

  使用 Fat-tree 2:1 (2倍超额):
    ✓ 中等规模，需要一定灵活性
    ✓ 混合工作负载

  使用 Dragonfly:
    ✓ 超大规模 (万节点)
    ✓ HPC + AI 混合环境
```

---

## 实际集群拓扑设计案例

### 256 GPU Rail-optimized 集群

```
256 GPU (32 节点 × 8 GPU) Rail-optimized 设计:

  设备清单:
    计算节点: 32 × DGX H100 (或 HGX H100)
    Leaf 交换机: 8 × QM9700 (NDR 400G, 64 口)
    节点内互联: NVLink 4th Gen (900 GB/s)

  连接方式:
    每个节点的 GPU0 → Leaf Switch 0
    每个节点的 GPU1 → Leaf Switch 1
    ...
    每个节点的 GPU7 → Leaf Switch 7

  每个交换机: 32 个下行端口连节点 + 32 个端口备用/上联

  网络带宽:
    同 Rail GPU 间: 400 Gbps (50 GB/s) 直连
    跨 Rail GPU 间: 经过节点内 NVLink (900 GB/s)
    
  总成本 (网络部分):
    交换机: 8 × ~$30,000 = $240,000
    线缆: 256 × ~$500 = $128,000
    总计: ~$370,000 (约 $1,445/GPU)
```

---

## 延伸阅读

- [NVIDIA DGX SuperPOD Reference Architecture](https://docs.nvidia.com/dgx-superpod/)
- [Fat-tree Networks (Al-Fares et al., SIGCOMM '08)](https://dl.acm.org/doi/10.1145/1402958.1402967)
- [Rail-optimized Topology (NVIDIA)](https://docs.nvidia.com/networking/)
- 论文: *Technology-Driven, Highly-Scalable Dragonfly Topology* (ISCA '08)

---

*上一篇：[02-rdma-deep-dive.md](02-rdma-deep-dive.md)* | *下一篇：[04-gpudirect-technologies.md](04-gpudirect-technologies.md)*

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **Al-Fares, M., et al. (2008).** *A Scalable, Commodity Data Center Network Architecture (Fat-tree).* ACM SIGCOMM.  
   https://dl.acm.org/doi/10.1145/1402958.1402967

2. **NVIDIA.** *Rail-Optimized Network Topology.*  
   https://developer.nvidia.com/blog/rail-optimized-topology-for-ai-training/
