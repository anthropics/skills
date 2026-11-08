# 多卡互联技术

> 理解 GPU 间通信技术，为分布式训练打下基础。

## 目录

- [互联技术概览](#互联技术概览)
- [PCIe 互联](#pcie-互联)
- [NVLink 详解](#nvlink-详解)
- [NVSwitch 架构](#nvswitch-架构)
- [InfiniBand 多机互联](#infiniband-多机互联)
- [互联选型建议](#互联选型建议)

---

## 互联技术概览

### 生活类比：不同的"交通方式"

```
GPU 互联技术就像不同的交通方式，每种适合不同距离和吞吐量：

PCIe:         普通公路
  带宽 ~64-128 GB/s, 延迟高
  类比: 城市道路，谁都能用，但堵车

NVLink:       高铁专线
  带宽 900-1800 GB/s, 延迟低
  类比: 高铁，快但只连特定站点（NVIDIA GPU 专用）

NVSwitch:     城市地铁网
  全互联，任意站点等时到达
  类比: 环线地铁，任意两站直达，不用换乘

InfiniBand:   城际飞机
  跨城市（跨机器）高速通信
  类比: 机场快线，不同城市间的高速通道

为什么互联带宽对 AI 如此重要？
  分布式训练的关键操作——AllReduce 梯度同步：
  4 GPU 的 7B 模型: 每步同步 14 GB 梯度数据
  如果带宽低 → 大部分时间在等通信 → GPU 空转
```

### 技术对比表

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        GPU 互联技术对比                                  │
├──────────┬──────────────┬──────────┬────────────────────────────────────┤
│ 技术      │ 带宽(双向)   │ 延迟     │ 适用场景                          │
├──────────┼──────────────┼──────────┼────────────────────────────────────┤
│ PCIe 4.0 │ 64 GB/s      │ 高       │ 单机多卡（消费级/开发）            │
│ PCIe 5.0 │ 128 GB/s     │ 高       │ 单机多卡（新服务器）              │
│ NVLink4.0│ 900 GB/s     │ 低       │ 单机多卡（H100 DGX）             │
│ NVLink5.0│ 1,800 GB/s   │ 低       │ 单机多卡（B200 DGX）             │
│ NVSwitch │ 全带宽       │ 极低     │ 8 卡全互联（DGX 系统）            │
│ IB NDR   │ 50 GB/s      │ 中       │ 跨机通信（400Gb/s）              │
│ RoCE     │ 25 GB/s      │ 中       │ 跨机通信（以太网方案）            │
└──────────┴──────────────┴──────────┴────────────────────────────────────┘
```

### 带宽差异可视化

```
带宽对比 (GB/s, 对数刻度):

PCIe 4.0    █ 64
PCIe 5.0    ██ 128
NVLink 4.0  █████████████████████████████ 900
NVLink 5.0  ██████████████████████████████████████████████████████████ 1,800
─── 分割线：以上机内，以下跨机 ───
IB NDR      ██ 50  (注意：单位 GB/s = 400 Gbps)
RoCE        █ 25

关键发现：
  NVLink 是 PCIe 的 14x（4.0 vs 4.0）
  NVLink 是 InfiniBand 的 18x
  → 机内通信比机间快 18 倍！

这就是为什么：
  张量并行 (TP) 只在机内做（需要 NVLink 的高带宽）
  流水线并行 (PP) 可以跨机（通信量小，IB 够用）
  数据并行 (DP) 可以跨机（梯度同步可以与计算重叠）
```

---

## PCIe 互联

### PCIe 规格

| 版本 | 单通道带宽 | x16 带宽 (双向) | 典型应用 |
|------|-----------|----------------|----------|
| PCIe 3.0 | 1 GB/s | 32 GB/s | 老旧服务器 |
| PCIe 4.0 | 2 GB/s | 64 GB/s | 主流服务器 |
| PCIe 5.0 | 4 GB/s | 128 GB/s | 新一代服务器 |
| PCIe 6.0 | 8 GB/s | 256 GB/s | 未来 |

### PCIe 的拓扑结构与"距离"问题

```
典型双路服务器的 PCIe 拓扑：

            ┌──── CPU 0 ────┐      ┌──── CPU 1 ────┐
            │   PCIe Root    │      │   PCIe Root    │
            │   Complex      │      │   Complex      │
            └───┬───┬───┬───┘      └───┬───┬───┬───┘
                │   │   │              │   │   │
              GPU0 GPU1 GPU2         GPU3 GPU4 GPU5
                │   │   │              │   │   │
              NIC0  │   │            NIC1  │   │
                    │   │                  │   │
              ┌─────┘   └─────┐     ┌─────┘   └─────┐
              SSD0            SSD1  SSD2            SSD3

GPU0 → GPU1: 同一 CPU 下，直接 P2P → 64 GB/s
GPU0 → GPU3: 不同 CPU，经过 QPI/UPI → 可能只有 30 GB/s
GPU0 → NIC1: 跨 NUMA 节点 → 额外延迟

"亲和性"(Affinity) 很重要：
  训练时，GPU、NIC、数据 SSD 应该在同一 NUMA 节点下
  否则跨节点通信成为隐形瓶颈
```

### PCIe P2P 通信

```python
import torch

def check_p2p():
    """检查 GPU 间 P2P 直连能力"""
    n_gpus = torch.cuda.device_count()
    print(f"GPU 数量: {n_gpus}")
    
    for i in range(n_gpus):
        for j in range(n_gpus):
            if i != j:
                can_access = torch.cuda.can_device_access_peer(i, j)
                print(f"GPU{i} → GPU{j}: {'✓ P2P' if can_access else '✗ 需经 CPU'}")
    
    # P2P 可用 → 数据直接在 GPU 间传输（走 PCIe 或 NVLink）
    # P2P 不可用 → 先到 CPU 内存，再传到目标 GPU（慢 2 倍）

check_p2p()
```

---

## NVLink 详解

### NVLink 为什么比 PCIe 快这么多？

```
关键区别不只是"更快的总线"，而是完全不同的设计理念：

PCIe:
  - 通用标准，兼容所有设备（GPU、SSD、网卡、声卡...）
  - 协议开销大（包头、CRC、TLP 封装）
  - 共享拓扑（多设备竞争带宽）

NVLink:
  - NVIDIA GPU 专用（不用兼容其他设备）
  - 极低协议开销（GPU 对 GPU 直连，没有中间层）
  - 专用链路（每对 GPU 有独立的物理连线）

类比：
  PCIe = 公共网络（要走 TCP/IP 协议栈，有路由器）
  NVLink = 两台电脑直接用网线连（低延迟，全带宽）
```

### NVLink 代际演进

| 版本 | 引入架构 | 链路带宽 | 最大链路数 | 总带宽/GPU |
|------|----------|---------|-----------|-----------|
| NVLink 1.0 | Pascal | 40 GB/s | 4 | 160 GB/s |
| NVLink 2.0 | Volta | 50 GB/s | 6 | 300 GB/s |
| NVLink 3.0 | Ampere | 50 GB/s | 12 | 600 GB/s |
| NVLink 4.0 | Hopper | 50 GB/s | 18 | 900 GB/s |
| NVLink 5.0 | Blackwell | 100 GB/s | 18 | 1,800 GB/s |

### NVLink 对分布式训练的影响

```
以 AllReduce 同步 7B 模型的梯度 (14 GB FP16) 为例：

4 GPU，Ring AllReduce 通信量 ≈ 2 × 14 GB = 28 GB

PCIe 4.0:  28 GB / 64 GB/s  = 437 ms   ← 太慢了
NVLink 4.0: 28 GB / 900 GB/s = 31 ms   ← 14 倍加速

如果一步训练的计算时间是 100 ms:
  PCIe:   总时间 = 100 + 437 = 537 ms (计算只占 19%)
  NVLink: 总时间 = 100 + 31 = 131 ms  (计算占 76%)
  
  实际上 NVLink + DDP 桶化可以实现通信-计算重叠
  → 总时间 ≈ max(100, 31) = 100 ms → 通信完全被隐藏

结论：
  PCIe → 通信成为严重瓶颈
  NVLink → 通信几乎可以完全重叠
  这就是为什么数据中心训练必须用 NVLink
```

---

## NVSwitch 架构

### 为什么需要 NVSwitch？

```
问题：8 个 GPU 用 NVLink 全互联需要多少链路？

全连接：每对 GPU 一条链路
  8 GPU → C(8,2) = 28 条链路
  每个 GPU 需要 7 条 NVLink 出接口
  
  但 H100 只有 18 条 NVLink 链路！
  直接全连接：每对 GPU 只有 18/7 ≈ 2.5 条 → 带宽受限

NVSwitch 解决方案：
  中间加一层交换芯片，类似网络交换机

  ┌─────────────────────────────────────┐
  │            NVSwitch ×4               │
  │   (每个 NVSwitch 连接所有 8 个 GPU)  │
  └──┬────┬────┬────┬────┬────┬────┬──┘
     │    │    │    │    │    │    │
  ┌──▼──┬─▼──┬─▼──┬─▼──┬─▼──┬─▼──┬─▼──┬────┐
  │GPU0│GPU1│GPU2│GPU3│GPU4│GPU5│GPU6│GPU7│
  └────┴────┴────┴────┴────┴────┴────┴────┘

  每个 GPU 的 18 条 NVLink 全部连到 NVSwitch
  NVSwitch 像交换机一样，任意 GPU 对之间全速转发
  → 每对 GPU 之间都有 900 GB/s 带宽！
```

### DGX H100 的 NVLink 拓扑

```
DGX H100 = 8×H100 + 4×NVSwitch

特性：
  任意 GPU 对带宽: 900 GB/s（全速 NVLink 4.0）
  总互联带宽: 3.6 TB/s per GPU（出 + 入）
  AllReduce 8 GPU: 延迟 < 10 微秒
  
  对比：
  8×A100 PCIe 版: GPU 间只有 64 GB/s → 数据中心不会买这个
  8×A100 SXM 版: GPU 间 600 GB/s (NVLink 3.0)
  8×H100 SXM 版: GPU 间 900 GB/s (NVLink 4.0)

NVSwitch 的另一个重要能力：统一内存寻址
  8×80 GB = 640 GB 的"统一显存池"
  任意 GPU 可以直接读写其他 GPU 的显存
  → 像是一张 640 GB 显存的超级 GPU
```

### NVLink 5.0 + NVSwitch 4.0 (Blackwell)

```
GB200 NVL72 系统：
  72 个 B200 GPU 通过 NVLink 5.0 全互联

  72 × 192 GB = 13.8 TB 统一显存
  每 GPU 带宽: 1.8 TB/s NVLink

  这意味着：
  1 万亿参数模型 (FP16 = 2 TB) 可以分布在 72 卡上
  每卡只需存 ~28 GB 参数
  且 GPU 间通信带宽足以支撑张量并行扩展到 72 路
```

---

## InfiniBand 多机互联

### 为什么跨机通信比机内难？

```
机内 (NVLink): 
  芯片到芯片，距离 < 1 米
  专用协议，硬件直连
  带宽 900+ GB/s

跨机 (InfiniBand/以太网):
  需要走网线/光纤，距离 1-100 米
  需要网络协议栈（即使是 RDMA 也有开销）
  带宽 25-50 GB/s
  
  速度差 18 倍以上！

这就是分布式训练架构设计的核心约束：
  高通信操作 (TP) → 只放机内
  低通信操作 (PP, DP) → 可以跨机
```

### InfiniBand 规格

| 版本 | 信号速率 | x4 链路带宽 | 典型部署 |
|------|----------|------------|----------|
| EDR | 25 Gb/s | 100 Gb/s (12.5 GB/s) | 旧集群 |
| HDR | 50 Gb/s | 200 Gb/s (25 GB/s) | 主流集群 |
| NDR | 100 Gb/s | 400 Gb/s (50 GB/s) | 新建集群 |
| XDR | 200 Gb/s | 800 Gb/s (100 GB/s) | 未来 |

### 多机互联架构

```
┌─────────────────────────────────────────────────────────────┐
│              多机 GPU 集群网络架构                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌────────────────┐      ┌────────────────┐               │
│   │   Node 0       │      │   Node 1       │               │
│   │  ┌──┬──┬──┬──┐ │      │  ┌──┬──┬──┬──┐ │               │
│   │  │G0│G1│G2│G3│ │      │  │G0│G1│G2│G3│ │               │
│   │  └──┴──┴──┴──┘ │      │  └──┴──┴──┴──┘ │               │
│   │   NVLink 互联  │      │   NVLink 互联  │               │
│   │       │        │      │       │        │               │
│   │   ┌───┴───┐    │      │   ┌───┴───┐    │               │
│   │   │  NIC  │────┼──IB──┼───│  NIC  │    │               │
│   │   └───────┘    │      │   └───────┘    │               │
│   └────────────────┘      └────────────────┘               │
│                                                             │
│   节点内: NVLink 900 GB/s                                   │
│   节点间: IB NDR 400 Gb/s = 50 GB/s                        │
│                                                             │
│   通常每节点配 8 个 NIC（每 GPU 一个）                      │
│   → 节点总出口带宽: 8 × 50 = 400 GB/s                      │
└─────────────────────────────────────────────────────────────┘
```

### GPUDirect 技术——绕过 CPU

```
传统数据路径（慢）：
  GPU 0 (Node A) → CPU 内存 → NIC → 网络 → NIC → CPU 内存 → GPU 0 (Node B)
  经过 2 次 PCIe + 2 次内存拷贝 → 延迟高，CPU 成为瓶颈

GPUDirect RDMA（快）：
  GPU 0 (Node A) → NIC → 网络 → NIC → GPU 0 (Node B)
  GPU 直接与 NIC 通信，完全绕过 CPU！

  ┌──────┐          ┌──────┐
  │ GPU  │ ←──────→ │ NIC  │ ─── 网络 ───→
  │      │  PCIe P2P│      │
  └──────┘          └──────┘
  CPU 完全不参与，数据路径最短

技术栈：
  GPUDirect P2P:     机内 GPU 间直传（绕过 CPU 内存）
  GPUDirect RDMA:    GPU 直接与网卡通信（跨机绕过 CPU）
  GPUDirect Storage: GPU 直接与 NVMe 通信（加速数据加载）

效果：
  传统：~15 GB/s + 高延迟
  GPUDirect RDMA：~50 GB/s + 低延迟
  → 跨机通信效率提升 3 倍以上
```

---

## 互联选型建议

### 场景选型

| 场景 | 推荐方案 | 理由 |
|------|----------|------|
| 单机 2-4 卡 (消费级) | PCIe | 成本低，够用 |
| 单机 4-8 卡 (训练) | NVLink + NVSwitch | 高带宽，低延迟 |
| 多机 (中小规模) | InfiniBand HDR | 成熟稳定 |
| 多机 (大规模) | InfiniBand NDR | 最高性能 |
| 预算有限多机 | RoCE v2 | 使用现有以太网基础设施 |

### 成本与性能权衡

```
构建一个 8 机 64 GPU 集群的互联选择：

方案 A: PCIe 机内 + 25GbE 以太网跨机
  成本: ~$50K (网络部分)
  性能: 机内 64 GB/s，跨机 3 GB/s
  适用: 实验/开发，不适合大模型训练

方案 B: NVLink 机内 + IB HDR 跨机
  成本: ~$500K (DGX + IB 交换机)
  性能: 机内 900 GB/s，跨机 25 GB/s
  适用: 中等规模生产训练

方案 C: NVLink 机内 + IB NDR 跨机 + GPUDirect
  成本: ~$800K
  性能: 机内 900 GB/s，跨机 50 GB/s
  适用: 大规模生产训练

方案 A 看似省钱，但训练效率可能只有方案 C 的 30%
  → 如果训练任务重，方案 C 的 TCO（总拥有成本）反而更低
```

### 互联与并行策略的匹配

```
分布式训练不同的并行策略对互联带宽的需求不同：

┌────────────┬──────────────────────────────────┐
│ 并行策略    │ 互联需求                          │
├────────────┼──────────────────────────────────┤
│ 张量并行TP  │ 每层 2 次 AllReduce              │
│            │ 需要最高带宽 → 必须 NVLink        │
│            │ 通常 TP ≤ 8（一台机器内）         │
├────────────┼──────────────────────────────────┤
│ 流水线PP   │ 相邻 Stage 传中间激活值           │
│            │ 通信量小 → IB 足够               │
│            │ 可以跨机部署                      │
├────────────┼──────────────────────────────────┤
│ 数据并行DP  │ 每步 AllReduce 梯度              │
│            │ 可以与计算重叠 → IB 够用          │
│            │ 跨机部署                          │
├────────────┼──────────────────────────────────┤
│ 3D 并行    │ TP 机内 NVLink                   │
│ (TP+PP+DP) │ PP 和 DP 跨机 IB                │
│            │ 最佳实践组合                      │
└────────────┴──────────────────────────────────┘
```

---

## 小结

```
多卡互联核心知识：

1. PCIe: 通用但慢，适合开发/小规模
2. NVLink: NVIDIA 专有，10x+ 于 PCIe，机内训练必备
3. NVSwitch: 让 8 GPU 全速互联，DGX 系统标配
4. InfiniBand: 跨机高性能通信首选，GPUDirect RDMA 绕过 CPU
5. 选型原则: 互联带宽必须匹配并行策略的通信需求
   TP → NVLink，PP/DP → IB，千万不要反过来
```

---

*下一篇：[08-hardware-selection.md](08-hardware-selection.md) - 硬件选型指南*

---

## 参考资料与引用

1. **NVIDIA.** *NVLink and NVSwitch.*  
   https://www.nvidia.com/en-us/data-center/nvlink/

2. **NVIDIA.** *DGX A100 System Architecture.* — DGX 系统中的 NVSwitch 拓扑  
   https://www.nvidia.com/en-us/data-center/dgx-a100/

3. **Li, S., et al. (2020).** *Evaluating Modern GPU Interconnect: PCIe, NVLink, NV-SLI, NVSwitch and GPUDirect.* — GPU 互联技术性能对比  
   https://arxiv.org/abs/1903.04611

4. **NVIDIA.** *GPUDirect RDMA.* — GPU 直接远程内存访问  
   https://docs.nvidia.com/cuda/gpudirect-rdma/

5. **Mellanox/NVIDIA.** *InfiniBand Overview.*  
   https://www.nvidia.com/en-us/networking/infiniband/
