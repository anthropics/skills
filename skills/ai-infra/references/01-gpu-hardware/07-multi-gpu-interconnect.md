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

### 技术对比

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        GPU 互联技术对比                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  技术          带宽(双向)      延迟        适用场景                       │
│  ─────────     ──────────     ─────       ─────────                     │
│  PCIe 4.0      64 GB/s        高          单机多卡（消费级）              │
│  PCIe 5.0      128 GB/s       高          单机多卡                       │
│  NVLink 3.0    600 GB/s       低          单机多卡（数据中心）            │
│  NVLink 4.0    900 GB/s       低          单机多卡（H100）               │
│  NVLink 5.0    1.8 TB/s       低          单机多卡（B200）               │
│  NVSwitch      全带宽         低          8卡全互联（DGX）               │
│  InfiniBand    400 Gb/s       中          多机互联                       │
│  RoCE          200 Gb/s       中          多机互联（以太网）              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 性能差异可视化

```
带宽对比 (GB/s):
PCIe 4.0   ████░░░░░░░░░░░░░░░░░░░░░░░░░░░░  64
PCIe 5.0   ████████░░░░░░░░░░░░░░░░░░░░░░░░  128
NVLink 3.0 █████████████████████████░░░░░░░  600
NVLink 4.0 █████████████████████████████████░ 900
NVLink 5.0 ██████████████████████████████████ 1,800
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

### PCIe 拓扑示例

```
                    典型 PCIe 拓扑
    ┌─────────────────────────────────────────┐
    │                   CPU                    │
    │              ┌─────┴─────┐               │
    │              │           │               │
    │         ┌────▼────┐ ┌────▼────┐         │
    │         │PCIe Root│ │PCIe Root│         │
    │         │Complex 0│ │Complex 1│         │
    │         └────┬────┘ └────┬────┘         │
    │              │           │               │
    │         ┌────┼────┐ ┌────┼────┐         │
    │         ▼    ▼    ▼ ▼    ▼    ▼         │
    │       GPU0 GPU1 GPU2 GPU3 GPU4 GPU5      │
    │                                          │
    │   问题: GPU0 与 GPU3 通信需经过 CPU       │
    │         延迟高，带宽有限                   │
    └─────────────────────────────────────────┘
```

### PCIe P2P 通信

```python
import torch

# 检查 P2P 访问能力
def check_p2p():
    n_gpus = torch.cuda.device_count()
    print(f"GPU 数量: {n_gpus}")
    
    for i in range(n_gpus):
        for j in range(n_gpus):
            if i != j:
                can_access = torch.cuda.can_device_access_peer(i, j)
                print(f"GPU{i} → GPU{j}: {'✓' if can_access else '✗'}")

check_p2p()
```

---

## NVLink 详解

### NVLink 代际演进

| 版本 | 引入架构 | 链路带宽 | 最大链路数 | 总带宽/GPU |
|------|----------|---------|-----------|-----------|
| NVLink 1.0 | Pascal | 40 GB/s | 4 | 160 GB/s |
| NVLink 2.0 | Volta | 50 GB/s | 6 | 300 GB/s |
| NVLink 3.0 | Ampere | 50 GB/s | 12 | 600 GB/s |
| NVLink 4.0 | Hopper | 50 GB/s | 18 | 900 GB/s |
| NVLink 5.0 | Blackwell | 100 GB/s | 18 | 1,800 GB/s |

### NVLink vs PCIe 性能

```python
import torch
import time

def nvlink_vs_pcie_benchmark():
    """
    对比 NVLink 和 PCIe 的数据传输性能
    """
    size_gb = 1.0
    num_elements = int(size_gb * 1024**3 / 4)  # float32
    
    # GPU 0 上的数据
    data = torch.randn(num_elements, device='cuda:0')
    
    # GPU 间传输
    for target_gpu in range(1, torch.cuda.device_count()):
        torch.cuda.synchronize()
        start = time.time()
        
        for _ in range(10):
            data_copy = data.to(f'cuda:{target_gpu}')
            torch.cuda.synchronize()
        
        elapsed = time.time() - start
        bandwidth = size_gb * 10 / elapsed
        
        print(f"GPU0 → GPU{target_gpu}: {bandwidth:.1f} GB/s")

nvlink_vs_pcie_benchmark()
```

---

## NVSwitch 架构

### DGX NVLink 拓扑

```
┌─────────────────────────────────────────────────────────────┐
│              DGX H100 NVLink 拓扑 (8 GPU)                    │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   NVSwitch (全互联)                                          │
│                                                             │
│         ┌─────────────────────────────────────┐            │
│         │            NVSwitch ×4               │            │
│         └──┬────┬────┬────┬────┬────┬────┬──┘            │
│            │    │    │    │    │    │    │                 │
│         ┌──▼──┬─▼──┬─▼──┬─▼──┬─▼──┬─▼──┬─▼──┬────┐       │
│         │GPU0│GPU1│GPU2│GPU3│GPU4│GPU5│GPU6│GPU7│         │
│         └────┴────┴────┴────┴────┴────┴────┴────┘         │
│                                                             │
│   每个 GPU 到任意其他 GPU: 900 GB/s                          │
│   总互联带宽: 3.6 TB/s/GPU                                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### NVSwitch 特点

| 特性 | 说明 |
|------|------|
| 全互联 | 任意 GPU 对之间等带宽 |
| 低延迟 | 比 PCIe 低一个数量级 |
| 统一内存 | 支持跨 GPU 统一寻址 |
| 可扩展 | 支持多节点 NVLink 连接 |

---

## InfiniBand 多机互联

### InfiniBand 规格

| 版本 | 信号速率 | x4 链路带宽 | 典型应用 |
|------|----------|------------|----------|
| EDR | 25 Gb/s | 100 Gb/s | 旧集群 |
| HDR | 50 Gb/s | 200 Gb/s | 主流集群 |
| NDR | 100 Gb/s | 400 Gb/s | 新建集群 |
| XDR | 200 Gb/s | 800 Gb/s | 未来 |

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
│   │       │        │      │       │        │               │
│   │    NVSwitch    │      │    NVSwitch    │               │
│   │       │        │      │       │        │               │
│   │   ┌───┴───┐    │      │   ┌───┴───┐    │               │
│   │   │  NIC  │────┼──IB──┼───│  NIC  │    │               │
│   │   └───────┘    │      │   └───────┘    │               │
│   └────────────────┘      └────────────────┘               │
│                                                             │
│   节点内: NVLink (900 GB/s)                                  │
│   节点间: InfiniBand NDR (400 Gb/s = 50 GB/s)               │
│                                                             │
│   优化: GPUDirect RDMA 绕过 CPU，GPU 直接通信                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### GPUDirect 技术

```
GPUDirect 技术栈:

1. GPUDirect P2P
   - 同一节点内 GPU 间直接通信
   - 绕过 CPU 和系统内存

2. GPUDirect RDMA
   - GPU 直接与网卡通信
   - 绕过 CPU，降低延迟

3. GPUDirect Storage
   - GPU 直接与存储设备通信
   - 加速数据加载
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
| 预算有限多机 | RoCE | 使用现有以太网 |

### 成本考量

```
成本从低到高:
PCIe < RoCE < InfiniBand EDR < HDR < NDR

性能从低到高:
PCIe < RoCE < InfiniBand < NVLink

性价比建议:
- 开发/实验: PCIe
- 生产训练: NVLink + InfiniBand
```

---

## 小结

- **PCIe**：通用标准，带宽有限，适合消费级
- **NVLink**：NVIDIA 专有，高带宽低延迟，适合多卡训练
- **NVSwitch**：实现多卡全互联，DGX 系统标配
- **InfiniBand**：多机高性能互联首选
- **选型原则**：根据规模、预算、性能需求综合考虑

---

*下一篇：[08-hardware-selection.md](08-hardware-selection.md) - 硬件选型指南*
