# AI 网络基础设施

> 网络是大规模 AI 训练的"血管系统"——GPU 再强，网络不通，分布式训练就是一盘散沙。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [10-ai-networking/](./10-ai-networking/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | AI 网络基础 | [01-networking-fundamentals.md](./10-ai-networking/01-networking-fundamentals.md) |
> | RDMA 深入 | [02-rdma-deep-dive.md](./10-ai-networking/02-rdma-deep-dive.md) |
> | 网络拓扑设计 | [03-network-topology.md](./10-ai-networking/03-network-topology.md) |
> | GPUDirect 技术族 | [04-gpudirect-technologies.md](./10-ai-networking/04-gpudirect-technologies.md) |
> | 网络故障排查 | [05-network-troubleshooting.md](./10-ai-networking/05-network-troubleshooting.md) |
> | 网络规划与建设 | [06-network-planning.md](./10-ai-networking/06-network-planning.md) |

---

## 目录

- [为什么网络是 AI 训练的瓶颈](#为什么网络是-ai-训练的瓶颈)
- [AI 网络技术栈概览](#ai-网络技术栈概览)

---

## 为什么网络是 AI 训练的瓶颈

```
分布式训练每个 step 的通信量:

  模型: 70B 参数，256 GPU，数据并行
  AllReduce 通信量: 70B × 2 bytes × 2 = 280 GB/step
  Step 时间目标: < 1 秒
  → 所需网络带宽: 280 GB/s

  如果用普通以太网 (25 Gbps):
    单链路: 3.125 GB/s
    通信时间: 280 / 3.125 ≈ 90 秒 → 不可接受

  使用 InfiniBand NDR (400 Gbps):
    单链路: 50 GB/s
    多链路聚合 + 拓扑优化 → 实际可用 ~200 GB/s
    通信时间: < 2 秒 → 可接受
```

---

## AI 网络技术栈概览

```
┌─────────────────────────────────────────────────────────────────┐
│                   AI 网络技术栈                                   │
├─────────────────────────────────────────────────────────────────┤
│  通信库     NCCL / RCCL / Gloo / MPI                            │
│  传输协议    RDMA (InfiniBand / RoCE v2) / TCP/IP               │
│  直通技术    GPUDirect RDMA / GPUDirect Storage / NVLink         │
│  网络拓扑    Fat-tree / Rail-optimized / Dragonfly               │
│  网络设备    InfiniBand 交换机 / RoCE 交换机 / SmartNIC          │
│  物理层     光纤 / DAC 铜缆 / AOC 有源光缆                      │
└─────────────────────────────────────────────────────────────────┘
```

---

## 参考资料与引用

> 详细引用请参见各子文件。以下为本章核心参考：

1. InfiniBand Trade Association (IBTA). *InfiniBand Architecture Specification*. https://www.infinibandta.org/
2. NVIDIA Networking Documentation. https://docs.nvidia.com/networking/
3. NCCL Documentation. NVIDIA. https://docs.nvidia.com/deeplearning/nccl/
4. Al-Fares, M., et al. (2008). *A Scalable, Commodity Data Center Network Architecture*. SIGCOMM 2008. https://doi.org/10.1145/1402958.1402967

---

*上一篇：[09-ai-storage.md](09-ai-storage.md)* | *下一篇：[11-ai-safety-alignment.md](11-ai-safety-alignment.md)*
