# GPUDirect 技术族

> GPUDirect 让 GPU 直接与网络和存储设备通信，绕过 CPU——消除数据传输中的中间人，是高性能 AI 基建的关键加速技术。

## 目录

- [GPUDirect 技术概览](#gpudirect-技术概览)
- [GPUDirect RDMA](#gpudirect-rdma)
- [GPUDirect Storage](#gpudirect-storage)
- [GPUDirect Peer](#gpudirect-peer)
- [NVLink 与网络的协同](#nvlink-与网络的协同)
- [配置与验证](#配置与验证)
- [延伸阅读](#延伸阅读)

---

## GPUDirect 技术概览

```
┌─────────────────────────────────────────────────────────────────┐
│                GPUDirect 技术族                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  GPUDirect Peer (P2P):                                           │
│    GPU ←→ GPU (同一节点内，通过 PCIe/NVLink)                     │
│    用途: 节点内 GPU 间直接数据传输                                │
│                                                                 │
│  GPUDirect RDMA (GDR):                                           │
│    GPU ←→ NIC/HCA (绕过 CPU 和系统内存)                          │
│    用途: 跨节点 GPU 直接通信                                     │
│                                                                 │
│  GPUDirect Storage (GDS):                                        │
│    GPU ←→ NVMe SSD (绕过 CPU 和系统内存)                         │
│    用途: GPU 直接读写存储设备                                    │
│                                                                 │
│  传统路径 vs GPUDirect:                                          │
│                                                                 │
│  传统: GPU → PCIe → CPU内存 → PCIe → NIC/SSD                    │
│        (2 次 PCIe 传输 + CPU 参与)                               │
│                                                                 │
│  GDR:  GPU → PCIe → NIC  (1 次传输，CPU 不参与)                  │
│  GDS:  GPU → PCIe → NVMe (1 次传输，CPU 不参与)                  │
│                                                                 │
│  性能提升: 延迟减少 30-50%, 吞吐提升 20-40%, CPU 释放 70%+       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## GPUDirect RDMA

### 工作原理

```
GPUDirect RDMA — 跨节点 GPU 直接通信:

  节点 A                          节点 B
  ┌──────────────┐              ┌──────────────┐
  │  ┌────────┐  │              │  ┌────────┐  │
  │  │  GPU   │  │              │  │  GPU   │  │
  │  │ (显存) │  │              │  │ (显存) │  │
  │  └───┬────┘  │              │  └───┬────┘  │
  │      │ PCIe  │              │      │ PCIe  │
  │  ┌───▼────┐  │   RDMA      │  ┌───▼────┐  │
  │  │  HCA/  │──┼────────────→│  │  HCA/  │  │
  │  │  NIC   │  │  网络        │  │  NIC   │  │
  │  └────────┘  │              │  └────────┘  │
  │              │              │              │
  │  CPU 不参与! │              │  CPU 不参与! │
  └──────────────┘              └──────────────┘

  GPU 显存 → PCIe → HCA → 网络 → HCA → PCIe → GPU 显存
  整个过程 CPU 和系统内存不参与

  要求:
    GPU 和 HCA 在同一 PCIe Root Complex 下
    → BAR1 映射（GPU 显存暴露给 PCIe 总线）
    → nvidia-peermem 内核模块

  NCCL 自动使用 GDR（如果可用）
```

### 验证 GDR

```bash
# 验证 GPUDirect RDMA 是否可用

# 1. 检查 nvidia-peermem 模块
lsmod | grep nvidia_peermem
# 如果没有: modprobe nvidia-peermem

# 2. 检查 GPU 和 NIC 的 PCIe 拓扑
nvidia-smi topo -m
# 期望: GPU 和 mlx5_X 显示 PIX/PHB (同一 PCIe Switch/Bridge)

# 3. CUDA-aware RDMA 测试
# 使用 perftest 的 CUDA 模式
ib_write_bw --use_cuda=0 -d mlx5_0 -s 65536 <server>
# 应看到接近线速的带宽

# 4. NCCL 测试
NCCL_DEBUG=INFO nccl-tests/build/all_reduce_perf -b 1M -e 1G -g 1
# 日志中应包含 "NET/IB : Using GPUDirect RDMA"

# 5. 检查 NCCL GDR 级别
echo $NCCL_NET_GDR_LEVEL
# 5 = 跨 PCIe switch 也启用 GDR
# 推荐设为 5
```

---

## GPUDirect Storage

```
GPUDirect Storage — GPU 直接读写 NVMe:

  场景: Checkpoint 保存/加载、训练数据读取

  传统路径:
    保存: GPU显存 → CPU内存 → 文件系统 → NVMe  (3步)
    加载: NVMe → 文件系统 → CPU内存 → GPU显存  (3步)

  GDS 路径:
    保存: GPU显存 → NVMe  (1步, DMA直传)
    加载: NVMe → GPU显存  (1步, DMA直传)

  性能对比:
    Checkpoint 保存 (70B 模型, 140GB):
      传统: ~25 秒 (CPU 拷贝 + 文件系统开销)
      GDS:  ~12 秒 (直接 DMA)
      提升: ~2x

  配置:
    1. 安装 GDS 驱动: apt install nvidia-gds
    2. 配置 cuFile: /etc/cufile.json
    3. 应用代码使用 cuFile API

  兼容的文件系统: ext4, XFS (本地)
  实验性支持: Lustre, GPFS, NFS
```

---

## GPUDirect Peer

```
GPUDirect Peer (P2P) — 节点内 GPU 直接通信:

  同一节点内的 GPU 可以直接通过 PCIe/NVLink 交换数据
  不经过 CPU 内存

  NVLink P2P:
    GPU0 ←──NVLink──→ GPU1   (900 GB/s, H100)
    延迟: ~0.1-0.5 μs
    最快的 GPU 间通信方式

  PCIe P2P:
    GPU0 ←──PCIe──→ GPU1     (64 GB/s, PCIe Gen5 x16)
    需要 GPU 在同一 PCIe Switch 下
    比 NVLink 慢很多，但比经过 CPU 快

  验证:
    nvidia-smi topo -m
    # NV# = NVLink 连接 (# 表示链路数)
    # PIX = 同一 PCIe Switch
    # PHB = 同一 PCIe Host Bridge
    # SYS = 跨 NUMA (最慢)
```

---

## NVLink 与网络的协同

```
NVLink 与网络在分布式训练中的协同:

  DGX H100 节点内部:
  ┌───────────────────────────────────────┐
  │  GPU0 ─NVLink─ GPU1 ─NVLink─ GPU2    │
  │   │              │              │     │
  │  NVLink        NVLink        NVLink   │
  │   │              │              │     │
  │  GPU3 ─NVLink─ GPU4 ─NVLink─ GPU5    │
  │   │              │              │     │
  │  NVLink        NVLink        NVLink   │
  │   │              │              │     │
  │  GPU6 ─NVLink─ GPU7               │  │
  │                                       │
  │  NVLink 带宽: 900 GB/s (全双工)       │
  │  → 张量并行 (TP) 放在节点内              │
  └──────────┬────────────────────────────┘
             │ 8× 400G InfiniBand (NDR)
             │ 总带宽: 400 GB/s
             ▼
  ┌──────────────────────────────────────┐
  │  网络 (InfiniBand/RoCE)              │
  │  → 数据并行 (DP) / 流水线并行 (PP)   │
  │    放在节点间                         │
  └──────────────────────────────────────┘

  最优并行策略映射:
    TP (张量并行): 节点内 NVLink (通信量大，需极高带宽)
    PP (流水线并行): 跨节点 (通信量较小，需低延迟)
    DP (数据并行): 跨节点 (通信量大，但可重叠)
    EP (专家并行): 跨节点 (通信模式复杂)

  NVSwitch (H100/B200):
    全连接 NVLink 交换（节点内任意 GPU 对 900 GB/s）
    vs 旧架构: 部分 GPU 对之间需要多跳 NVLink
```

---

## 配置与验证

```bash
# GPUDirect 全家族验证脚本

echo "=== 1. GPU 拓扑 ==="
nvidia-smi topo -m

echo "=== 2. NVLink 状态 ==="
nvidia-smi nvlink -s

echo "=== 3. nvidia-peermem (GDR) ==="
lsmod | grep nvidia_peermem
if [ $? -ne 0 ]; then
    echo "Loading nvidia-peermem..."
    modprobe nvidia-peermem
fi

echo "=== 4. P2P 带宽测试 ==="
# CUDA Samples 中的 p2pBandwidthLatencyTest
# ./p2pBandwidthLatencyTest

echo "=== 5. GDS 状态 ==="
if command -v gdscheck &> /dev/null; then
    gdscheck -p  # 检查 GDS 支持
fi

echo "=== 6. RDMA 设备 ==="
ibv_devinfo | grep -E "hca_id|port:|state:|phys_state:|link_layer:|rate:"

echo "=== 7. PCIe 拓扑 (GPU & NIC) ==="
lspci | grep -E "NVIDIA|Mellanox|ConnectX"
```

---

## 延伸阅读

- [NVIDIA GPUDirect Technologies](https://developer.nvidia.com/gpudirect)
- [GPUDirect RDMA Documentation](https://docs.nvidia.com/cuda/gpudirect-rdma/)
- [GPUDirect Storage Developer Guide](https://docs.nvidia.com/gpudirect-storage/)
- [NVLink and NVSwitch](https://www.nvidia.com/en-us/data-center/nvlink/)

---

*上一篇：[03-network-topology.md](03-network-topology.md)* | *下一篇：[05-network-troubleshooting.md](05-network-troubleshooting.md)*

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **NVIDIA.** *GPUDirect RDMA.*  
   https://docs.nvidia.com/cuda/gpudirect-rdma/

2. **NVIDIA.** *GPUDirect Storage.*  
   https://developer.nvidia.com/gpudirect-storage

3. **NVIDIA.** *GPUDirect Peer-to-Peer.*  
   https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#peer-to-peer-memory-access
