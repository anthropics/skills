# GPU/硬件基础详解

> GPU 是 AI 计算的核心引擎，理解硬件架构才能写出高效的 AI 代码。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [01-gpu-hardware/](./01-gpu-hardware/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | 为什么需要 GPU | [01-why-gpu.md](./01-gpu-hardware/01-why-gpu.md) |
> | GPU 架构演进 | [02-architecture-evolution.md](./01-gpu-hardware/02-architecture-evolution.md) |
> | NVIDIA GPU 架构详解 | [03-nvidia-architecture.md](./01-gpu-hardware/03-nvidia-architecture.md) |
> | CUDA 编程模型 | [04-cuda-programming.md](./01-gpu-hardware/04-cuda-programming.md) |
> | 内存层次结构 | [05-memory-hierarchy.md](./01-gpu-hardware/05-memory-hierarchy.md) |
> | Tensor Core 详解 | [06-tensor-core.md](./01-gpu-hardware/06-tensor-core.md) |
> | 多卡互联技术 | [07-multi-gpu-interconnect.md](./01-gpu-hardware/07-multi-gpu-interconnect.md) |
> | 硬件选型指南 | [08-hardware-selection.md](./01-gpu-hardware/08-hardware-selection.md) |

---

## 目录

- [为什么需要 GPU](#为什么需要-gpu)
- [GPU 架构演进](#gpu-架构演进)
- [NVIDIA GPU 架构详解](#nvidia-gpu-架构详解)
- [CUDA 编程模型](#cuda-编程模型)
- [内存层次结构](#内存层次结构)
- [Tensor Core 详解](#tensor-core-详解)
- [多卡互联技术](#多卡互联技术)
- [硬件选型指南](#硬件选型指南)
- [实战练习](#实战练习)

---

## 为什么需要 GPU

### CPU vs GPU：设计哲学的差异

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        CPU vs GPU 架构对比                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   CPU (延迟优化)                    GPU (吞吐优化)                        │
│   ┌─────────────────┐              ┌─────────────────────────────────┐  │
│   │ ┌───┐ ┌───┐     │              │ ┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐ │  │
│   │ │Core│ │Core│   │              │ └─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘ │  │
│   │ └───┘ └───┘     │              │ ┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐ │  │
│   │ ┌───┐ ┌───┐     │              │ └─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘ │  │
│   │ │Core│ │Core│   │              │ ┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐ │  │
│   │ └───┘ └───┘     │              │ └─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘ │  │
│   │   Large Cache   │              │        ... thousands more ...   │  │
│   └─────────────────┘              └─────────────────────────────────┘  │
│                                                                         │
│   4-64 复杂核心                     数千个简单核心                         │
│   优化单线程性能                    优化大规模并行                         │
│   低延迟，串行任务                  高吞吐，数据并行                        │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 为什么 AI 需要 GPU

| 特性 | CPU | GPU | AI 需求匹配度 |
|------|-----|-----|---------------|
| **并行度** | 数十线程 | 数千线程 | ✅ 矩阵运算天然并行 |
| **内存带宽** | ~100 GB/s | ~3 TB/s (HBM) | ✅ 大量数据搬运 |
| **矩阵计算** | 通用指令 | Tensor Core 专用 | ✅ 神经网络核心操作 |
| **能效比** | 低 | 高（针对并行） | ✅ 大规模计算成本 |

**关键洞察**：深度学习本质是**大规模矩阵运算**，而 GPU 正是为此设计的。

---

## GPU 架构演进

### NVIDIA 架构时间线

```
2017 ──── Volta (V100) ────────── 首次引入 Tensor Core
   │
2020 ──── Ampere (A100) ────────── 第三代 Tensor Core，支持 TF32/BF16
   │
2022 ──── Hopper (H100) ────────── 第四代 Tensor Core，Transformer Engine
   │
2024 ──── Blackwell (B100/B200) ── 第五代，FP4 支持，更强 NVLink
```

### 关键规格对比

| 指标 | V100 | A100 | H100 | B200 |
|------|------|------|------|------|
| **架构** | Volta | Ampere | Hopper | Blackwell |
| **FP16 TFLOPS** | 125 | 312 | 989 | 2,250 |
| **FP8 TFLOPS** | - | - | 1,979 | 4,500 |
| **内存** | 32GB HBM2 | 80GB HBM2e | 80GB HBM3 | 192GB HBM3e |
| **带宽** | 900 GB/s | 2 TB/s | 3.35 TB/s | 8 TB/s |
| **TDP** | 300W | 400W | 700W | 1000W |
| **互联** | NVLink 2.0 | NVLink 3.0 | NVLink 4.0 | NVLink 5.0 |

### 性能飞跃的原因

1. **Tensor Core 迭代**：专用矩阵计算单元持续优化
2. **内存带宽提升**：HBM 技术演进（HBM2 → HBM3e）
3. **互联带宽增长**：NVLink 从 300GB/s → 1.8TB/s
4. **低精度支持**：FP32 → FP16 → BF16 → FP8 → FP4

---

## NVIDIA GPU 架构详解

### 层次结构

```
┌─────────────────────────────────────────────────────────────────────┐
│                         GPU 架构层次                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  GPU Device                                                         │
│  ├── GPC (Graphics Processing Cluster) × N                         │
│  │   ├── TPC (Texture Processing Cluster) × M                      │
│  │   │   └── SM (Streaming Multiprocessor) × 2                     │
│  │   │       ├── CUDA Cores (FP32/INT32)                           │
│  │   │       ├── Tensor Cores                                      │
│  │   │       ├── Load/Store Units                                  │
│  │   │       ├── Special Function Units (SFU)                      │
│  │   │       ├── Warp Scheduler                                    │
│  │   │       ├── Register File (64KB per SM)                       │
│  │   │       └── Shared Memory / L1 Cache (configurable)           │
│  │   └── Raster Engine                                             │
│  ├── L2 Cache (shared across all SMs)                              │
│  ├── Memory Controllers                                            │
│  └── HBM (High Bandwidth Memory)                                   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### SM（Streaming Multiprocessor）详解

SM 是 GPU 的核心计算单元，以 H100 为例：

```
┌─────────────────────────────────────────────────────────────┐
│                    H100 SM 架构                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              Warp Schedulers (×4)                    │   │
│  │     每周期调度 4 个 warp，每个 warp 32 线程            │   │
│  └─────────────────────────────────────────────────────┘   │
│                          │                                  │
│  ┌───────────────────────┼───────────────────────────┐     │
│  │                       ▼                           │     │
│  │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ │     │
│  │  │ FP32 Cores  │ │ INT32 Cores │ │ Tensor Core │ │     │
│  │  │    ×128     │ │     ×64     │ │     ×4      │ │     │
│  │  └─────────────┘ └─────────────┘ └─────────────┘ │     │
│  │                   Processing Units               │     │
│  └──────────────────────────────────────────────────┘     │
│                          │                                  │
│  ┌───────────────────────┼───────────────────────────┐     │
│  │                       ▼                           │     │
│  │  ┌────────────────────────────────────────────┐  │     │
│  │  │     Register File (256 KB)                 │  │     │
│  │  └────────────────────────────────────────────┘  │     │
│  │  ┌────────────────────────────────────────────┐  │     │
│  │  │   Shared Memory / L1 Cache (256 KB)        │  │     │
│  │  │        可配置分配比例                        │  │     │
│  │  └────────────────────────────────────────────┘  │     │
│  │                   Memory Subsystem               │     │
│  └──────────────────────────────────────────────────┘     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Warp 执行模型

```python
# Warp = 32 个线程，SIMT 执行模型
# 同一 warp 中的线程执行相同指令，但处理不同数据

# 理想情况：所有线程走同一分支
if condition:  # 32 线程都满足
    do_something()

# 糟糕情况：Warp Divergence
if thread_id % 2 == 0:  # 16 线程满足
    do_A()              # 先执行
else:                   # 16 线程满足
    do_B()              # 后执行（串行化！）
```

**优化原则**：避免同一 warp 内的线程走不同分支。

---

## CUDA 编程模型

### 基本概念映射

```
┌─────────────────────────────────────────────────────────────┐
│              CUDA 编程模型 → 硬件映射                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  软件概念                    硬件对应                        │
│  ───────                    ────────                        │
│  Grid (网格)         ───→   整个 GPU                        │
│    │                                                        │
│    ├── Block (线程块) ───→   单个 SM                         │
│    │     │                                                  │
│    │     ├── Warp    ───→   32 线程的调度单位               │
│    │     │                                                  │
│    │     └── Thread  ───→   单个 CUDA Core                  │
│    │                                                        │
│  Shared Memory       ───→   SM 的 Shared Memory            │
│  Registers           ───→   SM 的 Register File            │
│  Global Memory       ───→   HBM/GDDR                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### CUDA 核函数示例

```cpp
// 向量加法示例
__global__ void vectorAdd(float *a, float *b, float *c, int n) {
    // 计算全局线程索引
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    
    if (idx < n) {
        c[idx] = a[idx] + b[idx];
    }
}

// 主机代码
int main() {
    int n = 1000000;
    float *d_a, *d_b, *d_c;
    
    // 分配设备内存
    cudaMalloc(&d_a, n * sizeof(float));
    cudaMalloc(&d_b, n * sizeof(float));
    cudaMalloc(&d_c, n * sizeof(float));
    
    // 配置执行参数
    int blockSize = 256;
    int numBlocks = (n + blockSize - 1) / blockSize;
    
    // 启动核函数
    vectorAdd<<<numBlocks, blockSize>>>(d_a, d_b, d_c, n);
    
    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);
    return 0;
}
```

### 关键优化技术

#### 1. Coalesced Memory Access（合并内存访问）

```cpp
// ✅ 好的访问模式：连续线程访问连续内存
// 一次事务读取 128 字节
c[idx] = a[idx] + b[idx];  // idx = 0,1,2,3... (coalesced)

// ❌ 坏的访问模式：跨步访问
c[idx] = a[idx * stride];  // stride > 1 (uncoalesced, 多次事务)
```

#### 2. Shared Memory 使用

```cpp
__global__ void matMul(float *A, float *B, float *C, int N) {
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];
    
    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;
    float sum = 0.0f;
    
    // 分块计算，利用 shared memory 复用数据
    for (int t = 0; t < N / TILE_SIZE; t++) {
        // 协作加载到 shared memory
        As[threadIdx.y][threadIdx.x] = A[row * N + t * TILE_SIZE + threadIdx.x];
        Bs[threadIdx.y][threadIdx.x] = B[(t * TILE_SIZE + threadIdx.y) * N + col];
        __syncthreads();
        
        // 从 shared memory 计算
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }
        __syncthreads();
    }
    
    C[row * N + col] = sum;
}
```

#### 3. 占用率优化

```cpp
// 查询设备属性
cudaDeviceProp prop;
cudaGetDeviceProperties(&prop, 0);

// 关键限制因素
// - 每 SM 最大线程数: prop.maxThreadsPerMultiProcessor
// - 每 SM 最大 block 数: prop.maxBlocksPerMultiProcessor
// - 每 SM 寄存器数: prop.regsPerMultiprocessor
// - 每 SM shared memory: prop.sharedMemPerMultiprocessor

// 占用率 = 实际 warps / SM 最大 warps
// 目标: 达到 50%+ 占用率，隐藏内存延迟
```

---

## 内存层次结构

### 内存层次金字塔

```
                    ┌─────────────┐
                    │  Registers  │  ← 最快，线程私有
                    │   ~20 TB/s  │     无延迟
                    └──────┬──────┘
                           │
                    ┌──────▼──────┐
                    │   Shared    │  ← Block 内共享
                    │   Memory    │     ~10 TB/s
                    │   L1 Cache  │     ~30 cycles
                    └──────┬──────┘
                           │
                    ┌──────▼──────┐
                    │  L2 Cache   │  ← 全 GPU 共享
                    │   ~5 TB/s   │     ~200 cycles
                    └──────┬──────┘
                           │
              ┌────────────▼────────────┐
              │    HBM (Global Mem)     │  ← 最大，最慢
              │      ~3 TB/s            │     ~500 cycles
              └────────────┬────────────┘
                           │
              ┌────────────▼────────────┐
              │   System Memory (CPU)   │  ← PCIe 带宽限制
              │      ~64 GB/s           │     ~10000 cycles
              └─────────────────────────┘
```

### HBM（High Bandwidth Memory）详解

```
┌─────────────────────────────────────────────────────────────┐
│                    HBM 架构示意                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   传统 GDDR:                                                │
│   ┌─────┐                    ┌─────────────────┐            │
│   │ GPU │ ←── PCB 走线 ──→  │  GDDR 芯片组     │            │
│   └─────┘    (长距离)        └─────────────────┘            │
│                                                             │
│   HBM:                                                      │
│   ┌─────────────────────────────────────────────┐          │
│   │              硅中介层 (Interposer)           │          │
│   │  ┌─────┐  ┌─────┐  ┌─────┐  ┌─────┐        │          │
│   │  │HBM  │  │HBM  │  │ GPU │  │HBM  │        │          │
│   │  │Stack│  │Stack│  │ Die │  │Stack│        │          │
│   │  └─────┘  └─────┘  └─────┘  └─────┘        │          │
│   │      ↑        ↑        ↑        ↑          │          │
│   │      └────────┴────────┴────────┘          │          │
│   │           Through-Silicon Vias (TSV)        │          │
│   └─────────────────────────────────────────────┘          │
│                                                             │
│   优势: 短距离、宽总线(1024-bit)、低功耗、高带宽              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 内存优化策略

| 策略 | 描述 | 适用场景 |
|------|------|----------|
| **数据复用** | 将频繁访问的数据放入 shared memory | 矩阵乘法、卷积 |
| **预取** | 提前加载下一批数据到 shared memory | 流式计算 |
| **合并访问** | 确保 warp 内线程访问连续内存 | 所有全局内存访问 |
| **避免 bank conflict** | 调整 shared memory 访问模式 | 使用 shared memory 时 |
| **使用只读缓存** | `__ldg()` 或 `const __restrict__` | 只读数据 |

---

## Tensor Core 详解

### 什么是 Tensor Core

Tensor Core 是专门为矩阵乘累加（Matrix Multiply-Accumulate, MMA）设计的硬件单元。

```
┌─────────────────────────────────────────────────────────────┐
│                 Tensor Core 操作                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   D = A × B + C                                             │
│                                                             │
│   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐    │
│   │  A      │ × │  B      │ + │  C      │ = │  D      │    │
│   │ (MxK)   │   │ (KxN)   │   │ (MxN)   │   │ (MxN)   │    │
│   │ FP16/   │   │ FP16/   │   │ FP32    │   │ FP32    │    │
│   │ BF16/   │   │ BF16/   │   │         │   │         │    │
│   │ FP8     │   │ FP8     │   │         │   │         │    │
│   └─────────┘   └─────────┘   └─────────┘   └─────────┘    │
│                                                             │
│   单次操作: 4×4×4 (Volta) → 8×8×4 (Ampere) → 16×8×16 (Hopper)│
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 数据类型支持演进

| 架构 | FP64 | FP32 | TF32 | FP16 | BF16 | FP8 | INT8 | INT4 |
|------|------|------|------|------|------|-----|------|------|
| Volta | - | - | - | ✅ | - | - | ✅ | - |
| Ampere | ✅ | - | ✅ | ✅ | ✅ | - | ✅ | ✅ |
| Hopper | ✅ | - | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |

### 使用 Tensor Core

```python
import torch

# PyTorch 自动使用 Tensor Core（当满足条件时）
# 条件: 1) CUDA GPU  2) 矩阵维度是 8 的倍数  3) 使用支持的数据类型

# 方式 1: 使用 torch.cuda.amp 自动混合精度
with torch.cuda.amp.autocast():
    output = model(input)  # 自动选择 FP16 运算

# 方式 2: 手动指定数据类型
a = torch.randn(1024, 1024, device='cuda', dtype=torch.float16)
b = torch.randn(1024, 1024, device='cuda', dtype=torch.float16)
c = torch.matmul(a, b)  # 使用 Tensor Core

# 方式 3: 使用 TF32（Ampere+）
# 默认开启，FP32 输入自动使用 TF32 加速
torch.backends.cuda.matmul.allow_tf32 = True
torch.backends.cudnn.allow_tf32 = True
```

### Transformer Engine (Hopper)

```python
# H100 引入的 Transformer Engine
# 自动管理 FP8 训练，动态选择精度

import transformer_engine.pytorch as te

# 替换标准 Linear 层
layer = te.Linear(1024, 1024, bias=True)

# FP8 自动混合精度训练
with te.fp8_autocast(enabled=True):
    output = layer(input)
```

---

## 多卡互联技术

### 互联技术对比

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
│  NVSwitch      900 GB/s       低          8卡全互联（DGX）               │
│  InfiniBand    400 Gb/s       中          多机互联                       │
│  RoCE          200 Gb/s       中          多机互联（以太网）              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### NVLink 架构

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
│         ┌──▼──┬─▼──┬─▼──┬─▼──┬─▼──┬─▼──┬─▼──┐            │
│         │GPU0│GPU1│GPU2│GPU3│GPU4│GPU5│GPU6│GPU7│         │
│         └────┴────┴────┴────┴────┴────┴────┴────┘         │
│                                                             │
│   每个 GPU 到任意其他 GPU: 900 GB/s                          │
│   总互联带宽: 3.6 TB/s/GPU × 8 = 28.8 TB/s                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### InfiniBand 多机互联

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

---

## 硬件选型指南

### 按场景选择

| 场景 | 推荐 GPU | 理由 |
|------|----------|------|
| **LLM 推理（小规模）** | RTX 4090 / L40S | 性价比高，24GB/48GB 显存够用 |
| **LLM 推理（生产）** | A100 40GB / H100 | 高带宽，Tensor Core 优化 |
| **LLM 训练（中小模型）** | A100 80GB × 8 | 显存充足，NVLink 互联 |
| **LLM 训练（大模型）** | H100 80GB × 8+ | 最强性能，Transformer Engine |
| **研究/实验** | RTX 3090/4090 | 成本低，快速迭代 |
| **边缘推理** | Jetson Orin | 低功耗，嵌入式场景 |

### 关键考量因素

```
┌─────────────────────────────────────────────────────────────┐
│                    GPU 选型决策树                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                    你的主要任务是什么？                        │
│                          │                                   │
│           ┌──────────────┼──────────────┐                   │
│           ▼              ▼              ▼                   │
│        训练           推理          研究/实验                 │
│           │              │              │                   │
│     模型多大？      延迟要求？      预算多少？                  │
│           │              │              │                   │
│   ┌───────┼───────┐  ┌──┼──┐      ┌────┼────┐             │
│   ▼       ▼       ▼  ▼     ▼      ▼         ▼             │
│ <7B    7-70B    >70B 宽松  严格   有限     充足              │
│   │       │       │   │     │      │         │             │
│   ▼       ▼       ▼   ▼     ▼      ▼         ▼             │
│ A100×1  A100×8  H100  L40S  H100  RTX4090  A100/H100       │
│ 80GB    80GB    ×8+                                        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 显存需求估算

```python
# 模型显存估算公式（训练）
def estimate_training_memory(param_count_billion, precision="fp16"):
    """
    参数量（十亿）-> 显存需求（GB）
    
    组成部分:
    - 模型参数: params × bytes_per_param
    - 梯度: params × bytes_per_param  
    - 优化器状态: params × 8 bytes (AdamW)
    - 激活值: 取决于 batch size 和序列长度
    """
    bytes_per_param = 2 if precision == "fp16" else 4
    
    # 模型 + 梯度 + 优化器 ≈ 模型参数的 16-20 倍（FP16 + AdamW）
    param_bytes = param_count_billion * 1e9 * bytes_per_param
    gradient_bytes = param_bytes
    optimizer_bytes = param_count_billion * 1e9 * 8  # AdamW: 2 states × FP32
    
    total_bytes = param_bytes + gradient_bytes + optimizer_bytes
    return total_bytes / (1024**3)  # GB

# 示例
print(f"7B 模型训练显存: ~{estimate_training_memory(7):.0f} GB")
print(f"70B 模型训练显存: ~{estimate_training_memory(70):.0f} GB")

# 输出:
# 7B 模型训练显存: ~98 GB (需要 2×A100 80GB 或 DeepSpeed ZeRO)
# 70B 模型训练显存: ~980 GB (需要多卡 + ZeRO-3)
```

---

## 实战练习

### 练习 1：GPU 信息查询

```python
# 查询 GPU 详细信息
import torch

if torch.cuda.is_available():
    device = torch.cuda.current_device()
    props = torch.cuda.get_device_properties(device)
    
    print(f"GPU: {props.name}")
    print(f"计算能力: {props.major}.{props.minor}")
    print(f"显存: {props.total_memory / 1024**3:.1f} GB")
    print(f"SM 数量: {props.multi_processor_count}")
    print(f"每 SM 最大线程: {props.max_threads_per_multi_processor}")
```

### 练习 2：内存带宽测试

```python
import torch
import time

def bandwidth_test(size_gb=1.0, dtype=torch.float32):
    """测试 GPU 内存带宽"""
    bytes_per_elem = torch.tensor([], dtype=dtype).element_size()
    num_elements = int(size_gb * 1024**3 / bytes_per_elem)
    
    # 创建张量
    a = torch.randn(num_elements, device='cuda', dtype=dtype)
    b = torch.empty_like(a)
    
    # 预热
    b.copy_(a)
    torch.cuda.synchronize()
    
    # 计时
    start = time.time()
    for _ in range(100):
        b.copy_(a)
    torch.cuda.synchronize()
    elapsed = time.time() - start
    
    # 计算带宽 (读 + 写)
    total_bytes = 2 * size_gb * 1024**3 * 100
    bandwidth_gbps = total_bytes / elapsed / 1024**3
    
    print(f"内存带宽: {bandwidth_gbps:.1f} GB/s")

bandwidth_test()
```

### 练习 3：Tensor Core 性能对比

```python
import torch
import time

def matmul_benchmark(size=4096, dtype=torch.float32, iterations=100):
    """对比不同精度的矩阵乘法性能"""
    a = torch.randn(size, size, device='cuda', dtype=dtype)
    b = torch.randn(size, size, device='cuda', dtype=dtype)
    
    # 预热
    torch.matmul(a, b)
    torch.cuda.synchronize()
    
    # 计时
    start = time.time()
    for _ in range(iterations):
        c = torch.matmul(a, b)
    torch.cuda.synchronize()
    elapsed = time.time() - start
    
    # TFLOPS = 2 * N^3 (矩阵乘法 FLOPs)
    flops = 2 * size**3 * iterations
    tflops = flops / elapsed / 1e12
    
    print(f"{str(dtype):20} - {tflops:.1f} TFLOPS")

print("矩阵乘法性能对比 (4096×4096):")
matmul_benchmark(dtype=torch.float32)
matmul_benchmark(dtype=torch.float16)
matmul_benchmark(dtype=torch.bfloat16)
```

---

## 延伸阅读

### 官方文档

- [CUDA C++ Programming Guide](https://docs.nvidia.com/cuda/cuda-c-programming-guide/)
- [NVIDIA GPU Architecture Whitepapers](https://www.nvidia.com/en-us/data-center/resources/)
- [PyTorch CUDA Semantics](https://pytorch.org/docs/stable/notes/cuda.html)

### 推荐书籍

- *Programming Massively Parallel Processors* - CUDA 编程圣经
- *CUDA by Example* - 入门实践指南

### 必读论文

- [NVIDIA Tesla V100 GPU Architecture](https://images.nvidia.com/content/volta-architecture/pdf/volta-architecture-whitepaper.pdf)
- [NVIDIA A100 Tensor Core GPU Architecture](https://www.nvidia.com/content/dam/en-zz/Solutions/Data-Center/nvidia-ampere-architecture-whitepaper.pdf)
- [NVIDIA H100 Tensor Core GPU Architecture](https://resources.nvidia.com/en-us-tensor-core)

---

*下一篇：[02-distributed-training.md](02-distributed-training.md) - 分布式训练详解*
