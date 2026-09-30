# NVIDIA GPU 架构详解

> 深入理解 GPU 的层次结构、SM 架构和 Warp 执行模型。

## 目录

- [GPU 层次结构](#gpu-层次结构)
- [SM 架构详解](#sm-架构详解)
- [Warp 执行模型](#warp-执行模型)
- [执行资源管理](#执行资源管理)
- [实战练习](#实战练习)

---

## GPU 层次结构

### 生活类比：从集团到员工

```
GPU 的组织结构就像一个大型集团公司：

集团 (GPU Device)
  │
  ├── 事业部 (GPC - Graphics Processing Cluster)
  │     │
  │     ├── 部门 (TPC - Texture Processing Cluster)
  │     │     │
  │     │     └── 工厂 (SM - Streaming Multiprocessor) ← 核心！
  │     │           │
  │     │           ├── 生产线 (CUDA Cores)    → 通用计算
  │     │           ├── 专用设备 (Tensor Cores) → 矩阵运算
  │     │           ├── 仓库 (Register File)    → 最快的存储
  │     │           └── 共享车间 (Shared Memory) → 组内数据交换
  │     │
  │     └── ...
  │
  ├── 大仓库 (L2 Cache)     → 全公司共享
  └── 供应链 (HBM 显存)     → 海量但较慢的存储

关键理解：SM 才是真正干活的"工厂"
  H100 有 132 个 SM → 132 个并行运转的工厂
```

### 架构总览

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
│  │   │       ├── Register File (256KB per SM, H100)                │
│  │   │       └── Shared Memory / L1 Cache                          │
│  │   └── Raster Engine                                             │
│  ├── L2 Cache (shared across all SMs)                              │
│  ├── Memory Controllers                                            │
│  └── HBM (High Bandwidth Memory)                                   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 各层级说明

| 层级 | 说明 | H100 数量 |
|------|------|-----------|
| **GPC** | 图形处理集群，包含多个 TPC | 8 |
| **TPC** | 纹理处理集群，包含 2 个 SM | 66 |
| **SM** | 流多处理器，基本计算单元 | 132 |
| **CUDA Core** | 标量处理单元 | 16,896 |
| **Tensor Core** | 矩阵运算单元 | 528 |

### 为什么 GPU 要这样分层？

```
原因：管理海量计算单元的必要手段

H100 有 16,896 个 CUDA Core
如果让一个调度器管 16,896 个核心 → 调度开销炸裂

分层管理：
  每个 SM 管 128 个 CUDA Core（可控）
  每个 SM 有自己的调度器、缓存、寄存器
  SM 之间完全独立运行 → 天然并行

类比：军队编制
  一个连长管 100 人可以
  一个连长管 10,000 人不行 → 需要营、团、旅逐级管理
```

---

## SM 架构详解

### H100 SM 结构

```
┌─────────────────────────────────────────────────────────────┐
│                    H100 SM 架构                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              Warp Schedulers (×4)                    │   │
│  │     每周期调度 4 个 warp，每个 warp 32 线程          │   │
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

### SM 组件深入理解

| 组件 | 功能 | H100 规格 | 类比 |
|------|------|-----------|------|
| **Warp Scheduler** | 调度 warp 执行 | 4 个/SM | 车间主任 |
| **FP32 Cores** | 单精度浮点运算 | 128 个/SM | 通用工人 |
| **INT32 Cores** | 整数运算 | 64 个/SM | 搬运工 |
| **Tensor Core** | 矩阵乘累加 | 4 个/SM | 自动化流水线 |
| **LD/ST Unit** | 加载/存储单元 | 32 个/SM | 叉车搬运 |
| **SFU** | 特殊函数 (sin, cos) | 16 个/SM | 专业技师 |
| **Register File** | 寄存器文件 | 256 KB/SM | 工人口袋 |
| **Shared Memory** | 共享内存 | 最大 228 KB/SM | 车间工作台 |

### 理解 Tensor Core vs CUDA Core

```
打个比方：计算 4×4 矩阵乘法

CUDA Core 方式（逐个元素计算）：
  C[0][0] = A[0][0]*B[0][0] + A[0][1]*B[1][0] + A[0][2]*B[2][0] + A[0][3]*B[3][0]
  C[0][1] = ...
  ...
  总共：4×4×4 = 64 次乘加
  需要：64 个 CUDA Core 各 1 周期，或 1 个 CUDA Core 64 周期

Tensor Core 方式（整块计算）：
  D[4×4] = A[4×4] × B[4×4] + C[4×4]
  一步到位！
  需要：1 个 Tensor Core 1 周期

所以每个 SM 虽然只有 4 个 Tensor Core，
但它们处理矩阵乘法的效率远超 128 个 CUDA Core
```

---

## Warp 执行模型

### SIMT 执行模型

```
SIMT = Single Instruction, Multiple Threads
"一声令下，万众同行"

类比：广播体操
  教练喊：第一节伸展运动！
  1000 个学生同时做相同动作，但面向不同方向（不同数据）
  效率极高——教练只需要喊一次指令

一个 Warp = 32 个线程，必须执行相同的指令

  ┌──────────────────────────────────────────────────────┐
  │  Thread 0  │ Thread 1  │ ... │ Thread 30 │ Thread 31 │
  │    ▼       │    ▼      │     │     ▼     │     ▼     │
  │ Data[0]    │ Data[1]   │     │ Data[30]  │ Data[31]  │
  │    ▼       │    ▼      │     │     ▼     │     ▼     │
  │ [同一指令] │ [同一指令] │     │ [同一指令] │ [同一指令] │
  └──────────────────────────────────────────────────────┘

为什么是 32？
  这是 NVIDIA 在"并行度"和"硬件成本"之间的平衡点
  太少（8）：并行度不够
  太多（128）：分支分歧代价太大
  32 是实践中最佳的 sweet spot
```

### Warp Divergence（分支分歧）——最常见的性能陷阱

```
问题：如果 Warp 内的 32 个线程需要走不同的代码路径怎么办？

答案：串行化！两条路径都要执行，只是部分线程"空转"

类比：广播体操时教练说"男生做俯卧撑，女生做仰卧起坐"
  → 男生先做，女生站着等
  → 女生再做，男生站着等
  → 时间变成了 2 倍！
```

```python
# 理想情况：所有线程走同一分支
if condition:  # 32 线程都满足
    do_something()

# 糟糕情况：Warp Divergence
if thread_id % 2 == 0:  # 16 线程满足
    do_A()              # 先执行，另 16 线程空转
else:                   # 另 16 线程满足
    do_B()              # 后执行，前 16 线程空转
```

```
性能影响量化：

无分歧:  32/32 线程活跃 → 利用率 100%
│████████████████████████████████│  1 周期完成

2 路分歧: 16/32 + 16/32 → 利用率 50%
│████████████████                │  周期 1
│                ████████████████│  周期 2

最坏情况 (32 路分歧): 每条路径只有 1 个线程活跃 → 利用率 3.1%
实际退化为串行执行！

优化策略：
1. 让同一 Warp 内的线程走相同路径
2. 按条件值对线程重新排序
3. 使用 select/min/max 等无分支操作代替 if/else
```

### Warp 调度：如何隐藏内存延迟

```
关键洞见：GPU 不是靠缓存隐藏延迟，而是靠"大量 Warp 轮流执行"

一个 SM 上同时有很多 Warp 处于"就绪"状态

Warp A: 计算 → 等内存(500周期) → 计算
Warp B:          计算 → 等内存     → 计算
Warp C:                 计算 → 等   → 计算
Warp D:                        计算 → 计算
...

调度器：
  Warp A 等内存？切到 Warp B
  Warp B 等内存？切到 Warp C
  ...
  切换是零开销的！（每个 Warp 有独立寄存器，不需保存/恢复状态）

这就是为什么 GPU 需要"高占用率"：
  活跃 Warp 越多 → 可切换的对象越多 → 内存延迟越容易被隐藏
  占用率太低 → 所有 Warp 都在等内存 → GPU 空闲
```

---

## 执行资源管理

### 占用率 (Occupancy)

占用率 = 实际活跃 warps / SM 最大支持 warps

```
H100 每个 SM 最多支持 64 个 warp = 2048 个线程

如果你的 kernel 只能在 SM 上放 16 个 warp:
  占用率 = 16/64 = 25%  → 可能不够隐藏内存延迟

如果能放 48 个 warp:
  占用率 = 48/64 = 75%  → 通常足够好

目标：至少 50% 占用率
```

### 什么限制了占用率？——三大资源瓶颈

```
每个 SM 的资源是固定的，所有活跃 Block 共享这些资源：

资源 1: 寄存器 (Register File)
  H100: 每 SM 65,536 个 32-bit 寄存器
  如果你的 kernel 每线程用 128 个寄存器:
    → 最多 65536/128 = 512 个线程 = 16 warps → 占用率 25%
  优化：减少每线程寄存器用量（简化 kernel）

资源 2: 共享内存 (Shared Memory)
  H100: 每 SM 最大 228 KB
  如果你的 Block 用 114 KB 共享内存:
    → 每 SM 最多 2 个 Block
  优化：减少共享内存用量，或用更小的 tile

资源 3: Block 数量限制
  H100: 每 SM 最多 32 个 Block
  如果你的 Block 只有 64 个线程 (2 warps):
    → 32 个 Block × 64 线程 = 2048 → 刚好满
  但如果 Block 是 256 线程:
    → 2048/256 = 8 个 Block → 还有余量

实际占用率 = min(寄存器限制, 共享内存限制, Block 数限制)
```

### 占用率计算示例

```python
def calculate_occupancy(threads_per_block, regs_per_thread, smem_per_block):
    """估算 H100 的 SM 占用率"""
    max_threads_per_sm = 2048
    max_blocks_per_sm = 32
    max_regs_per_sm = 65536
    max_smem_per_sm = 228 * 1024  # bytes
    
    # 每 block 资源
    threads = threads_per_block
    regs = threads_per_block * regs_per_thread
    smem = smem_per_block
    
    # 计算各资源允许的 block 数
    blocks_by_threads = max_threads_per_sm // threads
    blocks_by_regs = max_regs_per_sm // regs if regs > 0 else max_blocks_per_sm
    blocks_by_smem = max_smem_per_sm // smem if smem > 0 else max_blocks_per_sm
    blocks_by_limit = max_blocks_per_sm
    
    # 实际 block 数取最小值
    actual_blocks = min(blocks_by_threads, blocks_by_regs, 
                       blocks_by_smem, blocks_by_limit)
    
    # 占用率
    actual_threads = actual_blocks * threads_per_block
    occupancy = actual_threads / max_threads_per_sm * 100
    
    bottleneck = "threads"
    if actual_blocks == blocks_by_regs: bottleneck = "registers"
    if actual_blocks == blocks_by_smem: bottleneck = "shared memory"
    
    print(f"每 SM blocks: {actual_blocks}")
    print(f"每 SM 线程: {actual_threads}")
    print(f"占用率: {occupancy:.1f}%")
    print(f"瓶颈: {bottleneck}")
    
    return occupancy

# 常见配置对比
print("=== 配置 A: 256 线程, 32 寄存器/线程, 4KB 共享内存 ===")
calculate_occupancy(256, 32, 4096)
print()
print("=== 配置 B: 256 线程, 128 寄存器/线程, 48KB 共享内存 ===")
calculate_occupancy(256, 128, 48*1024)
```

---

## 实战练习

### 练习 1：查询 GPU 架构信息

```python
import torch

def explore_gpu_architecture():
    if not torch.cuda.is_available():
        print("CUDA 不可用")
        return
    
    props = torch.cuda.get_device_properties(0)
    
    print(f"GPU: {props.name}")
    print(f"计算能力: {props.major}.{props.minor}")
    print(f"SM 数量: {props.multi_processor_count}")
    print(f"每 SM 最大线程: {props.max_threads_per_multi_processor}")
    print(f"每 block 最大线程: {props.max_threads_per_block}")
    print(f"Warp 大小: {props.warp_size}")
    print(f"总显存: {props.total_memory / 1024**3:.1f} GB")
    print(f"每 SM 共享内存: {props.max_shared_memory_per_multiprocessor / 1024:.0f} KB")
    
    # 架构识别（需要结合 major 和 minor 版本号）
    cc = (props.major, props.minor)
    arch_names = {
        (7, 0): "Volta", (7, 5): "Turing",
        (8, 0): "Ampere", (8, 6): "Ampere", (8, 9): "Ada Lovelace",
        (9, 0): "Hopper", (10, 0): "Blackwell",
    }
    arch = arch_names.get(cc, f"Unknown (CC {props.major}.{props.minor})")
    print(f"架构: {arch}")
    
    # 估算 CUDA Cores
    cuda_cores_per_sm = {
        (7, 0): 64, (7, 5): 64,
        (8, 0): 64, (8, 6): 128, (8, 9): 128,
        (9, 0): 128, (10, 0): 128,
    }
    cores = cuda_cores_per_sm.get(cc, 64) * props.multi_processor_count
    print(f"估算 CUDA Cores: {cores}")
    
    # 最大占用率
    max_warps = props.max_threads_per_multi_processor // props.warp_size
    print(f"每 SM 最大 Warps: {max_warps}")

explore_gpu_architecture()
```

### 练习 2：Warp Divergence 性能影响

```python
import torch
import time

def divergence_benchmark():
    """演示分支分歧对性能的影响"""
    n = 100_000_000
    x = torch.randn(n, device='cuda')
    
    # 无分歧：所有元素相同操作
    torch.cuda.synchronize()
    start = time.time()
    for _ in range(100):
        y = torch.relu(x)  # 统一操作
    torch.cuda.synchronize()
    no_divergence = time.time() - start
    
    # 有分歧：不同元素不同操作
    torch.cuda.synchronize()
    start = time.time()
    for _ in range(100):
        y = torch.where(x > 0, x, x * 0.01)  # 条件操作
    torch.cuda.synchronize()
    with_divergence = time.time() - start
    
    print(f"无分歧 (ReLU): {no_divergence:.3f}s")
    print(f"有分歧 (where): {with_divergence:.3f}s")
    print(f"开销增加: {with_divergence/no_divergence:.2f}x")

divergence_benchmark()
```

---

## 小结

```
GPU 架构核心知识点：

1. 层次结构: Device → GPC → TPC → SM → Cores
   SM 是核心计算单元（"工厂"），GPU 的性能 ≈ SM 数量 × 每 SM 能力

2. Warp 是执行单位: 32 线程执行相同指令（SIMT）
   分支分歧会导致串行化 → 性能大幅下降

3. 延迟隐藏: GPU 靠大量 Warp 轮流执行来掩盖内存延迟
   不是靠缓存，而是靠"人多力量大"

4. 占用率: 寄存器、共享内存、Block 数三重限制
   目标 > 50%，瓶颈分析是 CUDA 优化的第一步
```

---

*下一篇：[04-cuda-programming.md](04-cuda-programming.md) - CUDA 编程模型*

---

## 参考资料与引用

1. **NVIDIA.** *NVIDIA GPU Architecture Whitepapers.* — 各代架构白皮书合集  
   https://developer.nvidia.com/cuda-toolkit-archive

2. **NVIDIA.** *Streaming Multiprocessor (SM) Architecture.*  
   https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#hardware-implementation

3. **Jia, Z., et al. (2019).** *Dissecting the NVIDIA Volta GPU Architecture via Microbenchmarking.* — SM 内部结构分析  
   https://arxiv.org/abs/1804.06826

4. **NVIDIA.** *A100 GPU Product Specifications.*  
   https://www.nvidia.com/en-us/data-center/a100/
