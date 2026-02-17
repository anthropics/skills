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

### SM 关键组件

| 组件 | 功能 | H100 规格 |
|------|------|-----------|
| **Warp Scheduler** | 调度 warp 执行 | 4 个/SM |
| **FP32 Cores** | 单精度浮点运算 | 128 个/SM |
| **INT32 Cores** | 整数运算 | 64 个/SM |
| **Tensor Core** | 矩阵乘累加 | 4 个/SM |
| **LD/ST Unit** | 加载/存储单元 | 32 个/SM |
| **SFU** | 特殊函数 (sin, cos) | 16 个/SM |
| **Register File** | 寄存器文件 | 256 KB/SM |
| **Shared Memory** | 共享内存 | 最大 228 KB/SM |

---

## Warp 执行模型

### SIMT 执行模型

```
SIMT = Single Instruction, Multiple Threads

┌─────────────────────────────────────────────────────────────┐
│                      Warp 执行模型                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  一个 Warp = 32 个线程                                       │
│                                                             │
│  ┌──────────────────────────────────────────────────────┐  │
│  │  Thread 0  │ Thread 1  │ ... │ Thread 30 │ Thread 31 │  │
│  │    ▼       │    ▼      │     │     ▼     │     ▼     │  │
│  │ Data[0]    │ Data[1]   │     │ Data[30]  │ Data[31]  │  │
│  │    ▼       │    ▼      │     │     ▼     │     ▼     │  │
│  │ [同一指令] │ [同一指令] │     │ [同一指令] │ [同一指令] │  │
│  └──────────────────────────────────────────────────────┘  │
│                                                             │
│  32 个线程执行相同指令，处理不同数据                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Warp Divergence（分支分歧）

```python
# 理想情况：所有线程走同一分支
if condition:  # 32 线程都满足
    do_something()

# 糟糕情况：Warp Divergence
if thread_id % 2 == 0:  # 16 线程满足
    do_A()              # 先执行，其他线程等待
else:                   # 16 线程满足
    do_B()              # 后执行，串行化！
```

```
┌─────────────────────────────────────────────────────────────┐
│                   Warp Divergence 影响                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  无分歧 (最优):                                              │
│  ┌────────────────────────────────────────────┐            │
│  │ All 32 threads: ████████████████████████████│ → 1 周期  │
│  └────────────────────────────────────────────┘            │
│                                                             │
│  有分歧 (串行化):                                            │
│  ┌────────────────────────────────────────────┐            │
│  │ 16 threads (if):   ████████████████        │ → 周期 1   │
│  │ 16 threads (else):                 ████████│ → 周期 2   │
│  └────────────────────────────────────────────┘            │
│                                                             │
│  性能损失: 2x (最坏情况可达 32x)                              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**优化原则**：避免同一 warp 内的线程走不同分支。

---

## 执行资源管理

### 占用率 (Occupancy)

占用率 = 实际活跃 warps / SM 最大支持 warps

```python
# 查询设备属性
import torch
props = torch.cuda.get_device_properties(0)

# 关键限制因素
print(f"每 SM 最大线程数: {props.max_threads_per_multi_processor}")
print(f"每 SM 最大 blocks: {props.max_blocks_per_multiprocessor}")  
print(f"每 SM 寄存器数: {props.regs_per_multiprocessor}")
print(f"每 SM shared memory: {props.shared_memory_per_multiprocessor}")

# 目标: 达到 50%+ 占用率，隐藏内存延迟
```

### 资源限制因素

| 限制因素 | H100 限制 | 影响 |
|----------|-----------|------|
| 每 SM 最大线程 | 2,048 | Block 大小配置 |
| 每 SM 最大 blocks | 32 | Block 数量 |
| 每线程寄存器 | 255 | Kernel 复杂度 |
| Shared Memory | 228 KB | 数据复用 |

### 占用率计算示例

```python
def calculate_occupancy(threads_per_block, regs_per_thread, smem_per_block):
    """
    估算占用率
    """
    # H100 限制
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
    
    print(f"每 SM blocks: {actual_blocks}")
    print(f"每 SM 线程: {actual_threads}")
    print(f"占用率: {occupancy:.1f}%")
    
    return occupancy

# 示例
calculate_occupancy(threads_per_block=256, regs_per_thread=32, smem_per_block=4096)
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
    
    # 估算总 CUDA Cores (近似)
    # 每 SM 的 CUDA Cores 取决于架构
    cuda_cores_per_sm = {
        7: 64,   # Volta
        8: 64,   # Ampere
        9: 128,  # Hopper
    }
    cores = cuda_cores_per_sm.get(props.major, 64) * props.multi_processor_count
    print(f"估算 CUDA Cores: {cores}")

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

- **GPU 是层次化结构**：Device → GPC → TPC → SM → Cores
- **SM 是核心计算单元**：包含 CUDA Cores、Tensor Cores、调度器、内存
- **Warp 是执行单位**：32 线程 SIMT 执行，避免分支分歧
- **占用率影响性能**：平衡寄存器、共享内存、线程数配置

---

*下一篇：[04-cuda-programming.md](04-cuda-programming.md) - CUDA 编程模型*
