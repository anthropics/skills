# 内存层次结构

> 理解 GPU 内存金字塔，掌握内存优化策略。

## 目录

- [内存层次金字塔](#内存层次金字塔)
- [各级内存详解](#各级内存详解)
- [HBM 高带宽内存](#hbm-高带宽内存)
- [内存优化策略](#内存优化策略)
- [大模型中的内存瓶颈](#大模型中的内存瓶颈)
- [实战练习](#实战练习)

---

## 内存层次金字塔

### 生活类比：你的学习材料存放在哪里？

```
你正在解一道数学题，需要查各种公式：

寄存器 (Register)  → 你脑子里记住的公式
  速度：瞬间，0 延迟
  容量：很少，记不了几个

共享内存 (Shared)   → 桌面上摊开的笔记
  速度：扫一眼就行，~30 纳秒
  容量：一张桌子放不了太多

L2 Cache            → 手边的书架
  速度：起身拿一下，~200 纳秒
  容量：几十本参考书

HBM (Global Memory) → 隔壁的图书馆
  速度：走过去找书，~500 纳秒
  容量：80GB，海量

系统内存 (CPU)      → 另一栋楼的档案馆
  速度：得过马路走一趟，~10,000 纳秒
  容量：上百 GB

核心优化思想：
  把要反复用的公式背下来（寄存器）
  把这道题需要的笔记放桌上（Shared Memory）
  尽量少跑图书馆（减少 Global Memory 访问）
```

### 内存金字塔

```
                    ┌─────────────┐
                    │  Registers  │  ← 最快，线程私有
                    │   ~20 TB/s  │     零延迟
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
              │    HBM (Global Mem)     │  ← 最大，最慢（GPU内）
              │      ~3 TB/s            │     ~500 cycles
              └────────────┬────────────┘
                           │
              ┌────────────▼────────────┐
              │   System Memory (CPU)   │  ← PCIe 带宽限制
              │      ~64 GB/s           │     ~10000 cycles
              └─────────────────────────┘
```

### 各级内存特性对比

| 内存级别 | 容量 | 带宽 | 延迟 | 作用域 | 对 AI 的意义 |
|----------|------|------|------|--------|-------------|
| **Registers** | ~256 KB/SM | ~20 TB/s | 0 cycles | 线程 | 循环中的累加变量 |
| **Shared/L1** | ~228 KB/SM | ~10 TB/s | ~30 cycles | Block | Tiling 数据复用 |
| **L2 Cache** | ~50 MB | ~5 TB/s | ~200 cycles | GPU | 小张量自动缓存 |
| **HBM** | 80-192 GB | 2-8 TB/s | ~500 cycles | GPU | 模型参数+KV Cache |
| **System** | 数百 GB | ~64 GB/s | ~10K cycles | CPU+GPU | ZeRO Offload |

---

## 各级内存详解

### Register File——最快但最珍贵

```
每个 SM 有 256 KB 寄存器（H100），所有活跃线程共享

为什么寄存器如此重要？
  - 访问速度：0 延迟！每周期都可读写
  - 是计算的"工作台"——所有中间结果先放这里

寄存器溢出 (Register Spill) 的代价：
  如果一个线程需要的变量超过可用寄存器
  → 编译器自动把多余的放到 Local Memory（实际是 Global Memory）
  → 速度从 0 cycles 直接跳到 ~500 cycles → 性能悬崖

如何检查溢出:
  nvcc --ptxas-options=-v kernel.cu
  → 输出: registers=64, spill=0 (好) 或 spill=128 (坏)
```

```cpp
__global__ void kernel() {
    int a = 1;           // ✅ 存在寄存器（快）
    float b = 2.0f;      // ✅ 存在寄存器
    float c[4];          // ⚠️ 小数组可能在寄存器
    float d[100];        // ❌ 太大，溢出到 Local Memory（慢！）
}
```

### Shared Memory——团队协作的关键

```
类比：一个工作小组的共享白板

  - 同一 Block 的所有线程都能读写
  - 不同 Block 的 Shared Memory 互相看不到
  - H100: 每 SM 最大 228 KB，可与 L1 Cache 动态分配

主要用途：
  1. 数据复用（Tiling）——从 HBM 读一次，用多次
  2. 线程间通信——Block 内的线程交换数据
  3. 归约操作——求和、求最大值等

关键操作：__syncthreads()
  → Block 内所有线程的同步点
  → "等所有人都把数据写到白板上，再一起读"
```

```cpp
// Shared Memory 与 L1 Cache 的配比
// 物理上共用同一块 SRAM，可以软件配置

cudaFuncSetCacheConfig(kernel, cudaFuncCachePreferShared);
// Shared Memory 优先 → Tiling 场景

cudaFuncSetCacheConfig(kernel, cudaFuncCachePreferL1);
// L1 Cache 优先 → 随机访问场景
```

### Global Memory (HBM)

```
最大但最慢（GPU 内）的存储

HBM 特点：
  - 容量大：80-192 GB（放得下整个模型）
  - 带宽高：2-8 TB/s（对比 CPU 内存 ~100 GB/s）
  - 延迟大：~500 cycles（对比 Register 0 cycles）

为什么 HBM 延迟这么高还能被接受？
  因为 GPU 靠"大量 Warp 轮流执行"来隐藏延迟
  不是等数据回来，而是切换到其他 Warp 继续算

Global Memory 访问优化的关键：合并访问（见优化策略）
```

---

## HBM 高带宽内存

### HBM 为什么比 DDR 快？

```
传统 DDR (CPU 内存):
  ┌─────┐                    ┌─────────────────┐
  │ CPU │ ←── PCB 走线 ──→  │  DDR 芯片组     │
  └─────┘    (长距离,窄总线)  └─────────────────┘
  总线宽度: 64 bit
  带宽: ~50 GB/s

HBM (GPU 内存):
  ┌─────────────────────────────────────────────┐
  │              硅中介层 (Interposer)           │
  │  ┌─────┐  ┌─────┐  ┌─────┐  ┌─────┐        │
  │  │HBM  │  │HBM  │  │ GPU │  │HBM  │        │
  │  │Stack│  │Stack│  │ Die │  │Stack│        │
  │  └─────┘  └─────┘  └─────┘  └─────┘        │
  │      ↑        ↑        ↑        ↑          │
  │      └────────┴────────┴────────┘          │
  │           Through-Silicon Vias (TSV)        │
  └─────────────────────────────────────────────┘
  总线宽度: 1024 bit（16 倍！）
  距离: 微米级（vs 厘米级）
  带宽: 数 TB/s

HBM 快的三个原因：
  1. 宽总线：1024 bit vs 64 bit → 单次传输数据 16 倍
  2. 短距离：芯片贴着芯片（微米 vs 厘米） → 信号传输快
  3. 3D 堆叠：多层 DRAM 芯片叠起来 → 密度和带宽同时提升
```

### HBM 代际演进

| 版本 | 发布年 | 每 Stack 带宽 | 每 Stack 容量 | 代表 GPU |
|------|--------|------|------------|----------|
| HBM | 2015 | 128 GB/s | 4 GB | AMD Fury |
| HBM2 | 2016 | 256 GB/s | 8 GB | V100 |
| HBM2e | 2020 | 450 GB/s | 16 GB | A100 |
| HBM3 | 2022 | 665 GB/s | 24 GB | H100 |
| HBM3e | 2024 | 1.15 TB/s | 36 GB | B200 |

```
为什么 HBM 带宽对 LLM 如此关键？

LLM 推理是"内存带宽瓶颈"型任务：
  每生成一个 token，需要读取全部模型参数
  LLaMA-7B (FP16): 14 GB 参数，每 token 都要读一遍
  
  A100 (2 TB/s): 14 GB / 2000 GB/s = 7ms → ~143 tokens/s
  H100 (3.35 TB/s): 14 GB / 3350 = 4.2ms → ~238 tokens/s
  B200 (8 TB/s): 14 GB / 8000 = 1.75ms → ~571 tokens/s

HBM 带宽翻倍 → LLM 推理速度近乎翻倍！
这就是为什么每代 GPU 的 HBM 升级对 AI 社区至关重要
```

---

## 内存优化策略

### 策略 1: 数据复用 (Shared Memory Tiling)

```
核心思想：从 HBM 读一次，在 Shared Memory 中用多次

矩阵乘法 C = A × B (N×N):
  朴素方式：每个元素 C[i][j] 需要读 A 的一行 + B 的一列
    → 总 Global 读次数: N² × 2N = 2N³

  Tiling (TILE=16):
    把 A 和 B 各切成 16×16 的小块
    每个 Block 负责 C 的一个 16×16 区域
    每个小块从 HBM 读入 Shared Memory 后，被 16 个线程复用
    → 总 Global 读次数: 2N³/16 = N³/8

  加速：16x 减少内存访问（TILE 越大加速越多，但受限于 Shared Memory 大小）
```

### 策略 2: 合并访问 (Memory Coalescing)

```
一个 Warp 32 线程的访问模式决定了实际内存事务数

✅ 合并（1 次 128B 事务）:     ❌ 非合并（多次事务）:
Thread 0 → data[0]            Thread 0 → data[0]
Thread 1 → data[1]            Thread 1 → data[stride]
Thread 2 → data[2]            Thread 2 → data[2*stride]
...                            ...
→ 带宽利用率接近 100%          → 带宽利用率可能 < 10%

实际应用：
// AoS (Array of Structures) — 非合并
struct Point { float x, y, z; };
Point points[N];
// 读所有 x: points[0].x, points[1].x, ... → 跨步 12 bytes

// SoA (Structure of Arrays) — 合并
float x[N], y[N], z[N];
// 读所有 x: x[0], x[1], ... → 连续！

PyTorch 张量默认行优先（C 连续），沿最后一维访问是合并的
转置后变列优先 → 访问模式可能不合并 → .contiguous() 修复
```

### 策略 3: 异步传输与计算重叠

```
问题：CPU → GPU 数据传输走 PCIe，只有 ~32 GB/s

同步方式（低效）：
  [传输 batch 1] [计算 batch 1] [传输 batch 2] [计算 batch 2]

异步方式（高效）——使用 CUDA Stream：
  Stream 1: [传输 batch 1] [传输 batch 2] [传输 batch 3]
  Stream 2:                [计算 batch 1] [计算 batch 2] [计算 batch 3]
  
  传输和计算并行！总时间 ≈ max(传输, 计算) 而非 传输+计算

PyTorch DataLoader 的 pin_memory=True + num_workers > 0
就是利用了这个原理
```

---

## 大模型中的内存瓶颈

### 训练时的内存构成

```
以 LLaMA-7B + AdamW + FP16 训练为例：

┌──────────────────────────────────────────────────────────┐
│  显存构成                                                 │
├──────────────────────────────────────────────────────────┤
│                                                           │
│  FP16 模型参数:   7B × 2 bytes  =  14 GB                │
│  FP16 梯度:       7B × 2 bytes  =  14 GB                │
│  FP32 优化器:     7B × 12 bytes =  84 GB                │
│    ├ FP32 参数副本: 4 bytes/param                        │
│    ├ Adam m (动量): 4 bytes/param                        │
│    └ Adam v (方差): 4 bytes/param                        │
│  ──────────────────────────────────                      │
│  模型状态合计:                    112 GB                 │
│                                                           │
│  激活值 (batch_size=4, seq=2048):                        │
│    每层: ~2 × batch × seq × hidden × 2 bytes            │
│    32 层合计:                     ~16 GB                  │
│  ──────────────────────────────────                      │
│  总计:                            ~128 GB               │
│                                                           │
│  单张 A100 80GB → 放不下！                               │
│  需要：ZeRO/FSDP 切分 + 激活值重算 (activation checkpointing) │
└──────────────────────────────────────────────────────────┘
```

### 推理时的内存构成

```
LLaMA-7B FP16 推理：

┌──────────────────────────────────────────────────────┐
│  模型参数: 14 GB（固定，只读）                         │
│                                                       │
│  KV Cache（随生成长度增长）:                           │
│    每层: 2 × batch × seq × n_heads × head_dim × 2   │
│    = 2 × 1 × 2048 × 32 × 128 × 2 = 32 MB/层        │
│    32 层: ~1 GB                                       │
│                                                       │
│  batch=32 时: KV Cache = 32 GB                       │
│  → KV Cache 成为显存的最大消费者！                    │
│                                                       │
│  这就是 PagedAttention (vLLM) 存在的意义：            │
│  高效管理动态增长的 KV Cache 内存                     │
└──────────────────────────────────────────────────────┘
```

### 算术强度与内存瓶颈

```
算术强度 (Arithmetic Intensity) = 计算量 / 内存访问量

如果 AI < GPU 的 计算/带宽 比值 → 内存瓶颈
如果 AI > GPU 的 计算/带宽 比值 → 计算瓶颈

H100: 1979 TFLOPS / 3.35 TB/s ≈ 590 FLOPs/Byte

矩阵乘法 (M×K × K×N):
  计算: 2MKN FLOPs
  内存: (MK + KN + MN) × 2 bytes
  AI = 2MKN / (2(MK+KN+MN))
  
  大矩阵 (4096×4096): AI ≈ 1365 > 590 → 计算瓶颈 ✅
  小矩阵 (64×64):     AI ≈ 21 < 590   → 内存瓶颈 ❌

LLM 推理 Decode 阶段（batch=1）:
  矩阵向量乘 W × x，W=[4096,4096], x=[4096,1]
  计算: 2×4096×4096 = 33M FLOPs
  内存: 4096×4096 × 2 = 32 MB（要读整个权重！）
  AI = 33M / 32M = ~1 FLOP/Byte << 590

  → 严重的内存带宽瓶颈！这就是 LLM 推理慢的根本原因
```

---

## 实战练习

### 练习 1：内存带宽测试

```python
import torch
import time

def bandwidth_test(size_gb=1.0, dtype=torch.float32):
    bytes_per_elem = torch.tensor([], dtype=dtype).element_size()
    num_elements = int(size_gb * 1024**3 / bytes_per_elem)
    
    a = torch.randn(num_elements, device='cuda', dtype=dtype)
    b = torch.empty_like(a)
    
    b.copy_(a)  # 预热
    torch.cuda.synchronize()
    
    iterations = 100
    start = time.time()
    for _ in range(iterations):
        b.copy_(a)
    torch.cuda.synchronize()
    elapsed = time.time() - start
    
    total_bytes = 2 * size_gb * 1024**3 * iterations  # 读 + 写
    bandwidth_gbps = total_bytes / elapsed / 1024**3
    
    print(f"数据量: {size_gb} GB, 类型: {dtype}")
    print(f"实测带宽: {bandwidth_gbps:.1f} GB/s")
    # 对比理论值：A100=2TB/s, H100=3.35TB/s

bandwidth_test(size_gb=1.0)
```

### 练习 2：内存访问模式对比

```python
def access_pattern_benchmark():
    N = 10000
    M = 10000
    matrix = torch.randn(N, M, device='cuda')
    
    # 行求和（沿最后一维，连续访问，合并）
    torch.cuda.synchronize()
    start = time.time()
    for _ in range(100):
        row_sum = matrix.sum(dim=1)
    torch.cuda.synchronize()
    row_time = time.time() - start
    
    # 列求和（沿第一维，跨步访问，非合并）
    torch.cuda.synchronize()
    start = time.time()
    for _ in range(100):
        col_sum = matrix.sum(dim=0)
    torch.cuda.synchronize()
    col_time = time.time() - start
    
    print(f"行求和 (连续/合并): {row_time:.4f}s")
    print(f"列求和 (跨步/非合并): {col_time:.4f}s")
    print(f"比例: {col_time/row_time:.2f}x")

access_pattern_benchmark()
```

---

## 小结

```
GPU 内存层次核心知识：

1. 金字塔结构: Register > Shared > L2 > HBM > System
   速度差异超过 1000 倍！优化 = 让数据尽量待在快的层级

2. HBM 是 AI 的关键: 带宽决定 LLM 推理速度
   每代 HBM 升级直接提升 AI 工作负载性能

3. 内存瓶颈是 LLM 推理的核心挑战:
   Decode 阶段算术强度 ~1 FLOP/Byte，远低于 GPU 能力
   → 优化方向：量化(减少数据量)、KV Cache 管理、批处理

4. 三大优化策略：
   - Tiling: 读一次用多次
   - Coalescing: 连续线程读连续地址
   - 计算-传输重叠: 异步 Stream
```

---

*下一篇：[06-tensor-core.md](06-tensor-core.md) - Tensor Core 详解*

---

## 参考资料与引用

1. **NVIDIA.** *CUDA C++ Programming Guide — Memory Hierarchy.*  
   https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#memory-hierarchy

2. **NVIDIA.** *GPU Memory: HBM vs GDDR.*  
   https://www.nvidia.com/en-us/data-center/hbm/

3. **Jia, Z., et al. (2018).** *Dissecting the NVidia Turing T4 GPU via Microbenchmarking.* — GPU 内存层次性能测量  
   https://arxiv.org/abs/1804.06826

4. **Dao, T., et al. (2022).** *FlashAttention: Fast and Memory-Efficient Exact Attention with IO-Awareness.* — HBM 带宽瓶颈与 IO-aware 算法  
   https://arxiv.org/abs/2205.14135

5. **NVIDIA.** *Shared Memory and Caches.* — 共享内存与 L1/L2 缓存详解  
   https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/index.html#shared-memory
