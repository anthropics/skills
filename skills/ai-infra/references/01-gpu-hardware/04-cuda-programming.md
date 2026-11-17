# CUDA 编程模型

> 理解 CUDA 编程的核心概念、内存模型和优化技术。

## 目录

- [基本概念映射](#基本概念映射)
- [核函数编写](#核函数编写)
- [内存管理](#内存管理)
- [关键优化技术](#关键优化技术)
- [性能分析工具](#性能分析工具)
- [实战练习](#实战练习)

---

## 基本概念映射

### 生活类比：组织一次全校考试

```
CUDA 编程就像组织一次全校大考试：

  Grid (网格) = 整个学校
    │
    ├── Block (线程块) = 一个考场（教室）
    │     │
    │     ├── Warp = 一排座位（32 个同学）
    │     │
    │     └── Thread = 一个考生
    │
    │  每个考场有自己的：
    │  - 黑板 (Shared Memory) → 本考场学生共享
    │  - 考生的桌面 (Register) → 只有自己能用
    │
    └── 学校图书馆 (Global Memory) → 所有人都能访问，但跑一趟很慢

关键规则：
  1. 不同考场的学生不能交流（Block 间不直接通信）
  2. 同一排座位的学生必须做同一道题（Warp 内同一指令）
  3. 考生的桌面空间有限（寄存器有上限）
```

### 软件概念到硬件的映射

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
│  重要理解：                                                  │
│  一个 Block 的所有线程一定在同一个 SM 上运行                │
│  但一个 SM 可以同时运行多个 Block                            │
│  Block 完成后，SM 可以接新的 Block（动态调度）               │
└─────────────────────────────────────────────────────────────┘
```

### 线程索引：你在哪个考场的哪个座位？

```cpp
// 每个线程都需要知道"我是谁，我处理哪个数据"

// 1D 索引（最常用）
int global_idx = blockIdx.x * blockDim.x + threadIdx.x;
//                考场编号 × 每考场人数 + 考场内座位号

// 例如：Block 2 的 Thread 5，每 Block 256 线程
// global_idx = 2 × 256 + 5 = 517 → 处理第 517 个元素

// 2D 索引（矩阵运算常用）
int row = blockIdx.y * blockDim.y + threadIdx.y;
int col = blockIdx.x * blockDim.x + threadIdx.x;

// 3D 索引（体数据、视频处理）
int x = blockIdx.x * blockDim.x + threadIdx.x;
int y = blockIdx.y * blockDim.y + threadIdx.y;
int z = blockIdx.z * blockDim.z + threadIdx.z;
```

---

## 核函数编写

### 基本语法

```cpp
// 核函数声明：__global__ 表示在 GPU 执行，从 CPU 调用
__global__ void kernel_name(parameters) {
    // 在 GPU 上并行执行的代码
}

// 调用语法：<<<网格大小, 块大小>>>
kernel_name<<<gridDim, blockDim>>>(arguments);
kernel_name<<<gridDim, blockDim, sharedMemSize, stream>>>(arguments);

// __device__: 在 GPU 执行，从 GPU 调用（辅助函数）
// __host__:   在 CPU 执行，从 CPU 调用（默认）
```

### 向量加法——CUDA 入门的 "Hello World"

```cpp
// 目标：c[i] = a[i] + b[i]，n 个元素并行计算
__global__ void vectorAdd(float *a, float *b, float *c, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    
    // 边界检查：线程总数可能超过数组大小
    if (idx < n) {
        c[idx] = a[idx] + b[idx];
    }
}

int main() {
    int n = 1000000;
    size_t bytes = n * sizeof(float);
    
    // 分配设备内存
    float *d_a, *d_b, *d_c;
    cudaMalloc(&d_a, bytes);
    cudaMalloc(&d_b, bytes);
    cudaMalloc(&d_c, bytes);
    
    // 配置执行参数
    int blockSize = 256;  // 每 Block 256 线程（经验值）
    int numBlocks = (n + blockSize - 1) / blockSize;  // 向上取整
    // numBlocks = (1000000 + 255) / 256 = 3907
    
    // 启动 —— 3907 个 Block × 256 个线程 = 999,936 个线程
    vectorAdd<<<numBlocks, blockSize>>>(d_a, d_b, d_c, n);
    
    cudaFree(d_a); cudaFree(d_b); cudaFree(d_c);
    return 0;
}
```

```
理解这个例子的执行过程：

1. CPU 调用 vectorAdd<<<3907, 256>>>
2. GPU 创建 3907 × 256 = 999,936 个线程
3. 这些线程被分配到各个 SM 上
   - H100 有 132 个 SM
   - 每个 SM 可能同时运行多个 Block
4. 每个线程只做一件事：c[idx] = a[idx] + b[idx]
5. 百万次加法在微秒级完成

关键：一个线程只做一件小事，但百万线程并行
  → 这就是 GPU 的哲学
```

### 为什么 blockSize 通常是 256？

```
blockSize 选择的考量：

太小（如 32）:
  - Block 内只有 1 个 Warp
  - 无法利用 Shared Memory 做数据复用
  - 不够隐藏内存延迟

太大（如 1024）:
  - 寄存器/共享内存被一个 Block 占满
  - 每 SM 只能放 1-2 个 Block
  - 调度灵活性差

256 是经验最优值：
  - 8 个 Warp = 足够的调度粒度
  - 每 SM 可以放 8 个 Block (2048/256)
  - 寄存器/共享内存分配合理
  - 适合绝大多数 kernel

特殊情况：
  - 需要大量共享内存的 kernel → 可能用 128
  - 需要大量线程协作的 kernel → 可能用 512 或 1024
```

### PyTorch 中使用 CUDA

```python
import torch

# PyTorch 封装了底层 CUDA 操作，你通常不需要写 CUDA 代码
# 但理解底层有助于写出高效的 PyTorch 代码

# 创建 GPU 张量 → 内部调用 cudaMalloc
x = torch.randn(1000, 1000, device='cuda')
y = torch.randn(1000, 1000, device='cuda')

# GPU 计算 → 内部启动 cuBLAS kernel
z = torch.matmul(x, y)

# 重要：GPU 操作是异步的！
# CPU 代码不等 GPU 算完就继续执行
z = torch.matmul(x, y)  # CPU 只是"下单"，GPU 在后台算
print("CPU 已经跑到这里了，GPU 可能还在算")

# 要准确计时必须同步
torch.cuda.synchronize()  # 等 GPU 算完

# 显存管理
print(f"已分配: {torch.cuda.memory_allocated() / 1024**2:.1f} MB")
print(f"已缓存: {torch.cuda.memory_reserved() / 1024**2:.1f} MB")
# 缓存 > 已分配：PyTorch 的内存池，减少 cudaMalloc 调用
torch.cuda.empty_cache()  # 释放缓存（不影响已分配）
```

---

## 内存管理

### 内存类型与速度差异

```
┌─────────────────────────────────────────────────────────┐
│  CUDA 内存类型——速度差异可以超过 1000 倍！              │
├──────────┬─────────┬──────────┬────────┬────────────────┤
│ 内存类型  │ 作用域  │ 速度     │ 容量   │ 类比           │
├──────────┼─────────┼──────────┼────────┼────────────────┤
│ Register │ 线程    │ ~20TB/s  │ 极小   │ 口袋           │
│ Shared   │ Block   │ ~10TB/s  │ 228KB  │ 桌面           │
│ L2 Cache │ GPU     │ ~5TB/s   │ 50MB   │ 办公室书架     │
│ Global   │ 所有    │ ~3TB/s   │ 80GB   │ 城市图书馆     │
│ System   │ CPU+GPU │ ~64GB/s  │ 数百GB │ 另一座城市     │
└──────────┴─────────┴──────────┴────────┴────────────────┘

Register vs Global 速度差: ~7x
Global vs System 速度差: ~50x

所有 CUDA 优化的核心思想：
  尽量从快的内存读 → 数据复用 (Shared Memory Tiling)
  尽量少从慢的内存读 → 合并访问 (Memory Coalescing)
```

### 内存分配与传输

```cpp
// 全局内存
float *d_ptr;
cudaMalloc(&d_ptr, size);    // GPU 上分配
cudaFree(d_ptr);             // GPU 上释放

// 主机-设备传输（最慢的操作之一！）
cudaMemcpy(d_ptr, h_ptr, size, cudaMemcpyHostToDevice);  // CPU → GPU
cudaMemcpy(h_ptr, d_ptr, size, cudaMemcpyDeviceToHost);  // GPU → CPU
// 走 PCIe 总线，带宽只有 ~32 GB/s，是 HBM 的 1/100

// 异步传输（与计算重叠）
cudaMemcpyAsync(d_ptr, h_ptr, size, cudaMemcpyHostToDevice, stream);
// 需要 pinned memory: cudaMallocHost(&h_ptr, size)

// 统一内存（简化编程，但性能较低）
float *unified_ptr;
cudaMallocManaged(&unified_ptr, size);
// CPU 和 GPU 都能访问，驱动自动迁移数据
```

### Shared Memory 使用——矩阵乘法分块

```cpp
// 经典示例：为什么 Shared Memory 能加速矩阵乘法

// 朴素版：每次从 Global Memory 读
__global__ void matMul_naive(float *A, float *B, float *C, int N) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    float sum = 0.0f;
    for (int k = 0; k < N; k++) {
        sum += A[row * N + k] * B[k * N + col];
        // 每次迭代：2 次 Global Memory 读 → 500 cycles 延迟
    }
    C[row * N + col] = sum;
}
// N=1024 时：每线程 1024 次循环 × 2 次读 = 2048 次 Global 读

// 分块版：先读到 Shared Memory，反复使用
__global__ void matMul_tiled(float *A, float *B, float *C, int N) {
    __shared__ float As[TILE][TILE];  // 16×16 = 256 floats = 1KB
    __shared__ float Bs[TILE][TILE];
    
    int row = blockIdx.y * TILE + threadIdx.y;
    int col = blockIdx.x * TILE + threadIdx.x;
    float sum = 0.0f;
    
    for (int t = 0; t < N / TILE; t++) {
        // 全 Block 协作加载一块到 Shared Memory
        As[threadIdx.y][threadIdx.x] = A[row * N + t * TILE + threadIdx.x];
        Bs[threadIdx.y][threadIdx.x] = B[(t * TILE + threadIdx.y) * N + col];
        __syncthreads();  // 等所有人加载完
        
        // 从 Shared Memory 读（~30 cycles vs ~500 cycles）
        for (int k = 0; k < TILE; k++) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }
        __syncthreads();  // 等所有人算完再加载下一块
    }
    C[row * N + col] = sum;
}
// Global 读次数：从 2048 降到 2048/TILE = 128（TILE=16 时）
// 加速 16 倍！（理论值，实际取决于带宽利用率）
```

```
为什么分块有效？——数据复用

朴素版：
  线程 (0,0) 读 A 的第 0 行 和 B 的第 0 列
  线程 (0,1) 读 A 的第 0 行 和 B 的第 1 列
  → A 的第 0 行被 256 个线程重复读了 256 次！

分块版：
  A 的一块 (16×16) 被一个 Block 的 256 个线程协作读入 Shared Memory
  然后 256 个线程从 Shared Memory 反复使用这块数据
  每个数据只从 Global Memory 读 1 次，但被使用 16 次
  → 减少了 16 倍的 Global Memory 访问
```

---

## 关键优化技术

### 1. 合并内存访问 (Coalesced Access)

```
GPU 内存系统以 128 字节为单位访问 Global Memory

合并访问：一个 Warp 的 32 个线程访问连续 128 字节 → 1 次事务
非合并访问：32 个线程访问分散地址 → 最多 32 次事务！

┌─────────────────────────────────────────┐
│ 合并访问 (1 次事务):                     │
│ Thread 0 → data[0]   (addr 0)           │
│ Thread 1 → data[1]   (addr 4)           │
│ Thread 2 → data[2]   (addr 8)           │
│ ...                                      │
│ Thread 31 → data[31] (addr 124)          │
│ → 128 字节连续，一次搞定                │
├─────────────────────────────────────────┤
│ 非合并访问 (32 次事务):                  │
│ Thread 0 → data[0]     (addr 0)         │
│ Thread 1 → data[128]   (addr 512)       │
│ Thread 2 → data[256]   (addr 1024)      │
│ ...                                      │
│ → 每个线程跨越 512 字节，32 次事务      │
│ → 带宽利用率: 4/128 = 3.1%              │
└─────────────────────────────────────────┘
```

```cpp
// ✅ 好的访问模式
c[idx] = a[idx] + b[idx];  // 连续线程访问连续地址

// ❌ 坏的访问模式
c[idx] = a[idx * stride];  // stride > 1，非连续

// 常见陷阱：AoS vs SoA
// Array of Structures (AoS) — 非合并
struct Point { float x, y, z; };
Point points[N];  // 访问所有 x: points[i].x 跨步 12 bytes

// Structure of Arrays (SoA) — 合并
float x[N], y[N], z[N];  // 访问所有 x: x[i] 连续
```

### 2. 避免 Bank Conflict

```
Shared Memory 被分为 32 个 bank，每 bank 宽 4 bytes
同一 bank 被多个线程同时访问 → bank conflict → 串行化

Bank 分配规则：
  addr 0-3   → Bank 0
  addr 4-7   → Bank 1
  addr 8-11  → Bank 2
  ...
  addr 124-127 → Bank 31
  addr 128-131 → Bank 0  (循环)

// ✅ 无冲突：连续线程访问连续 bank
smem[threadIdx.x]  → Thread 0→Bank 0, Thread 1→Bank 1, ...

// ❌ 32-way 冲突：所有线程访问同一 bank
smem[threadIdx.x * 32]  → 全部落在 Bank 0 → 32 次串行

// 经典解决方案：padding
__shared__ float smem[32][33];  // 多一列，打破 bank 对齐
// 原本 smem[i][0] 都在 Bank 0
// 加了 padding 后 smem[i][0] 落在不同 bank
```

### 3. 循环展开

```cpp
// 减少循环控制开销，增加指令级并行
// 原始循环
for (int i = 0; i < 4; i++) {
    sum += a[i] * b[i];
}

// 展开后（编译器可以同时发射多条指令）
sum += a[0] * b[0];
sum += a[1] * b[1];
sum += a[2] * b[2];
sum += a[3] * b[3];

// 编译器指令：让编译器自动展开
#pragma unroll
for (int i = 0; i < 4; i++) {
    sum += a[i] * b[i];
}
```

### 4. 确保使用 Tensor Core

```python
import torch

# Tensor Core 激活条件：
# 1. 矩阵维度是 8 的倍数 (FP16) 或 16 的倍数 (INT8)
# 2. 数据类型是 FP16/BF16/TF32/INT8/FP8
# 3. 使用 cuBLAS/cuDNN 后端
# 4. 内存 256 bytes 对齐

# PyTorch 自动处理对齐，你只需确保前两条：

# ✅ 使用 Tensor Core
a = torch.randn(1024, 1024, device='cuda', dtype=torch.float16)  # 8 的倍数
b = torch.randn(1024, 1024, device='cuda', dtype=torch.float16)
c = torch.matmul(a, b)

# ❌ 可能不用 Tensor Core（维度不对齐）
a = torch.randn(1000, 1000, device='cuda', dtype=torch.float16)  # 1000 不是 8 的倍数
# PyTorch 可能会 pad，但效率不如原生对齐

# 混合精度训练——自动选择最优精度
with torch.amp.autocast(device_type="cuda"):
    output = model(input)  # 矩阵乘法用 FP16(Tensor Core)，加法用 FP32
```

---

## 性能分析工具

### NVIDIA Nsight

```bash
# Nsight Systems - 系统级分析（看全貌）
nsys profile -o report python train.py
# 可以看到：CPU/GPU 时间线、kernel 启动、内存传输、空闲时间

# Nsight Compute - Kernel 级分析（看细节）
ncu --set full -o report python train.py
# 可以看到：每个 kernel 的占用率、带宽利用率、Tensor Core 使用率
```

### PyTorch Profiler

```python
from torch.profiler import profile, ProfilerActivity

with profile(
    activities=[ProfilerActivity.CPU, ProfilerActivity.CUDA],
    record_shapes=True,
    profile_memory=True,
    with_stack=True
) as prof:
    model(input)

# 打印最耗时的操作
print(prof.key_averages().table(sort_by="cuda_time_total", row_limit=10))

# 导出到 Chrome 可视化
prof.export_chrome_trace("trace.json")
# 用 Chrome 打开 chrome://tracing 加载 trace.json
```

### 性能指标解读

| 指标 | 含义 | 目标 | 说明 |
|------|------|------|------|
| **Occupancy** | SM 占用率 | > 50% | 太低说明寄存器/共享内存用多了 |
| **Memory Throughput** | 内存带宽利用率 | > 60% | 太低说明计算密集，太高说明内存瓶颈 |
| **Compute Throughput** | 算力利用率 | > 60% | 越高越好，说明 GPU 在干活 |
| **SM Efficiency** | SM 活跃比例 | > 80% | 太低说明 Block 数不够 |
| **Warp Stall** | Warp 等待原因 | 最小化 | 内存等待 > 执行等待 → 内存瓶颈 |

---

## 实战练习

### 练习 1：CPU vs GPU 向量加法

```python
import torch
import time

def vector_add_benchmark():
    n = 100_000_000
    
    # CPU
    a_cpu = torch.randn(n)
    b_cpu = torch.randn(n)
    start = time.time()
    c_cpu = a_cpu + b_cpu
    cpu_time = time.time() - start
    
    # GPU
    a_gpu = torch.randn(n, device='cuda')
    b_gpu = torch.randn(n, device='cuda')
    _ = a_gpu + b_gpu  # 预热
    torch.cuda.synchronize()
    
    start = time.time()
    c_gpu = a_gpu + b_gpu
    torch.cuda.synchronize()  # 必须同步才能准确计时！
    gpu_time = time.time() - start
    
    print(f"CPU: {cpu_time:.4f}s")
    print(f"GPU: {gpu_time:.4f}s")
    print(f"加速比: {cpu_time/gpu_time:.1f}x")

vector_add_benchmark()
```

### 练习 2：矩阵乘法——不同精度对比

```python
def matmul_benchmark(size=4096, dtype=torch.float32, iterations=100):
    a = torch.randn(size, size, device='cuda', dtype=dtype)
    b = torch.randn(size, size, device='cuda', dtype=dtype)
    
    torch.matmul(a, b)  # 预热
    torch.cuda.synchronize()
    
    start = time.time()
    for _ in range(iterations):
        c = torch.matmul(a, b)
    torch.cuda.synchronize()
    elapsed = time.time() - start
    
    # TFLOPS = 2 × N³ (矩阵乘法的浮点运算次数)
    flops = 2 * size**3 * iterations
    tflops = flops / elapsed / 1e12
    print(f"{str(dtype):20} - {tflops:.1f} TFLOPS")

print("矩阵乘法性能对比 (4096×4096):")
matmul_benchmark(dtype=torch.float32)   # CUDA Core (或 TF32)
matmul_benchmark(dtype=torch.float16)   # Tensor Core
matmul_benchmark(dtype=torch.bfloat16)  # Tensor Core
```

---

## 小结

```
CUDA 编程核心知识：

1. 编程模型: Grid → Block → Thread 映射到 GPU → SM → Core
   理解映射关系是写高效代码的基础

2. 内存层次: Register > Shared > L2 > Global
   数据离计算单元越近越好 → Tiling 是核心优化手段

3. 关键优化:
   - 合并访问：连续线程访问连续内存
   - Shared Memory Tiling：减少 Global Memory 访问
   - 避免 Bank Conflict：padding 技巧
   - 保证 Tensor Core 使用：维度对齐 + 正确数据类型

4. AI 开发者通常不需要手写 CUDA
   但理解底层原理能帮你：
   - 选择正确的 batch size（8 的倍数）
   - 理解为什么某些操作慢（内存瓶颈 vs 计算瓶颈）
   - 有效使用混合精度训练
```

---

*下一篇：[05-memory-hierarchy.md](05-memory-hierarchy.md) - 内存层次结构*

---

## 参考资料与引用

1. **NVIDIA.** *CUDA C++ Programming Guide.*  
   https://docs.nvidia.com/cuda/cuda-c-programming-guide/

2. **NVIDIA.** *CUDA Toolkit Documentation.*  
   https://docs.nvidia.com/cuda/

3. **Kirk, D. B., & Hwu, W. (2016).** *Programming Massively Parallel Processors.* 3rd Edition, Morgan Kaufmann. — CUDA 编程权威教材  
   https://www.elsevier.com/books/programming-massively-parallel-processors/kirk/978-0-12-811986-0

4. **NVIDIA.** *cuBLAS Library.* — GPU 矩阵运算库  
   https://docs.nvidia.com/cuda/cublas/

5. **NVIDIA.** *CUDA Best Practices Guide.*  
   https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/
