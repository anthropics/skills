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
└─────────────────────────────────────────────────────────────┘
```

### 线程层次结构

```cpp
// CUDA 线程层次 (CUDA C/C++)
// Grid: 由多个 Block 组成
// Block: 由多个 Thread 组成

// 线程索引计算
// 1D 索引
int global_idx = blockIdx.x * blockDim.x + threadIdx.x;

// 2D 索引
int row = blockIdx.y * blockDim.y + threadIdx.y;
int col = blockIdx.x * blockDim.x + threadIdx.x;

// 3D 索引
int x = blockIdx.x * blockDim.x + threadIdx.x;
int y = blockIdx.y * blockDim.y + threadIdx.y;
int z = blockIdx.z * blockDim.z + threadIdx.z;
```

---

## 核函数编写

### 基本语法

```cpp
// 核函数声明
__global__ void kernel_name(parameters) {
    // 核函数代码
}

// 调用语法
kernel_name<<<gridDim, blockDim>>>(arguments);
kernel_name<<<gridDim, blockDim, sharedMemSize, stream>>>(arguments);
```

### 向量加法示例

```cpp
// 向量加法核函数
__global__ void vectorAdd(float *a, float *b, float *c, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    
    if (idx < n) {
        c[idx] = a[idx] + b[idx];
    }
}

// 主机代码
int main() {
    int n = 1000000;
    size_t bytes = n * sizeof(float);
    
    // 分配设备内存
    float *d_a, *d_b, *d_c;
    cudaMalloc(&d_a, bytes);
    cudaMalloc(&d_b, bytes);
    cudaMalloc(&d_c, bytes);
    
    // 配置执行参数
    int blockSize = 256;
    int numBlocks = (n + blockSize - 1) / blockSize;
    
    // 启动核函数
    vectorAdd<<<numBlocks, blockSize>>>(d_a, d_b, d_c, n);
    
    // 释放内存
    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);
    
    return 0;
}
```

### PyTorch 中使用 CUDA

```python
import torch

# 检查 CUDA 可用性
print(f"CUDA available: {torch.cuda.is_available()}")
print(f"Device count: {torch.cuda.device_count()}")

# 创建 GPU 张量
x = torch.randn(1000, 1000, device='cuda')
y = torch.randn(1000, 1000, device='cuda')

# GPU 计算
z = torch.matmul(x, y)

# 同步
torch.cuda.synchronize()

# 显存管理
print(f"Allocated: {torch.cuda.memory_allocated() / 1024**2:.1f} MB")
print(f"Cached: {torch.cuda.memory_reserved() / 1024**2:.1f} MB")

# 清理缓存
torch.cuda.empty_cache()
```

---

## 内存管理

### 内存类型

| 内存类型 | 作用域 | 生命周期 | 速度 |
|----------|--------|----------|------|
| **Register** | 线程 | 线程 | 最快 |
| **Local** | 线程 | 线程 | 慢 (溢出到 Global) |
| **Shared** | Block | Block | 快 |
| **Global** | 所有线程 | 应用 | 最慢 |
| **Constant** | 所有线程 | 应用 | 快 (缓存) |
| **Texture** | 所有线程 | 应用 | 快 (缓存) |

### 内存分配

```cpp
// 全局内存
float *d_ptr;
cudaMalloc(&d_ptr, size);
cudaFree(d_ptr);

// 主机-设备传输
cudaMemcpy(d_ptr, h_ptr, size, cudaMemcpyHostToDevice);
cudaMemcpy(h_ptr, d_ptr, size, cudaMemcpyDeviceToHost);

// 异步传输
cudaMemcpyAsync(d_ptr, h_ptr, size, cudaMemcpyHostToDevice, stream);

// 统一内存 (CUDA 6.0+)
float *unified_ptr;
cudaMallocManaged(&unified_ptr, size);
```

### Shared Memory 使用

```cpp
__global__ void matMul(float *A, float *B, float *C, int N) {
    // 声明共享内存
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];
    
    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;
    float sum = 0.0f;
    
    // 分块计算
    for (int t = 0; t < N / TILE_SIZE; t++) {
        // 协作加载到共享内存
        As[threadIdx.y][threadIdx.x] = A[row * N + t * TILE_SIZE + threadIdx.x];
        Bs[threadIdx.y][threadIdx.x] = B[(t * TILE_SIZE + threadIdx.y) * N + col];
        __syncthreads();  // 同步
        
        // 从共享内存计算
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }
        __syncthreads();
    }
    
    C[row * N + col] = sum;
}
```

---

## 关键优化技术

### 1. 合并内存访问 (Coalesced Access)

```cpp
// ✅ 好的访问模式：连续线程访问连续内存
c[idx] = a[idx] + b[idx];  // idx = 0,1,2,3... (coalesced)

// ❌ 坏的访问模式：跨步访问
c[idx] = a[idx * stride];  // stride > 1 (uncoalesced)
```

```
合并访问 (一次事务):
Thread 0 → Addr 0
Thread 1 → Addr 4
Thread 2 → Addr 8
...
Thread 31 → Addr 124
→ 一次 128 字节事务

非合并访问 (多次事务):
Thread 0 → Addr 0
Thread 1 → Addr 128
Thread 2 → Addr 256
...
→ 32 次事务！
```

### 2. 避免 Bank Conflict

```cpp
// Shared Memory 分为 32 个 bank
// 连续 4 字节地址映射到不同 bank

// ✅ 无冲突：不同线程访问不同 bank
shared[threadIdx.x]  // Thread i → Bank i

// ❌ 有冲突：多线程访问同一 bank
shared[threadIdx.x * 32]  // 所有线程访问 Bank 0
```

### 3. 循环展开

```cpp
// 原始循环
for (int i = 0; i < 4; i++) {
    sum += a[i] * b[i];
}

// 展开后
sum += a[0] * b[0];
sum += a[1] * b[1];
sum += a[2] * b[2];
sum += a[3] * b[3];

// 编译器指令
#pragma unroll
for (int i = 0; i < 4; i++) {
    sum += a[i] * b[i];
}
```

### 4. 使用 Tensor Core

```python
import torch

# 确保使用 Tensor Core 的条件:
# 1. 矩阵维度是 8 的倍数
# 2. 使用 FP16/BF16
# 3. 使用 cuBLAS/cuDNN

a = torch.randn(1024, 1024, device='cuda', dtype=torch.float16)
b = torch.randn(1024, 1024, device='cuda', dtype=torch.float16)
c = torch.matmul(a, b)  # 自动使用 Tensor Core

# 混合精度训练
with torch.cuda.amp.autocast():
    output = model(input)  # 自动选择精度
```

---

## 性能分析工具

### NVIDIA Nsight

```bash
# Nsight Systems - 系统级分析
nsys profile -o report python train.py

# Nsight Compute - Kernel 级分析
ncu --set full -o report python train.py
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

# 打印结果
print(prof.key_averages().table(sort_by="cuda_time_total", row_limit=10))

# 导出 Chrome trace
prof.export_chrome_trace("trace.json")
```

### 常用性能指标

| 指标 | 含义 | 目标 |
|------|------|------|
| **Occupancy** | SM 占用率 | > 50% |
| **Memory Throughput** | 内存带宽利用率 | > 60% |
| **Compute Throughput** | 算力利用率 | > 60% |
| **SM Efficiency** | SM 活跃时间比例 | > 80% |
| **Warp Stall** | Warp 等待原因 | 最小化 |

---

## 实战练习

### 练习 1：向量加法

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
    
    # 预热
    _ = a_gpu + b_gpu
    torch.cuda.synchronize()
    
    start = time.time()
    c_gpu = a_gpu + b_gpu
    torch.cuda.synchronize()
    gpu_time = time.time() - start
    
    print(f"CPU: {cpu_time:.4f}s")
    print(f"GPU: {gpu_time:.4f}s")
    print(f"加速比: {cpu_time/gpu_time:.1f}x")

vector_add_benchmark()
```

### 练习 2：矩阵乘法性能

```python
def matmul_benchmark(size=4096, dtype=torch.float32, iterations=100):
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
    
    # TFLOPS = 2 * N^3
    flops = 2 * size**3 * iterations
    tflops = flops / elapsed / 1e12
    
    print(f"{str(dtype):20} - {tflops:.1f} TFLOPS")

print("矩阵乘法性能对比 (4096×4096):")
matmul_benchmark(dtype=torch.float32)
matmul_benchmark(dtype=torch.float16)
matmul_benchmark(dtype=torch.bfloat16)
```

---

## 小结

- **CUDA 编程层次**：Grid → Block → Thread 映射到 GPU → SM → Core
- **内存层次**：Register > Shared > Global，合理使用各级内存
- **优化关键**：合并访问、避免 Bank Conflict、提高占用率
- **工具辅助**：Nsight Systems/Compute、PyTorch Profiler

---

*下一篇：[05-memory-hierarchy.md](05-memory-hierarchy.md) - 内存层次结构*
