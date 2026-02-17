# 内存层次结构

> 理解 GPU 内存金字塔，掌握内存优化策略。

## 目录

- [内存层次金字塔](#内存层次金字塔)
- [各级内存详解](#各级内存详解)
- [HBM 高带宽内存](#hbm-高带宽内存)
- [内存优化策略](#内存优化策略)
- [实战练习](#实战练习)

---

## 内存层次金字塔

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

### 各级内存特性对比

| 内存级别 | 容量 | 带宽 | 延迟 | 作用域 |
|----------|------|------|------|--------|
| **Registers** | ~256 KB/SM | ~20 TB/s | 0 cycles | 线程 |
| **Shared/L1** | ~228 KB/SM | ~10 TB/s | ~30 cycles | Block |
| **L2 Cache** | ~50 MB | ~5 TB/s | ~200 cycles | GPU |
| **HBM** | 80-192 GB | 2-8 TB/s | ~500 cycles | GPU |
| **System** | 数百 GB | ~64 GB/s | ~10K cycles | CPU+GPU |

---

## 各级内存详解

### Register File

```cpp
// 寄存器是最快的存储，编译器自动分配
__global__ void kernel() {
    int a = 1;           // 存储在寄存器
    float b = 2.0f;      // 存储在寄存器
    float c[4];          // 可能在寄存器或 Local Memory
    float d[100];        // 太大，溢出到 Local Memory
}

// 查看寄存器使用量
// nvcc --ptxas-options=-v kernel.cu
```

### Shared Memory

```cpp
// 静态声明
__shared__ float smem[256];

// 动态声明
extern __shared__ float dynamic_smem[];

// Kernel 调用时指定大小
kernel<<<grid, block, sharedMemSize>>>();

// 配置 Shared Memory 和 L1 Cache 比例
cudaFuncSetCacheConfig(kernel, cudaFuncCachePreferShared);  // 偏好 Shared
cudaFuncSetCacheConfig(kernel, cudaFuncCachePreferL1);      // 偏好 L1
cudaFuncSetCacheConfig(kernel, cudaFuncCachePreferEqual);   // 平均分配
```

### Global Memory

```cpp
// 分配
float *d_ptr;
cudaMalloc(&d_ptr, size);

// 访问 - 注意合并访问
__global__ void kernel(float *data) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    float val = data[idx];  // 全局内存访问
}

// 优化: 使用 __ldg() 走只读缓存
float val = __ldg(&data[idx]);
```

---

## HBM 高带宽内存

### HBM 架构

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

### HBM 代际演进

| 版本 | 发布年 | 带宽 | 容量/Stack | 代表 GPU |
|------|--------|------|------------|----------|
| HBM | 2015 | 128 GB/s | 4 GB | AMD Fury |
| HBM2 | 2016 | 256 GB/s | 8 GB | V100 |
| HBM2e | 2020 | 450 GB/s | 16 GB | A100 |
| HBM3 | 2022 | 665 GB/s | 24 GB | H100 |
| HBM3e | 2024 | 1.15 TB/s | 36 GB | B200 |

---

## 内存优化策略

### 1. 数据复用 (Shared Memory Tiling)

```cpp
// 矩阵乘法分块
__global__ void matmul_tiled(float *A, float *B, float *C, int N) {
    __shared__ float As[TILE][TILE];
    __shared__ float Bs[TILE][TILE];
    
    int row = blockIdx.y * TILE + threadIdx.y;
    int col = blockIdx.x * TILE + threadIdx.x;
    float sum = 0;
    
    for (int t = 0; t < N/TILE; t++) {
        // 加载到共享内存
        As[threadIdx.y][threadIdx.x] = A[row*N + t*TILE + threadIdx.x];
        Bs[threadIdx.y][threadIdx.x] = B[(t*TILE + threadIdx.y)*N + col];
        __syncthreads();
        
        // 复用共享内存数据
        for (int k = 0; k < TILE; k++)
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        __syncthreads();
    }
    C[row*N + col] = sum;
}
```

### 2. 合并访问 (Memory Coalescing)

```
✅ 合并访问模式:
Thread 0 → data[0]
Thread 1 → data[1]
Thread 2 → data[2]
...
→ 一次 128B 事务

❌ 非合并访问:
Thread 0 → data[0]
Thread 1 → data[stride]
Thread 2 → data[2*stride]
...
→ 多次事务
```

```cpp
// 转置示例: AoS to SoA
// Array of Structures (AoS) - 非合并
struct Point { float x, y, z; };
Point points[N];
// 访问 x: points[i].x 跨步为 12 bytes

// Structure of Arrays (SoA) - 合并
float x[N], y[N], z[N];
// 访问 x: x[i] 连续
```

### 3. 预取 (Prefetching)

```cpp
__global__ void kernel_with_prefetch(float *data, int N) {
    __shared__ float smem[2][TILE];
    
    // 双缓冲预取
    int ping = 0;
    smem[ping][threadIdx.x] = data[blockIdx.x * TILE + threadIdx.x];
    
    for (int i = 1; i < N/TILE; i++) {
        // 预取下一块
        smem[1-ping][threadIdx.x] = data[(blockIdx.x + i) * TILE + threadIdx.x];
        __syncthreads();
        
        // 处理当前块
        process(smem[ping]);
        __syncthreads();
        
        ping = 1 - ping;  // 切换缓冲
    }
}
```

### 4. 避免 Bank Conflict

```
Shared Memory Bank 分配:
Bank 0:  addr 0-3,   32-35,  64-67,  ...
Bank 1:  addr 4-7,   36-39,  68-71,  ...
Bank 2:  addr 8-11,  40-43,  72-75,  ...
...
Bank 31: addr 124-127, 156-159, ...

冲突示例:
// 32 线程都访问 Bank 0
smem[threadIdx.x * 32]  // ❌ 32-way conflict

避免方法:
// 添加 padding
__shared__ float smem[32][33];  // 33 而非 32
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
    
    # 预热
    b.copy_(a)
    torch.cuda.synchronize()
    
    # 计时
    iterations = 100
    start = time.time()
    for _ in range(iterations):
        b.copy_(a)
    torch.cuda.synchronize()
    elapsed = time.time() - start
    
    # 带宽 (读 + 写)
    total_bytes = 2 * size_gb * 1024**3 * iterations
    bandwidth_gbps = total_bytes / elapsed / 1024**3
    
    print(f"数据量: {size_gb} GB, 类型: {dtype}")
    print(f"带宽: {bandwidth_gbps:.1f} GB/s")

bandwidth_test(size_gb=1.0)
```

### 练习 2：比较不同内存访问模式

```python
import torch
import time

def access_pattern_benchmark():
    N = 10000
    M = 10000
    
    # 创建矩阵
    matrix = torch.randn(N, M, device='cuda')
    
    # 行优先访问 (连续)
    torch.cuda.synchronize()
    start = time.time()
    for _ in range(100):
        row_sum = matrix.sum(dim=1)
    torch.cuda.synchronize()
    row_time = time.time() - start
    
    # 列优先访问 (跨步)
    torch.cuda.synchronize()
    start = time.time()
    for _ in range(100):
        col_sum = matrix.sum(dim=0)
    torch.cuda.synchronize()
    col_time = time.time() - start
    
    print(f"行求和 (连续访问): {row_time:.4f}s")
    print(f"列求和 (跨步访问): {col_time:.4f}s")
    print(f"比例: {col_time/row_time:.2f}x")

access_pattern_benchmark()
```

---

## 小结

- **内存金字塔**：Register > Shared > L2 > HBM > System，越近越快
- **HBM 是关键**：提供 TB/s 级带宽，是 GPU 性能的保障
- **优化策略**：数据复用、合并访问、预取、避免 Bank Conflict

---

*下一篇：[06-tensor-core.md](06-tensor-core.md) - Tensor Core 详解*
