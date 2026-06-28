# 算子优化

> 算子优化就像赛车改装——引擎不变，但通过改进进气系统、排气管和悬挂，让每一匹马力都发挥到极致。

## 目录

- [算子优化概述](#算子优化概述)
- [FlashAttention](#flashattention)
- [Fused Kernel 实战](#fused-kernel-实战)
- [内存访问优化](#内存访问优化)
- [自定义 CUDA Kernel](#自定义-cuda-kernel)
- [算子优化实践指南](#算子优化实践指南)
- [延伸阅读](#延伸阅读)

---

## 算子优化概述

### 为什么算子优化如此重要

```
大模型训练/推理的时间分布

典型 Transformer 模型的算子时间占比：

┌──────────────────────────────────────────────┐
│ Attention (Q·K^T, Softmax, @V)  ████████████ 35-50%  │
│ MatMul (Linear 层)              ████████████ 30-40%  │
│ LayerNorm + 其他                ████         10-15%  │
│ 通信 (分布式)                   ███          5-15%   │
│ 数据加载                        ██           5-10%   │
└──────────────────────────────────────────────┘

关键洞察：
  Attention 和 MatMul 占 70-85% 的时间
  优化这两个算子的收益最大
```

### 优化维度

```
算子优化的三个维度

1. 计算优化
   ├── 算法改进（如 FlashAttention）
   ├── 近似计算（如稀疏注意力）
   └── 低精度计算（FP16/FP8/INT8）

2. 内存优化
   ├── 减少显存占用（内存复用）
   ├── 减少数据搬运（Fused Kernel）
   └── 利用内存层次（Tiling）

3. 并行优化
   ├── 线程级并行（Warp 内）
   ├── Block 级并行（SM 内）
   └── Kernel 级并行（多流）
```

---

## FlashAttention

### 标准 Attention 的问题

```
标准 Attention 的显存问题

输入: Q, K, V ∈ R^{N×d}   (N=序列长度, d=头维度)

标准计算步骤:
  S = Q · K^T         ← S ∈ R^{N×N}，O(N²) 显存！
  P = softmax(S)      ← P ∈ R^{N×N}，又一个 O(N²)
  O = P · V           ← 最终输出

问题: 当 N=8192 (8K 上下文)
  S 矩阵大小: 8192 × 8192 × 2 bytes = 128 MB（每个头！）
  32 个头: 128 MB × 32 = 4 GB！
  仅 Attention 矩阵就占用大量显存

  N=128K 时: 128K × 128K × 2 × 32 = 1 TB！完全不可行
```

### FlashAttention 原理

```
FlashAttention 的核心思想: Tiling + Online Softmax

关键洞察：
  不需要在显存中"物化"完整的 N×N 注意力矩阵
  可以分块计算，在 SRAM（共享内存）中完成 Softmax

标准 Attention:                    FlashAttention:
┌────────────────────┐            ┌────────────────────┐
│    HBM (显存)       │            │    HBM (显存)       │
│  ┌──────────────┐  │            │  ┌──────────────┐  │
│  │ Q (全量)     │  │            │  │ Q (全量)     │  │
│  │ K (全量)     │  │            │  │ K (全量)     │  │
│  │ V (全量)     │  │            │  │ V (全量)     │  │
│  │ S (N×N) 🔴  │  │            │  │ O (输出)     │  │
│  │ P (N×N) 🔴  │  │            │  └──────────────┘  │
│  │ O (输出)     │  │            │                     │
│  └──────────────┘  │            │    SRAM (共享内存)   │
│                     │            │  ┌──────────────┐  │
│  S 和 P 的 O(N²)    │            │  │ Q_block      │  │
│  显存是瓶颈！       │            │  │ K_block      │  │
│                     │            │  │ V_block      │  │
└────────────────────┘            │  │ S_block (小)  │  │
                                   │  └──────────────┘  │
                                   │                     │
                                   │  只需 O(N) 显存!    │
                                   └────────────────────┘
```

### FlashAttention 的分块算法

```
FlashAttention 分块计算过程

外循环: 遍历 K, V 的分块
  内循环: 遍历 Q 的分块
    1. 从 HBM 加载 Q_i, K_j, V_j 到 SRAM
    2. 在 SRAM 中计算 S_ij = Q_i · K_j^T
    3. Online Softmax: 更新 max, sum, 分块输出
    4. 更新 O_i（累积输出）
    5. 不需要将 S_ij 写回 HBM！

Online Softmax 的技巧:
  传统: 需要先算完整行的 max → 再算 exp → 再算 sum
  Online: 逐块更新 max 和 sum，数学上等价

  m_new = max(m_old, block_max)
  l_new = l_old * exp(m_old - m_new) + sum(exp(block - m_new))
  O_new = (l_old * exp(m_old - m_new) * O_old + exp(block - m_new) @ V) / l_new
```

### FlashAttention 性能对比

```
性能对比 (A100 80GB, FP16)

序列长度    标准 Attention    FlashAttention-2    加速比
─────────────────────────────────────────────────────
  512        0.3 ms           0.2 ms             1.5x
  2048       2.1 ms           0.8 ms             2.6x
  8192       34 ms            4.2 ms             8.1x
  32768      OOM ❌           18 ms              ∞
  128K       OOM ❌           ~80 ms             ∞

显存节省:
  8K 序列: 4 GB → 数 MB (100x+ 节省)
  FlashAttention 使得长上下文成为可能！
```

### 使用方法

```python
# 方法 1: PyTorch 内置（推荐，2.0+）
import torch
import torch.nn.functional as F

# PyTorch 2.0+ 自动使用 FlashAttention
with torch.backends.cuda.sdp_kernel(
    enable_flash=True,      # FlashAttention
    enable_math=False,      # 禁用标准实现
    enable_mem_efficient=False,
):
    output = F.scaled_dot_product_attention(q, k, v, is_causal=True)

# 方法 2: flash-attn 库（更多功能）
from flash_attn import flash_attn_func

# 输入形状: (batch, seqlen, num_heads, head_dim)
output = flash_attn_func(q, k, v, causal=True)

# 方法 3: FlashAttention with ALiBi, Sliding Window 等
from flash_attn import flash_attn_func
output = flash_attn_func(
    q, k, v,
    causal=True,
    window_size=(512, 512),  # 滑动窗口
)
```

---

## Fused Kernel 实战

### 常见的算子融合

```python
import triton
import triton.language as tl

@triton.jit
def fused_layer_norm_kernel(
    x_ptr, weight_ptr, bias_ptr, output_ptr,
    N,  # 隐藏维度
    eps: tl.constexpr,
    BLOCK_SIZE: tl.constexpr,
):
    """融合的 LayerNorm Kernel"""
    row = tl.program_id(0)
    cols = tl.arange(0, BLOCK_SIZE)
    mask = cols < N
    
    # 加载一行数据
    x = tl.load(x_ptr + row * N + cols, mask=mask, other=0.0).to(tl.float32)
    
    # 计算均值
    mean = tl.sum(x, axis=0) / N
    
    # 计算方差
    diff = x - mean
    var = tl.sum(diff * diff, axis=0) / N
    
    # 归一化
    rstd = 1.0 / tl.sqrt(var + eps)
    x_norm = diff * rstd
    
    # 应用 affine 变换
    weight = tl.load(weight_ptr + cols, mask=mask)
    bias = tl.load(bias_ptr + cols, mask=mask)
    output = x_norm * weight + bias
    
    # 存储结果
    tl.store(output_ptr + row * N + cols, output, mask=mask)

# 对比：PyTorch 的 LayerNorm 需要 3 次 Kernel Launch + 多次显存读写
# Fused 版本：1 次 Kernel Launch + 1 次读写
```

### RMSNorm 融合

```python
@triton.jit
def fused_rmsnorm_kernel(
    x_ptr, weight_ptr, output_ptr,
    N,
    eps: tl.constexpr,
    BLOCK_SIZE: tl.constexpr,
):
    """融合的 RMSNorm (Llama/Qwen 使用)"""
    row = tl.program_id(0)
    cols = tl.arange(0, BLOCK_SIZE)
    mask = cols < N
    
    x = tl.load(x_ptr + row * N + cols, mask=mask, other=0.0).to(tl.float32)
    
    # RMS = sqrt(mean(x²))
    rms = tl.sqrt(tl.sum(x * x, axis=0) / N + eps)
    x_norm = x / rms
    
    weight = tl.load(weight_ptr + cols, mask=mask)
    output = x_norm * weight
    
    tl.store(output_ptr + row * N + cols, output, mask=mask)
```

### SwiGLU 融合

```python
@triton.jit
def fused_swiglu_kernel(
    gate_ptr, up_ptr, output_ptr,
    N,
    BLOCK_SIZE: tl.constexpr,
):
    """融合的 SwiGLU 激活 (Llama FFN)
    
    SwiGLU(x) = (x · W_gate) × SiLU(x · W_gate) × (x · W_up)
    简化为: gate_output × silu(gate_output) × up_output
    """
    pid = tl.program_id(0)
    offsets = pid * BLOCK_SIZE + tl.arange(0, BLOCK_SIZE)
    mask = offsets < N
    
    gate = tl.load(gate_ptr + offsets, mask=mask)
    up = tl.load(up_ptr + offsets, mask=mask)
    
    # SiLU(x) = x * sigmoid(x)
    silu_gate = gate * tl.sigmoid(gate)
    output = silu_gate * up
    
    tl.store(output_ptr + offsets, output, mask=mask)
```

---

## 内存访问优化

### GPU 内存层次

```
GPU 内存层次与带宽

                    容量         带宽          延迟
                    ─────        ─────        ─────
寄存器文件          ~256KB/SM    ~20 TB/s     ~1 cycle
  ↓
共享内存/L1 Cache   ~228KB/SM   ~20 TB/s     ~30 cycles
  ↓
L2 Cache            ~50 MB      ~6 TB/s      ~200 cycles
  ↓
HBM (显存)          80 GB       3.35 TB/s    ~500 cycles
  ↓
CPU DRAM            ≥256 GB     ~50 GB/s     ~10000 cycles

关键洞察:
  HBM → 寄存器 的延迟差 500x
  优化原则: 尽可能在高层内存中完成计算
  这就是 Tiling 和算子融合有效的根本原因
```

### Tiling 策略

```
Tiling (分块) 优化矩阵乘法

朴素实现: 逐元素计算
  C[i,j] += A[i,k] * B[k,j]
  每次从 HBM 读取 → 计算密度低

Tiling 实现: 分块计算
  ┌─────────────────┐
  │ A               │     ┌──────────────────┐
  │ ┌───┐           │     │ B                │
  │ │A₁₁│A₁₂│...   │     │ ┌───┐            │
  │ ├───┤           │     │ │B₁₁│B₁₂│...    │
  │ │A₂₁│           │     │ ├───┤            │
  │ └───┘           │     │ │B₂₁│            │
  └─────────────────┘     │ └───┘            │
                           └──────────────────┘

  1. 加载 A₁₁, B₁₁ 到共享内存 (一次 HBM 读取)
  2. 在共享内存中计算 C₁₁ += A₁₁ × B₁₁ (多次复用)
  3. 加载下一块...

  数据复用率: O(BLOCK_SIZE) 倍
  BLOCK_SIZE=128 → 数据复用 128 倍！
```

### 内存合并访问

```
内存合并访问 (Memory Coalescing)

GPU 以 128 字节 (32×FP32) 为单位访问 HBM

良好的访问模式 (合并):            差的访问模式 (跨步):
Thread 0: addr[0]                Thread 0: addr[0]
Thread 1: addr[1]                Thread 1: addr[128]    ← 跨步
Thread 2: addr[2]                Thread 2: addr[256]
...                              ...
→ 1 次内存事务                    → 32 次内存事务（32x 慢！）

实践建议:
  • 矩阵按行优先存储时，连续线程访问连续列
  • 转置操作通过共享内存中间缓冲避免跨步访问
  • 注意张量的 stride 和 contiguous 属性
```

---

## 自定义 CUDA Kernel

### 何时需要自定义 Kernel

```
是否需要自定义 Kernel？

标准 PyTorch 算子
  └── 效果满足需求？ → ✅ 不需要自定义
       │ ❌
       ▼
torch.compile 编译优化
  └── 效果满足需求？ → ✅ 不需要自定义
       │ ❌
       ▼
现有 Triton Kernel（如 FlashAttention）
  └── 能否复用？     → ✅ 直接使用
       │ ❌
       ▼
编写自定义 Triton Kernel ← 优先
  └── 性能满足需求？  → ✅
       │ ❌
       ▼
编写 CUDA C++ Kernel ← 最后手段
```

### CUDA C++ Kernel 示例

```cpp
// CUDA C++ 融合的 RoPE (旋转位置编码) Kernel
__global__ void fused_rope_kernel(
    float* __restrict__ q,      // [batch, seq, heads, dim]
    float* __restrict__ k,
    const float* __restrict__ cos_cache,  // [max_seq, dim/2]
    const float* __restrict__ sin_cache,
    int batch_size, int seq_len, int num_heads, int head_dim
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int total = batch_size * seq_len * num_heads * (head_dim / 2);
    if (idx >= total) return;
    
    // 解析索引
    int half_dim = head_dim / 2;
    int d = idx % half_dim;
    int remaining = idx / half_dim;
    int h = remaining % num_heads;
    remaining /= num_heads;
    int s = remaining % seq_len;
    int b = remaining / seq_len;
    
    int base = ((b * seq_len + s) * num_heads + h) * head_dim;
    
    float cos_val = cos_cache[s * half_dim + d];
    float sin_val = sin_cache[s * half_dim + d];
    
    // 对 Q 应用 RoPE
    float q0 = q[base + d];
    float q1 = q[base + d + half_dim];
    q[base + d] = q0 * cos_val - q1 * sin_val;
    q[base + d + half_dim] = q0 * sin_val + q1 * cos_val;
    
    // 对 K 应用 RoPE
    float k0 = k[base + d];
    float k1 = k[base + d + half_dim];
    k[base + d] = k0 * cos_val - k1 * sin_val;
    k[base + d + half_dim] = k0 * sin_val + k1 * cos_val;
}
```

---

## 算子优化实践指南

### 优化优先级

```
算子优化投入产出排行

投入产出比    优化手段                        预期收益
──────────────────────────────────────────────────
⭐⭐⭐⭐⭐     使用 FlashAttention              2-8x (Attention)
⭐⭐⭐⭐⭐     torch.compile                    1.3-2x (全模型)
⭐⭐⭐⭐      使用 BF16/FP16 混合精度           1.5-2x
⭐⭐⭐⭐      开启 Tensor Core (矩阵对齐)       1.2-1.5x
⭐⭐⭐       Triton 自定义 Fused Kernel        1.2-3x (目标算子)
⭐⭐⭐       CUDA Graphs（减少 Launch 开销）    1.1-1.5x
⭐⭐        自定义 CUDA C++ Kernel            1.1-1.5x (极致优化)
⭐⭐        量化（INT8/FP8）                  1.5-2x (推理)
```

### 验证优化效果

```python
import torch
import time

def benchmark_kernel(func, *args, warmup=10, repeat=100):
    """基准测试 Kernel 性能"""
    # 预热
    for _ in range(warmup):
        func(*args)
    torch.cuda.synchronize()
    
    # 计时
    start = time.perf_counter()
    for _ in range(repeat):
        func(*args)
    torch.cuda.synchronize()
    end = time.perf_counter()
    
    avg_ms = (end - start) / repeat * 1000
    return avg_ms

# 对比标准实现 vs 优化实现
standard_time = benchmark_kernel(standard_attention, q, k, v)
flash_time = benchmark_kernel(flash_attention, q, k, v)

print(f"Standard: {standard_time:.2f} ms")
print(f"Flash:    {flash_time:.2f} ms")
print(f"Speedup:  {standard_time/flash_time:.1f}x")
```

---

## 参考资料与引用

1. Dao, T., et al. (2022). *FlashAttention: Fast and Memory-Efficient Exact Attention with IO-Awareness*. arXiv:2205.14135. https://arxiv.org/abs/2205.14135
2. Dao, T. (2023). *FlashAttention-2: Faster Attention with Better Parallelism and Work Partitioning*. arXiv:2307.08691. https://arxiv.org/abs/2307.08691
3. Shah, J., et al. (2024). *FlashAttention-3: Fast and Accurate Attention with Asynchrony and Low-precision*. arXiv:2407.08608. https://arxiv.org/abs/2407.08608
4. Triton Tutorials - GPU Programming in Python. https://triton-lang.org/main/getting-started/tutorials/
5. CUTLASS: CUDA Templates for Linear Algebra Subroutines. NVIDIA. https://github.com/NVIDIA/cutlass
6. Boehm, S. (2022). *How to Optimize a CUDA Matmul Kernel for cuBLAS-like Performance*. https://siboehm.com/articles/22/CUDA-MMM

---

*上一篇：[02-xla-tvm-triton.md](02-xla-tvm-triton.md)* | *下一篇：[04-profiling-tools.md](04-profiling-tools.md)*

[返回目录](README.md) | [返回主页](../README.md)
