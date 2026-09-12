# 为什么需要 GPU

> 理解 GPU 的价值，从理解它与 CPU 的本质区别开始。

## 目录

- [CPU vs GPU：设计哲学的差异](#cpu-vs-gpu设计哲学的差异)
- [为什么 AI 需要 GPU](#为什么-ai-需要-gpu)
- [GPU 计算的本质优势](#gpu-计算的本质优势)
- [AI 工作负载特性分析](#ai-工作负载特性分析)
- [GPU vs 其他加速器](#gpu-vs-其他加速器)
- [实战练习](#实战练习)

---

## CPU vs GPU：设计哲学的差异

### 架构对比图

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        CPU vs GPU 架构对比                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   CPU (延迟优化 - Latency Oriented)                                     │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                                                                 │  │
│   │   ┌──────────────────────────────────────────────────────────┐ │  │
│   │   │              Control Logic (复杂控制单元)                  │ │  │
│   │   │         分支预测、乱序执行、推测执行                        │ │  │
│   │   └──────────────────────────────────────────────────────────┘ │  │
│   │                                                                 │  │
│   │   ┌───────────────────────┐  ┌───────────────────────────────┐ │  │
│   │   │     L1 Cache          │  │        L2 Cache               │ │  │
│   │   │      (32KB/core)      │  │         (256KB/core)          │ │  │
│   │   └───────────────────────┘  └───────────────────────────────┘ │  │
│   │                                                                 │  │
│   │   ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐ │  │
│   │   │   Core 0   │ │   Core 1   │ │   Core 2   │ │   Core 3   │ │  │
│   │   │  (复杂ALU) │ │  (复杂ALU) │ │  (复杂ALU) │ │  (复杂ALU) │ │  │
│   │   └────────────┘ └────────────┘ └────────────┘ └────────────┘ │  │
│   │                                                                 │  │
│   │           4-64 个复杂核心，每个核心可独立执行                     │  │
│   │                                                                 │  │
│   └─────────────────────────────────────────────────────────────────┘  │
│                                                                         │
│   GPU (吞吐优化 - Throughput Oriented)                                  │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                                                                 │  │
│   │   ┌──────────────────────────────────────────────────────────┐ │  │
│   │   │       Minimal Control (精简控制单元)                       │ │  │
│   │   └──────────────────────────────────────────────────────────┘ │  │
│   │                                                                 │  │
│   │   ┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐ │  │
│   │   └─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘ │  │
│   │   ┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐ │  │
│   │   └─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘ │  │
│   │   ┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐ │  │
│   │   └─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘ │  │
│   │         ... 数千个简单核心，同时执行相同操作 ...                  │  │
│   │   ┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐ │  │
│   │   └─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘ │  │
│   │                                                                 │  │
│   │           数千个简单核心，SIMT 执行模式                           │  │
│   │                                                                 │  │
│   └─────────────────────────────────────────────────────────────────┘  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 设计哲学详解

#### CPU：延迟优化 (Latency-Oriented)

CPU 设计的核心目标是**最小化单个任务的完成时间**：

```
                    CPU 设计优先级
    ┌─────────────────────────────────────────┐
    │                                         │
    │   1. 分支预测 (Branch Prediction)        │
    │      └─ 猜测下一条指令，减少等待          │
    │                                         │
    │   2. 乱序执行 (Out-of-Order Execution)  │
    │      └─ 重排指令，最大化利用执行单元       │
    │                                         │
    │   3. 推测执行 (Speculative Execution)   │
    │      └─ 提前执行可能需要的指令            │
    │                                         │
    │   4. 大容量缓存 (Large Caches)           │
    │      └─ L1/L2/L3 缓存减少内存访问延迟     │
    │                                         │
    │   5. 高频时钟 (High Clock Speed)         │
    │      └─ 3-5 GHz 时钟频率                 │
    │                                         │
    └─────────────────────────────────────────┘
```

这些特性使 CPU 在处理**串行任务、复杂控制流、低延迟响应**方面表现出色。

#### GPU：吞吐优化 (Throughput-Oriented)

GPU 设计的核心目标是**最大化单位时间内处理的数据量**：

```
                    GPU 设计优先级
    ┌─────────────────────────────────────────┐
    │                                         │
    │   1. 大规模并行 (Massive Parallelism)    │
    │      └─ 数千个计算单元同时工作            │
    │                                         │
    │   2. 高内存带宽 (High Memory Bandwidth)  │
    │      └─ HBM 提供 TB/s 级带宽             │
    │                                         │
    │   3. 简单控制逻辑 (Simple Control)       │
    │      └─ 减少每核心面积，增加核心数量       │
    │                                         │
    │   4. SIMT 执行模型                       │
    │      └─ 单指令多线程，共享控制开销        │
    │                                         │
    │   5. 延迟隐藏 (Latency Hiding)           │
    │      └─ 通过大量线程切换隐藏内存延迟       │
    │                                         │
    └─────────────────────────────────────────┘
```

### 数值对比

| 特性 | CPU (Intel Xeon) | GPU (H100) | 差异倍数 |
|------|------------------|------------|----------|
| **核心数** | 56 核 | 16,896 CUDA Cores | 300x |
| **时钟频率** | 3.5 GHz | 1.8 GHz | 0.5x |
| **内存带宽** | 307 GB/s | 3,350 GB/s | 11x |
| **FP32 峰值** | ~3 TFLOPS | ~67 TFLOPS | 22x |
| **FP16 峰值** | ~6 TFLOPS | ~1,979 TFLOPS (Tensor Core, 含稀疏) | 330x |
| **功耗** | 350W | 700W | 2x |
| **能效比 (TFLOPS/W)** | 0.017 | 1.4 | 82x |

---

## 为什么 AI 需要 GPU

### 深度学习的计算本质

深度学习的核心操作可以归结为几类矩阵运算：

```
┌─────────────────────────────────────────────────────────────────────┐
│                   深度学习核心运算                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   1. 矩阵乘法 (Matrix Multiplication)                               │
│      Y = X × W                                                      │
│      ├── 全连接层 (Fully Connected)                                 │
│      ├── 注意力计算 (Attention: Q×K^T, Score×V)                     │
│      └── 卷积 (展开后的 im2col 矩阵乘)                               │
│                                                                     │
│   2. 逐元素运算 (Element-wise Operations)                           │
│      ├── 激活函数 (ReLU, GELU, SiLU)                                │
│      ├── 残差连接 (Y = X + F(X))                                    │
│      └── 归一化 (LayerNorm, BatchNorm)                              │
│                                                                     │
│   3. 规约运算 (Reduction Operations)                                │
│      ├── Softmax (指数 + 求和 + 除法)                                │
│      ├── 池化 (Max/Average Pooling)                                 │
│      └── 损失计算 (Cross-Entropy)                                   │
│                                                                     │
│   运算比例 (典型 Transformer):                                       │
│   ┌──────────────────────────────────────────────────────────┐     │
│   │ 矩阵乘法 █████████████████████████████████████░░░░░░░ 85% │     │
│   │ 逐元素   ████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░ 10% │     │
│   │ 规约运算 ██░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░ 5% │     │
│   └──────────────────────────────────────────────────────────┘     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### AI 任务与 GPU 的匹配度

| AI 特性 | GPU 能力 | 匹配度 | 说明 |
|---------|----------|--------|------|
| **大规模并行计算** | 数千个计算核心 | ⭐⭐⭐⭐⭐ | 矩阵运算天然可并行 |
| **高内存带宽需求** | HBM 提供 TB/s 带宽 | ⭐⭐⭐⭐⭐ | 权重和激活值需要频繁读写 |
| **矩阵乘法为主** | Tensor Core 专用硬件 | ⭐⭐⭐⭐⭐ | 单周期完成矩阵块乘法 |
| **批处理模式** | SIMT 执行模型 | ⭐⭐⭐⭐⭐ | 相同操作作用于不同数据 |
| **容忍高延迟** | 延迟隐藏机制 | ⭐⭐⭐⭐ | 通过线程切换隐藏内存延迟 |
| **低精度容忍** | FP16/BF16/FP8 支持 | ⭐⭐⭐⭐⭐ | 降低带宽和计算需求 |

### 矩阵乘法的并行性分析

以 `C = A × B` 为例，其中 A 是 MxK 矩阵，B 是 KxN 矩阵：

```python
# 串行实现 - CPU 风格
for i in range(M):           # M 次循环
    for j in range(N):       # N 次循环
        for k in range(K):   # K 次循环
            C[i,j] += A[i,k] * B[k,j]
# 总操作: M × N × K 次乘加，串行执行

# 并行实现 - GPU 风格
# 每个线程计算 C 中的一个元素
# 需要 M × N 个线程
def gpu_kernel(i, j):
    sum = 0
    for k in range(K):
        sum += A[i,k] * B[k,j]
    C[i,j] = sum
# M × N 个线程并行执行
```

```
                    并行度分析
    ┌─────────────────────────────────────────┐
    │                                         │
    │   矩阵乘法 C[M×N] = A[M×K] × B[K×N]      │
    │                                         │
    │   可并行度:                              │
    │   ├── C 的每个元素可独立计算              │
    │   ├── 并行度 = M × N                    │
    │   └── 对于 4096×4096: 16M 并行度         │
    │                                         │
    │   GPU 优势:                              │
    │   ├── H100: ~16K CUDA Cores             │
    │   ├── 每个 SM 可调度 2048 线程            │
    │   └── 132 SM × 2048 = 270K 并发线程      │
    │                                         │
    │   结论: GPU 可充分利用矩阵乘法的并行性      │
    │                                         │
    └─────────────────────────────────────────┘
```

---

## GPU 计算的本质优势

### 1. 算力密度

```python
# 计算密度对比
def compute_density_analysis():
    """
    对比相同芯片面积下的计算能力
    """
    # CPU: Intel Xeon W-3375 (Ice Lake)
    cpu_area = 660  # mm²
    cpu_fp32_tflops = 2.3
    cpu_density = cpu_fp32_tflops / cpu_area * 1000  # GFLOPS/mm²
    
    # GPU: NVIDIA H100
    gpu_area = 814  # mm²
    gpu_fp32_tflops = 67
    gpu_density = gpu_fp32_tflops / gpu_area * 1000  # GFLOPS/mm²
    
    print(f"CPU 计算密度: {cpu_density:.1f} GFLOPS/mm²")
    print(f"GPU 计算密度: {gpu_density:.1f} GFLOPS/mm²")
    print(f"GPU 是 CPU 的 {gpu_density/cpu_density:.1f} 倍")

# 输出:
# CPU 计算密度: 3.5 GFLOPS/mm²
# GPU 计算密度: 82.3 GFLOPS/mm²
# GPU 是 CPU 的 23.5 倍
```

### 2. 内存带宽

```
┌─────────────────────────────────────────────────────────────────────┐
│                      内存带宽对比                                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   系统内存 (DDR5)                                                    │
│   ███░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  76.8 GB/s            │
│                                                                     │
│   CPU 内存 (DDR5-4800 8通道)                                        │
│   █████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  307 GB/s             │
│                                                                     │
│   GPU 内存 (A100 HBM2e)                                             │
│   ██████████████████████████░░░░░░░░░░░░░░░░  2,039 GB/s           │
│                                                                     │
│   GPU 内存 (H100 HBM3)                                              │
│   ██████████████████████████████████████░░░░  3,350 GB/s           │
│                                                                     │
│   GPU 内存 (B200 HBM3e)                                             │
│   ████████████████████████████████████████████████████  8,000 GB/s │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

为什么带宽如此重要？

```python
def bandwidth_importance():
    """
    以矩阵乘法为例说明带宽的重要性
    
    C[M×N] = A[M×K] × B[K×N]
    
    计算量: 2 × M × N × K FLOPs
    数据量: (M×K + K×N + M×N) × bytes_per_element
    
    计算强度 = FLOPs / Bytes
    """
    M, N, K = 4096, 4096, 4096
    bytes_per_elem = 2  # FP16
    
    flops = 2 * M * N * K
    bytes_needed = (M*K + K*N + M*N) * bytes_per_elem
    
    compute_intensity = flops / bytes_needed  # FLOPs/Byte
    
    # H100 specs (FP16 Tensor Core, dense, 不含稀疏)
    h100_tflops = 989.5  # FP16 Tensor Core (dense)
    h100_bandwidth = 3350  # GB/s
    
    # 达到峰值算力需要的计算强度
    required_intensity = h100_tflops * 1000 / h100_bandwidth
    
    print(f"矩阵乘法计算强度: {compute_intensity:.1f} FLOPs/Byte")
    print(f"H100 所需计算强度: {required_intensity:.1f} FLOPs/Byte")
    
    if compute_intensity >= required_intensity:
        print("→ 计算受限 (Compute Bound): 可充分利用 GPU 算力")
    else:
        print("→ 内存受限 (Memory Bound): 带宽是瓶颈")

# 输出:
# 矩阵乘法计算强度: 1365.3 FLOPs/Byte
# H100 所需计算强度: 295.4 FLOPs/Byte
# → 计算受限 (Compute Bound): 可充分利用 GPU 算力
```

### 3. 专用硬件加速

```
┌─────────────────────────────────────────────────────────────────────┐
│                    GPU 专用硬件单元                                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   ┌──────────────────────────────────────────────────────────────┐ │
│   │                     Tensor Core                               │ │
│   │                                                               │ │
│   │   专门为矩阵乘累加 (D = A×B + C) 设计                          │ │
│   │                                                               │ │
│   │   ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐  │ │
│   │   │ A (4×4) │  × │ B (4×4) │  + │ C (4×4) │  = │ D (4×4) │  │ │
│   │   │  FP16   │    │  FP16   │    │  FP32   │    │  FP32   │  │ │
│   │   └─────────┘    └─────────┘    └─────────┘    └─────────┘  │ │
│   │                                                               │ │
│   │   单周期完成: 64 FMA 操作 = 128 FLOPs                         │ │
│   │   对比 CUDA Core: 1 FMA = 2 FLOPs/周期                       │ │
│   │   加速比: 64x                                                 │ │
│   │                                                               │ │
│   └──────────────────────────────────────────────────────────────┘ │
│                                                                     │
│   ┌──────────────────────────────────────────────────────────────┐ │
│   │                     RT Core (Ray Tracing)                     │ │
│   │   用于光线追踪，AI 渲染中的降噪和超分辨率                        │ │
│   └──────────────────────────────────────────────────────────────┘ │
│                                                                     │
│   ┌──────────────────────────────────────────────────────────────┐ │
│   │                   Transformer Engine (H100+)                  │ │
│   │   自动管理 FP8 精度，动态缩放，为 Transformer 优化              │ │
│   └──────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## AI 工作负载特性分析

### 训练 vs 推理

```
┌─────────────────────────────────────────────────────────────────────┐
│                    训练 vs 推理工作负载                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   训练 (Training)                    推理 (Inference)               │
│   ─────────────                      ─────────────                  │
│                                                                     │
│   ┌───────────────────┐              ┌───────────────────┐         │
│   │   前向传播         │              │   前向传播         │         │
│   │   Forward Pass    │              │   Forward Pass    │         │
│   └─────────┬─────────┘              └───────────────────┘         │
│             │                                                       │
│   ┌─────────▼─────────┐                                            │
│   │   反向传播         │              只有前向传播                   │
│   │   Backward Pass   │                                            │
│   └─────────┬─────────┘                                            │
│             │                                                       │
│   ┌─────────▼─────────┐                                            │
│   │   参数更新         │                                            │
│   │   Weight Update   │                                            │
│   └───────────────────┘                                            │
│                                                                     │
│   特点:                              特点:                          │
│   • 大 batch size (高吞吐)           • 小 batch size (低延迟)        │
│   • 计算密集 (Compute Bound)         • 内存密集 (Memory Bound)       │
│   • 需要完整模型+梯度+优化器          • 只需要模型参数                 │
│   • 允许较高延迟                      • 严格延迟要求                   │
│   • FP16/BF16 混合精度               • INT8/FP8 量化                 │
│                                                                     │
│   显存需求:                          显存需求:                       │
│   模型 + 梯度 + 优化器 + 激活值       模型 + KV Cache                 │
│   ≈ 16-20x 参数量 (FP16+AdamW)       ≈ 2x 参数量 (FP16)             │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 不同模型类型的 GPU 需求

| 模型类型 | 计算特点 | GPU 需求重点 | 典型应用 |
|----------|----------|--------------|----------|
| **CNN** | 卷积运算、局部连接 | 算力、内存带宽 | 图像分类、目标检测 |
| **RNN/LSTM** | 序列依赖、难并行 | 显存、时钟频率 | 时序预测 |
| **Transformer** | 大矩阵乘、注意力 | 显存、带宽、Tensor Core | LLM、Vision Transformer |
| **GNN** | 稀疏运算、不规则访问 | 内存带宽、随机访问 | 推荐系统、分子模拟 |
| **Diffusion** | 多次前向、U-Net | 算力、显存 | 图像生成 |

### LLM 的特殊需求

```python
def llm_memory_analysis(
    params_billion: float,
    seq_length: int = 4096,
    batch_size: int = 1,
    precision: str = "fp16"
):
    """
    分析 LLM 推理的显存需求
    """
    bytes_per_param = 2 if precision == "fp16" else 1 if precision == "int8" else 4
    
    # 模型参数
    model_memory_gb = params_billion * 1e9 * bytes_per_param / 1e9
    
    # KV Cache (假设 32 层，head_dim=128，num_heads=32)
    num_layers = 32
    hidden_dim = 4096
    kv_per_token = 2 * num_layers * hidden_dim * bytes_per_param  # K + V
    kv_cache_gb = batch_size * seq_length * kv_per_token / 1e9
    
    # 激活值 (中间计算)
    activation_gb = batch_size * seq_length * hidden_dim * 4 * bytes_per_param / 1e9
    
    total_gb = model_memory_gb + kv_cache_gb + activation_gb
    
    print(f"模型参数: {model_memory_gb:.1f} GB")
    print(f"KV Cache: {kv_cache_gb:.1f} GB")
    print(f"激活值:   {activation_gb:.1f} GB")
    print(f"总计:     {total_gb:.1f} GB")
    
    return total_gb

# 7B 模型分析
print("=== 7B 模型 (FP16) ===")
llm_memory_analysis(7, seq_length=4096)

# 70B 模型分析
print("\n=== 70B 模型 (FP16) ===")
llm_memory_analysis(70, seq_length=4096)
```

---

## GPU vs 其他加速器

### 加速器生态对比

```
┌─────────────────────────────────────────────────────────────────────┐
│                    AI 加速器对比                                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   NVIDIA GPU                                                        │
│   ├── 优势: 生态成熟、通用性强、工具链完善                             │
│   ├── 劣势: 价格高、功耗大                                           │
│   └── 适用: 通用 AI 训练/推理                                        │
│                                                                     │
│   Google TPU                                                        │
│   ├── 优势: 矩阵乘法极致优化、云原生                                   │
│   ├── 劣势: 只能通过 GCP 使用、灵活性差                               │
│   └── 适用: 大规模 Transformer 训练                                  │
│                                                                     │
│   AMD GPU (MI300X)                                                  │
│   ├── 优势: 显存更大 (192GB)、性价比                                  │
│   ├── 劣势: 软件生态弱、兼容性问题                                    │
│   └── 适用: 内存受限的大模型                                         │
│                                                                     │
│   Intel Gaudi                                                       │
│   ├── 优势: 性价比、与 Intel 生态集成                                 │
│   ├── 劣势: 软件生态不成熟                                           │
│   └── 适用: Intel 技术栈用户                                         │
│                                                                     │
│   Cerebras WSE                                                      │
│   ├── 优势: 超大芯片、无需模型并行                                    │
│   ├── 劣势: 极其昂贵、特殊场景                                       │
│   └── 适用: 超大模型研究                                             │
│                                                                     │
│   Apple Silicon (M系列)                                             │
│   ├── 优势: 统一内存、能效比高                                       │
│   ├── 劣势: 算力有限、专业支持少                                      │
│   └── 适用: 本地推理、小规模实验                                      │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 为什么 NVIDIA GPU 仍是首选

```
                    NVIDIA 生态护城河
    ┌─────────────────────────────────────────┐
    │                                         │
    │   1. CUDA 生态                          │
    │      └─ 15+ 年积累，数百万开发者          │
    │                                         │
    │   2. 框架支持                            │
    │      └─ PyTorch/TensorFlow 首选支持      │
    │                                         │
    │   3. 优化库                              │
    │      └─ cuDNN, cuBLAS, TensorRT...      │
    │                                         │
    │   4. 模型支持                            │
    │      └─ 几乎所有预训练模型默认 CUDA       │
    │                                         │
    │   5. 调试工具                            │
    │      └─ Nsight, nvprof, cuda-gdb        │
    │                                         │
    │   6. 社区资源                            │
    │      └─ 教程、论坛、Stack Overflow       │
    │                                         │
    │   7. 企业支持                            │
    │      └─ DGX, NGC, 企业级支持              │
    │                                         │
    └─────────────────────────────────────────┘
```

---

## 实战练习

### 练习 1：验证 GPU 加速效果

```python
import torch
import time

def compare_cpu_gpu(size=10000, iterations=100):
    """
    对比 CPU 和 GPU 的矩阵乘法性能
    """
    # CPU 测试
    a_cpu = torch.randn(size, size)
    b_cpu = torch.randn(size, size)
    
    start = time.time()
    for _ in range(iterations):
        c_cpu = torch.matmul(a_cpu, b_cpu)
    cpu_time = time.time() - start
    
    # GPU 测试
    if torch.cuda.is_available():
        a_gpu = torch.randn(size, size, device='cuda')
        b_gpu = torch.randn(size, size, device='cuda')
        
        # 预热
        torch.matmul(a_gpu, b_gpu)
        torch.cuda.synchronize()
        
        start = time.time()
        for _ in range(iterations):
            c_gpu = torch.matmul(a_gpu, b_gpu)
        torch.cuda.synchronize()
        gpu_time = time.time() - start
        
        print(f"矩阵大小: {size}×{size}")
        print(f"CPU 时间: {cpu_time:.3f}s")
        print(f"GPU 时间: {gpu_time:.3f}s")
        print(f"加速比:   {cpu_time/gpu_time:.1f}x")
    else:
        print("CUDA 不可用")

# 运行测试
compare_cpu_gpu(size=4096, iterations=10)
```

### 练习 2：探索 GPU 属性

```python
import torch

def explore_gpu():
    """
    探索 GPU 的详细属性
    """
    if not torch.cuda.is_available():
        print("CUDA 不可用")
        return
    
    device = torch.cuda.current_device()
    props = torch.cuda.get_device_properties(device)
    
    print("=" * 50)
    print(f"GPU: {props.name}")
    print("=" * 50)
    
    print(f"\n[计算能力]")
    print(f"  计算能力:         {props.major}.{props.minor}")
    print(f"  SM 数量:          {props.multi_processor_count}")
    print(f"  每 SM 最大线程:    {props.max_threads_per_multi_processor}")
    print(f"  每 block 最大线程: {props.max_threads_per_block}")
    
    print(f"\n[内存]")
    print(f"  总显存:           {props.total_memory / 1024**3:.1f} GB")
    print(f"  每 SM 共享内存:    {props.max_shared_memory_per_multiprocessor / 1024:.0f} KB")
    
    print(f"\n[其他]")
    print(f"  时钟频率:         {props.clock_rate / 1e6:.2f} GHz")
    print(f"  Warp 大小:        {props.warp_size}")
    
    # 检查 Tensor Core 支持
    if props.major >= 7:
        print(f"\n[Tensor Core]")
        print(f"  支持 Tensor Core:  ✓ (计算能力 >= 7.0)")
    
    # 当前显存使用
    print(f"\n[当前状态]")
    print(f"  已分配:           {torch.cuda.memory_allocated() / 1024**2:.1f} MB")
    print(f"  已缓存:           {torch.cuda.memory_reserved() / 1024**2:.1f} MB")

explore_gpu()
```

### 练习 3：理解批处理的重要性

```python
import torch
import time

def batch_size_experiment(model_dim=1024, seq_length=512):
    """
    演示批处理大小对 GPU 利用率的影响
    """
    if not torch.cuda.is_available():
        print("CUDA 不可用")
        return
    
    # 模拟简单的 Transformer 层
    linear1 = torch.nn.Linear(model_dim, 4 * model_dim, device='cuda')
    linear2 = torch.nn.Linear(4 * model_dim, model_dim, device='cuda')
    
    batch_sizes = [1, 2, 4, 8, 16, 32, 64]
    
    print(f"模型维度: {model_dim}, 序列长度: {seq_length}")
    print("-" * 50)
    
    for batch_size in batch_sizes:
        x = torch.randn(batch_size, seq_length, model_dim, device='cuda')
        
        # 预热
        _ = linear2(torch.relu(linear1(x)))
        torch.cuda.synchronize()
        
        # 计时
        start = time.time()
        iterations = 100
        for _ in range(iterations):
            y = linear2(torch.relu(linear1(x)))
        torch.cuda.synchronize()
        elapsed = time.time() - start
        
        throughput = batch_size * iterations / elapsed
        print(f"Batch={batch_size:3d}: {throughput:8.1f} samples/s, "
              f"每 batch 时间: {elapsed/iterations*1000:.2f} ms")

batch_size_experiment()
```

---

## 小结

### 核心要点

1. **设计哲学差异**：CPU 优化延迟，GPU 优化吞吐
2. **AI 天然适合 GPU**：矩阵运算的大规模并行性
3. **带宽至关重要**：HBM 提供的高带宽是 GPU 的关键优势
4. **专用硬件加速**：Tensor Core 提供数十倍的矩阵运算加速
5. **生态系统护城河**：NVIDIA CUDA 生态是当前最成熟的选择

### 下一步

理解了为什么需要 GPU 后，接下来学习 [GPU 架构演进](02-architecture-evolution.md)，了解 NVIDIA GPU 如何一步步针对 AI 工作负载进行优化。

---

*下一篇：[02-architecture-evolution.md](02-architecture-evolution.md) - GPU 架构演进*

---

## 参考资料与引用

1. **Hennessy, J. L., & Patterson, D. A. (2019).** *Computer Architecture: A Quantitative Approach*, 6th Edition. — CPU vs GPU 架构对比  
   https://www.elsevier.com/books/computer-architecture/hennessy/978-0-12-811905-1

2. **NVIDIA.** *CUDA C++ Programming Guide.* — CUDA 并行编程模型  
   https://docs.nvidia.com/cuda/cuda-c-programming-guide/

3. **Jouppi, N. P., et al. (2017).** *In-Datacenter Performance Analysis of a Tensor Processing Unit.* ISCA 2017. — TPU vs GPU 对比  
   https://arxiv.org/abs/1704.04760

4. **NVIDIA.** *A100 Tensor Core GPU Architecture Whitepaper.*  
   https://www.nvidia.com/content/dam/en-zz/Solutions/Data-Center/nvidia-ampere-architecture-whitepaper.pdf

5. **Raina, R., Madhavan, A., & Ng, A. Y. (2009).** *Large-scale Deep Unsupervised Learning using Graphics Processors.* ICML 2009. — GPU 深度学习先驱工作  
   https://dl.acm.org/doi/10.1145/1553374.1553486
