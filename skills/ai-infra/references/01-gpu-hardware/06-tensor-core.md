# Tensor Core 详解

> 理解 Tensor Core 的工作原理，掌握如何在 AI 应用中使用它。

## 目录

- [什么是 Tensor Core](#什么是-tensor-core)
- [MMA 操作原理](#mma-操作原理)
- [数据类型支持](#数据类型支持)
- [使用方法](#使用方法)
- [Transformer Engine](#transformer-engine)
- [实战练习](#实战练习)

---

## 什么是 Tensor Core

Tensor Core 是 NVIDIA GPU 中专门为**矩阵乘累加 (Matrix Multiply-Accumulate, MMA)** 设计的硬件单元。

### 与 CUDA Core 的对比

```
CUDA Core (标量运算):
每周期: 1 FMA = 2 FLOPs

Tensor Core (矩阵运算):
每周期: 64+ FMA = 128+ FLOPs (取决于架构)

加速比: 64x+
```

### Tensor Core 价值

| 场景 | CUDA Core | Tensor Core | 加速 |
|------|-----------|-------------|------|
| 矩阵乘法 | 基准 | 8-16x | ✅ |
| Transformer | 基准 | 8-16x | ✅ |
| 卷积 | 基准 | 8-16x | ✅ |
| 逐元素 | 基准 | 不适用 | - |

---

## MMA 操作原理

### 基本操作

```
D = A × B + C

┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐
│  A      │ × │  B      │ + │  C      │ = │  D      │
│ (M×K)   │   │ (K×N)   │   │ (M×N)   │   │ (M×N)   │
│ 输入    │   │ 输入    │   │ 累加器  │   │ 输出    │
└─────────┘   └─────────┘   └─────────┘   └─────────┘
```

### 各代 Tensor Core 矩阵块大小

| 架构 | 矩阵块大小 | 每次 FLOPs |
|------|-----------|------------|
| Volta | 4×4×4 | 128 (64 FMA) |
| Ampere | 8×8×4 | 512 (256 FMA) |
| Hopper | 16×8×16 | 4096 (2048 FMA) |

### 执行示意

```
Volta Tensor Core 4×4×4 MMA:

A[4×4]          B[4×4]          C[4×4]
┌───┬───┬───┬───┐  ┌───┬───┬───┬───┐  ┌───┬───┬───┬───┐
│a00│a01│a02│a03│  │b00│b01│b02│b03│  │c00│c01│c02│c03│
├───┼───┼───┼───┤  ├───┼───┼───┼───┤  ├───┼───┼───┼───┤
│a10│a11│a12│a13│× │b10│b11│b12│b13│+ │c10│c11│c12│c13│
├───┼───┼───┼───┤  ├───┼───┼───┼───┤  ├───┼───┼───┼───┤
│a20│a21│a22│a23│  │b20│b21│b22│b23│  │c20│c21│c22│c23│
├───┼───┼───┼───┤  ├───┼───┼───┼───┤  ├───┼───┼───┼───┤
│a30│a31│a32│a33│  │b30│b31│b32│b33│  │c30│c31│c32│c33│
└───┴───┴───┴───┘  └───┴───┴───┴───┘  └───┴───┴───┴───┘

单周期完成: 64 FMA = 128 FLOPs
```

---

## 数据类型支持

### 各架构支持的数据类型

| 架构 | FP64 | TF32 | FP16 | BF16 | FP8 | INT8 | INT4 |
|------|------|------|------|------|-----|------|------|
| Volta | - | - | ✅ | - | - | ✅ | - |
| Ampere | ✅ | ✅ | ✅ | ✅ | - | ✅ | ✅ |
| Hopper | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Blackwell | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |

### 数据类型详解

```
FP32:  [1][8 exp][23 mantissa] = 32 bits  - 精度最高
TF32:  [1][8 exp][10 mantissa] = 19 bits  - FP32 范围，降低精度
FP16:  [1][5 exp][10 mantissa] = 16 bits  - 标准半精度
BF16:  [1][8 exp][ 7 mantissa] = 16 bits  - FP32 范围，7-bit 尾数
FP8 E4M3: [1][4 exp][3 mantissa] = 8 bits - 前向传播(权重/激活), 范围±448
FP8 E5M2: [1][5 exp][2 mantissa] = 8 bits - 反向传播(梯度), 范围±57344
```

### 混合精度策略

```
典型训练配置:
输入/权重: FP16 或 BF16
累加器: FP32
主权重: FP32 (优化器状态)

内存节省: 约 50%
速度提升: 2-8x
```

---

## 使用方法

### PyTorch 自动混合精度

```python
import torch

# 方式 1: AMP autocast
model = MyModel().cuda()
optimizer = torch.optim.AdamW(model.parameters())
scaler = torch.cuda.amp.GradScaler()

for data, target in dataloader:
    optimizer.zero_grad()
    
    # 自动混合精度前向
    with torch.cuda.amp.autocast():
        output = model(data)
        loss = criterion(output, target)
    
    # 缩放后反向传播
    scaler.scale(loss).backward()
    scaler.step(optimizer)
    scaler.update()
```

### 手动指定数据类型

```python
# 手动使用 FP16
a = torch.randn(1024, 1024, device='cuda', dtype=torch.float16)
b = torch.randn(1024, 1024, device='cuda', dtype=torch.float16)
c = torch.matmul(a, b)  # 自动使用 Tensor Core

# 使用 BF16
a = torch.randn(1024, 1024, device='cuda', dtype=torch.bfloat16)
b = torch.randn(1024, 1024, device='cuda', dtype=torch.bfloat16)
c = torch.matmul(a, b)
```

### TF32 设置 (Ampere+)

```python
# TF32 默认开启
# FP32 输入自动使用 TF32 加速

# 显式控制
torch.backends.cuda.matmul.allow_tf32 = True   # 矩阵乘法
torch.backends.cudnn.allow_tf32 = True         # cuDNN 操作

# 禁用 (需要严格 FP32 精度时)
torch.backends.cuda.matmul.allow_tf32 = False
```

### Tensor Core 使用条件

```
Tensor Core 激活条件:
1. 矩阵维度是 8 的倍数 (FP16) 或 16 的倍数 (INT8)
2. 数据类型是 FP16/BF16/TF32/INT8/FP8
3. 使用 cuBLAS/cuDNN 后端
4. 内存对齐 (256 bytes)

PyTorch 自动处理大部分情况，无需手动对齐
```

---

## Transformer Engine

### 什么是 Transformer Engine

Transformer Engine (TE) 是 H100 引入的专门针对 Transformer 架构的优化引擎。

### 核心特性

```
1. 自动 FP8 管理
   - 动态选择 E4M3 或 E5M2
   - 自动缩放因子调整
   - 无需手动管理精度

2. 融合操作
   - LayerNorm + Linear 融合
   - Attention 优化
   - 减少内存带宽需求

3. 兼容性
   - 支持 PyTorch/JAX
   - Drop-in replacement
```

### 使用示例

```python
import transformer_engine.pytorch as te

# 替换标准 Linear 层
# 原始
layer = torch.nn.Linear(1024, 1024)
# TE 版本
layer = te.Linear(1024, 1024, bias=True)

# FP8 训练
model = te.TransformerLayer(...)

with te.fp8_autocast(enabled=True):
    output = model(input)
```

### TE 支持的模块

| 模块 | 说明 |
|------|------|
| `te.Linear` | FP8 线性层 |
| `te.LayerNorm` | 融合 LayerNorm |
| `te.TransformerLayer` | 完整 Transformer 层 |
| `te.MultiheadAttention` | 多头注意力 |

---

## 实战练习

### 练习 1：Tensor Core 性能对比

```python
import torch
import time

def tensor_core_benchmark(size=4096, iterations=100):
    results = {}
    
    for dtype in [torch.float32, torch.float16, torch.bfloat16]:
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
        
        flops = 2 * size**3 * iterations
        tflops = flops / elapsed / 1e12
        results[str(dtype)] = tflops
        
    print(f"矩阵大小: {size}×{size}")
    for dtype, tflops in results.items():
        print(f"  {dtype:20}: {tflops:.1f} TFLOPS")
    
    # 加速比
    fp32 = results['torch.float32']
    fp16 = results['torch.float16']
    print(f"FP16 vs FP32 加速比: {fp16/fp32:.1f}x")

tensor_core_benchmark()
```

### 练习 2：混合精度训练

```python
import torch
import torch.nn as nn

def amp_training_example():
    # 简单模型
    model = nn.Sequential(
        nn.Linear(1024, 2048),
        nn.ReLU(),
        nn.Linear(2048, 1024),
    ).cuda()
    
    optimizer = torch.optim.AdamW(model.parameters())
    scaler = torch.cuda.amp.GradScaler()
    
    # 模拟数据
    data = torch.randn(64, 1024, device='cuda')
    target = torch.randn(64, 1024, device='cuda')
    
    # 标准训练
    torch.cuda.synchronize()
    start = time.time()
    for _ in range(100):
        optimizer.zero_grad()
        output = model(data)
        loss = ((output - target) ** 2).mean()
        loss.backward()
        optimizer.step()
    torch.cuda.synchronize()
    fp32_time = time.time() - start
    
    # AMP 训练
    torch.cuda.synchronize()
    start = time.time()
    for _ in range(100):
        optimizer.zero_grad()
        with torch.cuda.amp.autocast():
            output = model(data)
            loss = ((output - target) ** 2).mean()
        scaler.scale(loss).backward()
        scaler.step(optimizer)
        scaler.update()
    torch.cuda.synchronize()
    amp_time = time.time() - start
    
    print(f"FP32 训练: {fp32_time:.3f}s")
    print(f"AMP 训练:  {amp_time:.3f}s")
    print(f"加速比: {fp32_time/amp_time:.2f}x")

amp_training_example()
```

---

## 小结

- **Tensor Core 是 AI 加速关键**：专用矩阵运算硬件，比 CUDA Core 快数十倍
- **数据类型进化**：FP32 → FP16 → BF16 → FP8 → FP4
- **使用简单**：PyTorch AMP 自动管理，维度满足条件即可
- **Transformer Engine**：H100+ 专用优化，自动管理 FP8

---

*下一篇：[07-multi-gpu-interconnect.md](07-multi-gpu-interconnect.md) - 多卡互联技术*
