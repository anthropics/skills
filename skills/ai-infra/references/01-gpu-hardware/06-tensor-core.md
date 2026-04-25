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

### 生活类比：计算器 vs 乘法表

```
CUDA Core 做矩阵乘法 = 用计算器逐个算每个乘法

  要算 4×4 矩阵乘法 → 64 次乘加
  一个 CUDA Core 每周期 1 次乘加 → 64 周期

Tensor Core 做矩阵乘法 = 直接查一张"矩阵乘法表"

  4×4 矩阵乘法 → 1 周期搞定！
  因为硬件里集成了专门的"矩阵乘法电路"
  不是一个一个算，而是所有元素同时算

这就像：
  CPU 做加法 → 用通用 ALU 电路，一次一个
  GPU Tensor Core → 用专用矩阵电路，一次一整块

代价：只能做矩阵乘累加 (D = A×B+C)，不能做其他计算
好处：矩阵乘法恰好是深度学习 90%+ 的计算量
```

### 与 CUDA Core 的性能对比

```
CUDA Core (标量运算):
  每周期: 1 FMA (fused multiply-add) = 2 FLOPs

Tensor Core (矩阵运算):
  每周期: 64~2048 FMA = 128~4096 FLOPs (取决于架构和精度)

实际加速比（H100 为例）:
  FP32 (CUDA Core): 67 TFLOPS
  FP16 (Tensor Core): 1,979 TFLOPS → 29.5x 加速！
  FP8 (Tensor Core):  3,958 TFLOPS → 59x 加速！

为什么 AI 社区如此重视 Tensor Core？
  因为 Transformer 的核心操作——注意力和 FFN——都是矩阵乘法
  Tensor Core 直接决定了 LLM 的训练和推理速度
```

---

## MMA 操作原理

### 基本操作

```
MMA = Matrix Multiply-Accumulate

D = A × B + C

┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐
│  A      │ × │  B      │ + │  C      │ = │  D      │
│ (M×K)   │   │ (K×N)   │   │ (M×N)   │   │ (M×N)   │
│ 低精度  │   │ 低精度  │   │ 高精度  │   │ 高精度  │
│(FP16等) │   │(FP16等) │   │(FP32)   │   │(FP32)   │
└─────────┘   └─────────┘   └─────────┘   └─────────┘

为什么叫"乘累加"？
  大矩阵乘法是分块进行的：
  C = A₁×B₁ + A₂×B₂ + ... + Aₖ×Bₖ
  每次 Tensor Core 计算一小块，结果累加到 C 上
  "累加"用高精度（FP32）→ 保证最终结果的精度
```

### 各代 Tensor Core 的进化

```
Volta (2017) — 第 1 代
  矩阵块: 4×4×4
  每次: 64 FMA = 128 FLOPs
  支持: FP16 输入, FP32 累加
  类比: 学会了查 4×4 乘法表

Ampere (2020) — 第 3 代
  矩阵块: 扩大到 8×8×4 (和更多格式)
  每次: 256 FMA = 512 FLOPs → 4x 提升
  新增: TF32, BF16, INT8, INT4, 结构化稀疏 (2:4)
  类比: 乘法表更大了，还学会了跳过零值

Hopper (2022) — 第 4 代
  矩阵块: 16×8×16 (FP16), 16×8×32 (FP8)
  每次: 最高 2048 FMA = 4096 FLOPs → 再翻 8x
  新增: FP8 (E4M3/E5M2), DPX 指令
  革命: 引入异步数据搬运 (TMA) + wgmma 指令
  类比: 不仅乘法表更大，还有专职搬运工提前备料

Blackwell (2024) — 第 5 代
  新增: FP4, 微张量缩放
  配合双芯封装：总算力再翻倍
```

### Warp 级别的 MMA 执行

```
一个 Tensor Core 操作实际由一整个 Warp (32 线程) 协作完成

以 Volta 4×4×4 MMA 为例：

  32 个线程分工：
  Thread 0-7:   持有 A 矩阵的 4 行（每人一部分）
  Thread 8-15:  持有 B 矩阵的 4 列
  Thread 16-31: 持有 C/D 矩阵的不同元素

  Tensor Core 一次操作：
  所有线程同时把数据喂给 Tensor Core 硬件
  → 一周期输出完整的 4×4 结果

这也解释了 Tensor Core 的使用条件：
  - 必须以 Warp 为单位调用（不能单线程调用）
  - 矩阵维度必须对齐到特定值（4/8/16 的倍数）
  - 数据需要按特定 layout 排列在线程的寄存器中
```

---

## 数据类型支持

### 精度格式对比

```
每种格式都是"范围"和"精度"的权衡：

FP32:    [1 sign][8 exp][23 mantissa] = 32 bits
  范围: ±3.4×10³⁸, 精度: 7 位有效数字
  用途: 传统训练的默认，优化器状态

TF32:    [1 sign][8 exp][10 mantissa] = 19 bits (内部使用)
  范围: 同 FP32, 精度: ~4 位有效数字
  用途: Ampere+ 自动加速 FP32 矩阵乘法

FP16:    [1 sign][5 exp][10 mantissa] = 16 bits
  范围: ±65504, 精度: ~4 位有效数字
  用途: 混合精度训练，推理
  注意: 范围较小，大梯度可能溢出 → 需要 loss scaling

BF16:    [1 sign][8 exp][ 7 mantissa] = 16 bits
  范围: 同 FP32(大！), 精度: ~3 位有效数字
  用途: 训练首选（不需要 loss scaling）
  类比: FP32 的"缩略版"，保留了范围

FP8 E4M3: [1 sign][4 exp][3 mantissa] = 8 bits
  范围: ±448, 精度: ~2 位
  用途: H100+ 前向传播

FP8 E5M2: [1 sign][5 exp][2 mantissa] = 8 bits
  范围: ±57344, 精度: ~1 位
  用途: H100+ 反向传播（梯度）

FP4:     [1 sign][2 exp][1 mantissa] = 4 bits
  范围: 极小, 需要 per-group 缩放因子
  用途: B200+ 推理
```

### 为什么低精度训练能工作？

```
直觉上：精度降低 → 信息丢失 → 模型变差？

实际上：

1. 深度学习本身是"近似计算"
   - 梯度下降本身就是估计（mini-batch 采样）
   - 少量噪声反而有正则化效果（类似 Dropout）

2. 关键是"累加用高精度"
   - A(FP16) × B(FP16) → 中间结果用 FP32 累加
   - 最终权重更新在 FP32 精度下进行
   - 只有矩阵乘法内部用低精度，全局精度不丢失

3. BF16 的范围保证
   - BF16 和 FP32 有相同的指数位 → 不会溢出
   - Google 训练 PaLM、Meta 训练 LLaMA 都用 BF16
   - 已经在数千个模型上验证

数值对比：
  FP32: 0.123456789 → 0.123456789（精确）
  FP16: 0.123456789 → 0.12347（4位有效数字）
  BF16: 0.123456789 → 0.1235（3位有效数字）
  FP8:  0.123456789 → 0.125（2位有效数字）

对模型训练的影响通常在 0.1% 以内
但速度提升是 2-4 倍！
```

### 各架构支持矩阵

| 架构 | FP64 | TF32 | FP16 | BF16 | FP8 | INT8 | INT4 | FP4 |
|------|------|------|------|------|-----|------|------|-----|
| Volta | - | - | ✅ | - | - | ❌ | - | - |
| Ampere | ✅ | ✅ | ✅ | ✅ | - | ✅ | ✅ | - |
| Hopper | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | - |
| Blackwell | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |

---

## 使用方法

### PyTorch 自动混合精度 (AMP)

```python
import torch

# AMP 是使用 Tensor Core 最简单的方式
# 原理：自动选择每个操作的最优精度
#   矩阵乘法 → FP16/BF16 (Tensor Core)
#   损失计算 → FP32 (精度敏感)
#   BatchNorm → FP32 (精度敏感)

model = MyModel().cuda()
optimizer = torch.optim.AdamW(model.parameters())
scaler = torch.amp.GradScaler()  # 梯度缩放器

for data, target in dataloader:
    optimizer.zero_grad()
    
    # autocast 自动管理精度
    with torch.amp.autocast(device_type="cuda"):
        output = model(data)
        loss = criterion(output, target)
    
    # GradScaler 防止 FP16 梯度下溢
    scaler.scale(loss).backward()
    scaler.step(optimizer)
    scaler.update()
```

### GradScaler 为什么必要？

```
问题：FP16 的最小非零值是 ~6×10⁻⁸
  如果梯度 < 6×10⁻⁸ → 下溢为 0 → 参数不更新 → 训练卡住

解决：GradScaler
  1. 前向：正常计算 loss
  2. 缩放：loss × scale_factor (如 65536)
  3. 反向：梯度也被放大 65536 倍 → 不会下溢
  4. 更新前：梯度 / scale_factor → 恢复真实值
  5. 动态调整 scale_factor（太大会溢出 → 减半，太小无效 → 翻倍）

BF16 通常不需要 GradScaler（范围与 FP32 相同）
但 FP16 训练必须用！
```

### TF32 设置 (Ampere+)

```python
# TF32 在 Ampere+ 上默认开启
# FP32 的矩阵乘法自动用 TF32 在 Tensor Core 执行

# 显式控制
torch.backends.cuda.matmul.allow_tf32 = True   # 矩阵乘法用 TF32
torch.backends.cudnn.allow_tf32 = True         # cuDNN 操作用 TF32

# 关闭 TF32（需要严格 FP32 精度时，如科学计算）
torch.backends.cuda.matmul.allow_tf32 = False
# 注意：即使设置 dtype=float32，如果 allow_tf32=True
# 矩阵乘法内部仍会用 TF32 → 结果可能有微小差异
```

### 确保 Tensor Core 被使用的检查清单

```
1. 数据类型正确:
   ✅ FP16, BF16, TF32, FP8, INT8
   ❌ FP64, FP32(未开 TF32)

2. 矩阵维度对齐:
   ✅ 维度是 8 的倍数 (FP16/BF16)
   ✅ 维度是 16 的倍数 (INT8)
   ❌ 任意维度（可能回退到 CUDA Core）

3. 使用正确的后端:
   ✅ cuBLAS (torch.matmul)
   ✅ cuDNN (Conv2d, BatchNorm)
   ❌ 自定义 CUDA kernel（除非手写 wmma/mma 指令）

验证方法：
  用 Nsight Compute 查看 kernel 的 Tensor Core 使用比例
  ncu --metrics sm__pipe_tensor_cycles_active python test.py
```

---

## Transformer Engine

### 什么是 Transformer Engine

Transformer Engine (TE) 是 H100 引入的专门针对 Transformer 的优化引擎，解决的核心问题是**自动 FP8 精度管理**。

```
没有 TE 时使用 FP8 的困难：

1. 每一层的激活值范围不同
   Layer 0 的输出范围: [-0.5, 0.5]
   Layer 31 的输出范围: [-50, 50]
   → 同一个 FP8 格式不能同时表示两者

2. 训练过程中范围会变化
   epoch 0: 梯度范围 [0.001, 0.1]
   epoch 10: 梯度范围 [0.00001, 0.01]
   → 固定的缩放因子会失效

Transformer Engine 的解决方案：
  为每个操作维护一个"缩放因子"(scaling factor)
  每 N 步根据实际数据范围动态更新
  自动选择 E4M3 (精度优先) 或 E5M2 (范围优先)
```

### 使用示例

```python
import transformer_engine.pytorch as te

# 替换标准层 → 自动获得 FP8 加速
# 原始
layer = torch.nn.Linear(1024, 1024)
# TE 版本
layer = te.Linear(1024, 1024, bias=True)

# 完整 Transformer 层
model = te.TransformerLayer(
    hidden_size=4096,
    ffn_hidden_size=11008,
    num_attention_heads=32,
    layernorm_epsilon=1e-5,
)

# FP8 训练——就这一行
with te.fp8_autocast(enabled=True):
    output = model(input)
    
# TE 内部自动完成：
# 1. 选择 FP8 格式 (E4M3 for weights, E5M2 for grads)
# 2. 计算缩放因子
# 3. 量化输入 → FP8 计算 → 反量化输出
# 4. 动态调整缩放因子
```

### TE 的融合优化

```
TE 不仅管 FP8，还做算子融合：

标准 PyTorch:
  x = LayerNorm(x)     # kernel 1: 读 x, 写归一化结果
  x = Linear(x)        # kernel 2: 读归一化结果, 写线性变换
  → 中间结果写回 HBM 再读出，浪费带宽

TE 融合版:
  x = te.LayerNormLinear(x)  # 一个 kernel 完成两步
  → 归一化结果在 register/shared memory 中直接传给 Linear
  → 减少 HBM 读写，减少 kernel 启动开销

支持的融合模块:
  te.LayerNormLinear      = LayerNorm + Linear
  te.LayerNormMLP         = LayerNorm + MLP (up + activation + down)
  te.MultiheadAttention   = 融合注意力计算
```

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
        
        torch.matmul(a, b)  # 预热
        torch.cuda.synchronize()
        
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
    
    fp32 = results['torch.float32']
    fp16 = results['torch.float16']
    bf16 = results['torch.bfloat16']
    print(f"\n加速比:")
    print(f"  FP16 vs FP32: {fp16/fp32:.1f}x")
    print(f"  BF16 vs FP32: {bf16/fp32:.1f}x")
    # 如果 FP16/BF16 接近 FP32 → TF32 已开启
    # 如果 FP16/BF16 远大于 FP32 → TF32 未开启
    
    # 测试 TF32 的影响
    torch.backends.cuda.matmul.allow_tf32 = False
    a32 = torch.randn(size, size, device='cuda', dtype=torch.float32)
    b32 = torch.randn(size, size, device='cuda', dtype=torch.float32)
    torch.matmul(a32, b32)
    torch.cuda.synchronize()
    
    start = time.time()
    for _ in range(iterations):
        torch.matmul(a32, b32)
    torch.cuda.synchronize()
    fp32_no_tf32 = 2 * size**3 * iterations / (time.time() - start) / 1e12
    
    torch.backends.cuda.matmul.allow_tf32 = True
    print(f"\n  FP32 (无 TF32): {fp32_no_tf32:.1f} TFLOPS")
    print(f"  FP32 (有 TF32): {fp32:.1f} TFLOPS")
    print(f"  TF32 加速: {fp32/fp32_no_tf32:.1f}x")

tensor_core_benchmark()
```

### 练习 2：维度对齐的影响

```python
def alignment_benchmark():
    """矩阵维度是否对齐到 8 的倍数对性能的影响"""
    iterations = 100
    dtype = torch.float16
    
    for size in [1000, 1024, 2000, 2048, 4000, 4096]:
        a = torch.randn(size, size, device='cuda', dtype=dtype)
        b = torch.randn(size, size, device='cuda', dtype=dtype)
        torch.matmul(a, b)
        torch.cuda.synchronize()
        
        start = time.time()
        for _ in range(iterations):
            torch.matmul(a, b)
        torch.cuda.synchronize()
        elapsed = time.time() - start
        
        flops = 2 * size**3 * iterations
        tflops = flops / elapsed / 1e12
        aligned = "✅ 对齐" if size % 8 == 0 else "❌ 未对齐"
        print(f"  {size:5d} × {size:5d} {aligned}: {tflops:.1f} TFLOPS")

print("维度对齐影响测试 (FP16):")
alignment_benchmark()
```

---

## 小结

```
Tensor Core 核心知识：

1. 本质: 矩阵乘累加的专用硬件，比 CUDA Core 快 10-60 倍
   代价是只能做 D = A×B+C 这一种运算

2. 低精度 + 高精度累加 = AI 训练的精髓
   输入 FP16/BF16/FP8（省带宽），累加 FP32（保精度）

3. 使用条件:
   - 数据类型正确 (FP16/BF16/TF32/FP8)
   - 维度对齐 (8 的倍数)
   - 使用标准库 (cuBLAS/cuDNN)

4. Transformer Engine (H100+):
   - 自动管理 FP8 精度
   - 融合操作减少内存带宽
   - 对用户几乎透明

5. 实践建议:
   - 训练用 BF16 (范围大,不需 GradScaler)
   - 推理用 FP8/INT8 (速度优先)
   - 确保 hidden_size / num_heads 等维度是 8 的倍数
```

---

*下一篇：[07-multi-gpu-interconnect.md](07-multi-gpu-interconnect.md) - 多卡互联技术*

---

## 参考资料与引用

1. **NVIDIA.** *Tensor Core Programming.* — Tensor Core 编程接口  
   https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#wmma

2. **Markidis, S., et al. (2018).** *NVIDIA Tensor Core Programmability, Performance & Precision.* — Tensor Core 性能分析  
   https://arxiv.org/abs/1803.04014

3. **Micikevicius, P., et al. (2018).** *Mixed Precision Training.* ICLR 2018. — 混合精度训练与 Tensor Core  
   https://arxiv.org/abs/1710.03740

4. **NVIDIA.** *H100 Tensor Core GPU Architecture — FP8 Training.*  
   https://resources.nvidia.com/en-us-tensor-core

5. **NVIDIA.** *cuDNN Library.* — 深度学习原语库 (使用 Tensor Core)  
   https://developer.nvidia.com/cudnn
