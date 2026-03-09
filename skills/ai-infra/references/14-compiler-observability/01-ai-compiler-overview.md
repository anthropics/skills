# AI 编译器概述

> AI 编译器就像一位经验丰富的"同声传译"——把研究员写的高层 Python 代码，高效翻译成 GPU 能理解的底层指令。

## 目录

- [为什么需要 AI 编译器](#为什么需要-ai-编译器)
- [AI 编译器 vs 传统编译器](#ai-编译器-vs-传统编译器)
- [计算图与优化](#计算图与优化)
- [算子融合](#算子融合)
- [编译模式](#编译模式)
- [AI 编译器全景](#ai-编译器全景)
- [延伸阅读](#延伸阅读)

---

## 为什么需要 AI 编译器

### 效率鸿沟

深度学习框架（PyTorch/TensorFlow）追求的是开发者的灵活性，但这种灵活性带来了性能代价：

```
Python 代码到 GPU 执行的效率鸿沟

Python 层 (PyTorch)              GPU 层 (CUDA)
┌───────────────────┐            ┌──────────────────┐
│ y = x @ W + b     │   GAP!     │ cublasSgemm()    │
│ y = F.relu(y)     │ ──────▶   │ relu_kernel()    │
│ y = F.dropout(y)  │            │ dropout_kernel() │
└───────────────────┘            └──────────────────┘
     3 行 Python                   3 次 Kernel Launch
     简单直观                      每次 Launch 有开销:
                                   • GPU 调度延迟 (~5μs)
                                   • 读写全局显存
                                   • Python 解释器开销

AI 编译器的目标: 消除这个 GAP

编译后:
┌──────────────────┐
│ fused_kernel()   │  ← 一次 Kernel Launch
│  matmul + relu   │     消除中间显存读写
│  + dropout       │     减少调度开销
└──────────────────┘
```

### 生活类比

> 想象你在翻译一本书：
>
> **逐句翻译**（无编译器）：读一句中文 → 翻译 → 写一句英文 → 再读下一句...
> - 每句都要"查字典、想语法"，效率低
>
> **整章翻译**（有编译器）：先通读全章 → 理解上下文 → 优化表达 → 一次性写出流畅的英文
> - 利用上下文信息，消除冗余，更优美高效
>
> AI 编译器就是那个"先通读再翻译"的高效翻译者。

---

## AI 编译器 vs 传统编译器

```
对比：传统编译器 vs AI 编译器

┌─────────────────┬──────────────────────┬──────────────────────┐
│ 维度            │ 传统编译器            │ AI 编译器             │
│                 │ (GCC/LLVM)           │ (XLA/TVM/Triton)     │
├─────────────────┼──────────────────────┼──────────────────────┤
│ 输入            │ C/C++/Rust 源代码     │ 计算图 / 张量表达式   │
│ 输出            │ 机器码 (x86/ARM)     │ GPU Kernel (CUDA/PTX)│
│ 优化重点        │ 指令调度、寄存器分配   │ 算子融合、内存布局    │
│ 核心抽象        │ 控制流、数据类型      │ 张量、循环、内存层次  │
│ 优化信息        │ 静态分析             │ 张量形状 + 硬件特性   │
│ 自动并行        │ 有限 (OpenMP)        │ 核心能力              │
│ 目标硬件        │ CPU                  │ GPU/TPU/NPU          │
└─────────────────┴──────────────────────┴──────────────────────┘

共同之处：
  • 都做中间表示 (IR) 的变换与优化
  • 都关注性能（延迟、吞吐）
  • 都需要理解目标硬件特性
```

### AI 编译器的编译栈

```
AI 编译器典型编译栈

            ┌─────────────────────────┐
            │  用户代码 (Python)       │
            │  model(x) / y = f(x)    │
            └────────────┬────────────┘
                         ▼
            ┌─────────────────────────┐
 High-level │  前端 IR (计算图)        │  ← Graph-level 优化
 IR         │  如 FX Graph / HLO      │     算子融合、常量折叠
            └────────────┬────────────┘     形状推断、布局优化
                         ▼
            ┌─────────────────────────┐
 Low-level  │  后端 IR (循环/张量)     │  ← Loop-level 优化
 IR         │  如 TorchInductor /     │     Tiling、向量化
            │  Triton IR / TVM TIR    │     共享内存利用
            └────────────┬────────────┘
                         ▼
            ┌─────────────────────────┐
 Target     │  硬件代码               │
 Code       │  CUDA / PTX / LLVM IR   │
            └─────────────────────────┘
```

---

## 计算图与优化

### 什么是计算图

```python
# Python 代码
def transformer_block(x, W_q, W_k, W_v, W_o):
    q = x @ W_q
    k = x @ W_k
    v = x @ W_v
    attn = softmax(q @ k.T / sqrt(d)) @ v
    out = attn @ W_o
    return layer_norm(out + x)  # 残差连接

# 对应的计算图：
#
#   x ──┬── MatMul(W_q) ──▶ q ──┐
#       ├── MatMul(W_k) ──▶ k ──┤
#       ├── MatMul(W_v) ──▶ v ──┤
#       │                        ▼
#       │              ┌── Attention ──┐
#       │              │   q @ k^T     │
#       │              │   / sqrt(d)   │
#       │              │   softmax     │
#       │              │   @ v         │
#       │              └───────┬───────┘
#       │                      ▼
#       │              MatMul(W_o) ──▶ attn_out
#       │                      │
#       └──────── Add ◀────────┘  ← 残差连接
#                  │
#            LayerNorm
#                  │
#                output
```

### 图级别优化

```
常见的图级别优化

1. 算子融合 (Operator Fusion)
   ┌─────────┐   ┌─────────┐   ┌─────────┐
   │ MatMul  │──▶│  BiasAdd │──▶│  ReLU   │
   └─────────┘   └─────────┘   └─────────┘
        ↓ 融合为
   ┌─────────────────────────────────────┐
   │   FusedMatMulBiasReLU               │  ← 减少 2 次显存读写
   └─────────────────────────────────────┘

2. 常量折叠 (Constant Folding)
   scale = 1.0 / sqrt(64)  → scale = 0.125  ← 编译时计算

3. 公共子表达式消除 (CSE)
   a = x + y                a = x + y
   b = x + y    ──▶        b = a           ← 复用计算结果
   c = a * b                c = a * a

4. 死代码消除 (DCE)
   y = f(x)                 y = f(x)
   z = g(x)     ──▶        return y         ← z 未使用，删除
   return y

5. 内存规划 (Memory Planning)
   分析张量的生命周期 → 原地复用缓冲区 → 减少显存峰值
```

---

## 算子融合

### 融合的类型

```
算子融合的三种模式

1. 逐元素融合 (Element-wise Fusion)
   ┌──────┐ ┌──────┐ ┌──────┐      ┌────────────────────┐
   │ Add  │→│ ReLU │→│Scale │  →   │ FusedAddReluScale  │
   └──────┘ └──────┘ └──────┘      └────────────────────┘
   每次读写显存 → 一次读写           节省 2/3 显存带宽

2. 归约融合 (Reduction Fusion)
   ┌──────┐ ┌──────────┐            ┌──────────────────┐
   │ Exp  │→│ ReduceSum│   →       │ FusedSoftmax     │
   └──────┘ └──────────┘            └──────────────────┘
   softmax = exp(x) / sum(exp(x))  一个 Kernel 完成

3. 跨算子融合 (Cross-operator Fusion)
   ┌────────┐ ┌────────┐ ┌──────┐  ┌──────────────────────┐
   │ MatMul │→│BiasAdd │→│ GeLU │→ │ FusedLinearGeLU      │
   └────────┘ └────────┘ └──────┘  └──────────────────────┘
   最有价值的融合：消除大量中间张量
```

### 融合的性能影响

```
算子融合性能影响示例（以 BERT-Large 为例）

                无融合      基础融合     激进融合
Kernel 数量      1200+       ~400        ~150
显存带宽使用      100%        60%         35%
总延迟            8.2ms       5.1ms       3.4ms
加速比            1.0x        1.6x        2.4x

关键洞察：
  GPU 上大部分小算子是"显存带宽受限"的
  融合减少显存读写 → 直接转化为性能提升
```

---

## 编译模式

### Eager vs Graph vs JIT

```
三种执行模式对比

1. Eager Mode（即时执行）
   ┌─────────────────────────────────┐
   │ Python 一行 → GPU 执行一步      │
   │ 优点: 灵活、易调试              │
   │ 缺点: 开销大、无法全局优化      │
   │ 代表: PyTorch 默认模式          │
   └─────────────────────────────────┘

2. Graph Mode（图模式）
   ┌─────────────────────────────────┐
   │ 先构建完整计算图 → 再优化执行    │
   │ 优点: 全局优化、高性能           │
   │ 缺点: 灵活性低、调试困难        │
   │ 代表: TensorFlow 1.x            │
   └─────────────────────────────────┘

3. JIT Compilation（即时编译）
   ┌─────────────────────────────────┐
   │ 运行时捕获计算图 → 编译优化      │
   │ 优点: 兼顾灵活性与性能           │
   │ 缺点: 首次编译慢、兼容性问题     │
   │ 代表: torch.compile, JAX jit    │
   └─────────────────────────────────┘
```

### torch.compile 示例

```python
import torch

# 定义模型
class TransformerBlock(torch.nn.Module):
    def __init__(self, d_model=512):
        super().__init__()
        self.attn = torch.nn.MultiheadAttention(d_model, 8)
        self.ffn = torch.nn.Sequential(
            torch.nn.Linear(d_model, 2048),
            torch.nn.GELU(),
            torch.nn.Linear(2048, d_model),
        )
        self.norm1 = torch.nn.LayerNorm(d_model)
        self.norm2 = torch.nn.LayerNorm(d_model)
    
    def forward(self, x):
        x = x + self.attn(self.norm1(x), self.norm1(x), self.norm1(x))[0]
        x = x + self.ffn(self.norm2(x))
        return x

model = TransformerBlock().cuda()

# 一行代码编译加速！
compiled_model = torch.compile(model)

# 第一次调用：编译（较慢）
x = torch.randn(32, 128, 512).cuda()
output = compiled_model(x)  # 触发编译

# 后续调用：使用编译后的 Kernel（更快）
output = compiled_model(x)  # 使用缓存的编译结果

# 不同编译模式
torch.compile(model, mode="default")       # 平衡编译时间和性能
torch.compile(model, mode="reduce-overhead") # 减少 Python 开销
torch.compile(model, mode="max-autotune")  # 最大性能（编译最慢）
```

---

## AI 编译器全景

```
AI 编译器生态全景图（2024-2025）

PyTorch 生态                    JAX/TF 生态
┌────────────────────┐          ┌────────────────────┐
│ torch.compile      │          │ XLA                │
│ ├── TorchDynamo    │          │ ├── HLO IR         │
│ │   (图捕获)       │          │ │   (高层 IR)       │
│ ├── TorchInductor  │          │ ├── 图级别优化      │
│ │   (代码生成)     │          │ └── 目标:           │
│ │   └── Triton     │          │     GPU/TPU/CPU    │
│ └── AOTAutograd    │          └────────────────────┘
│     (自动微分)     │
└────────────────────┘          跨平台
                                ┌────────────────────┐
GPU Kernel 编写                  │ Apache TVM         │
┌────────────────────┐          │ ├── Relay IR        │
│ OpenAI Triton      │          │ ├── AutoTVM/Ansor   │
│ ├── 块级编程       │          │ └── 目标:           │
│ ├── 自动 Tiling    │          │     任意硬件        │
│ └── Python 语法    │          └────────────────────┘
└────────────────────┘
                                推理优化
NVIDIA 官方                      ┌────────────────────┐
┌────────────────────┐          │ ONNX Runtime       │
│ TensorRT           │          │ ├── 图优化          │
│ ├── Layer Fusion   │          │ ├── 多后端          │
│ ├── INT8/FP8 量化  │          │ └── 跨平台          │
│ └── 推理最优       │          └────────────────────┘
└────────────────────┘
```

### 选型建议

| 场景 | 推荐 | 原因 |
|------|------|------|
| PyTorch 训练加速 | torch.compile | 无缝集成，一行代码 |
| JAX 生态 | XLA | 原生支持，TPU 最优 |
| 自定义 GPU Kernel | Triton | Python 语法，高效率 |
| 跨平台部署 | TVM / ONNX Runtime | 多硬件支持 |
| NVIDIA GPU 推理 | TensorRT | 推理性能最优 |
| 研究/探索 | Triton | 灵活、易于实验 |

---

## 延伸阅读

- [The Deep Learning Compiler: A Comprehensive Survey](https://arxiv.org/abs/2002.03794)
- [torch.compile: Understanding PyTorch 2.0](https://pytorch.org/get-started/pytorch-2.0/)
- [Triton: An Intermediate Language and Compiler](https://triton-lang.org/)
- [TVM: An Automated End-to-End Optimizing Compiler](https://tvm.apache.org/)
- [XLA: Optimizing Compiler for Machine Learning](https://www.tensorflow.org/xla)

---

*下一篇：[02-xla-tvm-triton.md](02-xla-tvm-triton.md)*

[返回目录](README.md) | [返回主页](../README.md)
