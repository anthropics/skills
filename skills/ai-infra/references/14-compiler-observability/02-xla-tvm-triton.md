# 主流 AI 编译器

> 选 AI 编译器就像选交通工具——XLA 是高铁（快但固定线路），TVM 是越野车（哪里都能去），Triton 是赛车（赛道上最快），torch.compile 是自动驾驶汽车（最方便）。

## 目录

- [torch.compile / TorchInductor](#torchcompile--torchinductor)
- [XLA](#xla)
- [OpenAI Triton](#openai-triton)
- [Apache TVM](#apache-tvm)
- [TensorRT](#tensorrt)
- [编译器对比](#编译器对比)
- [延伸阅读](#延伸阅读)

---

## torch.compile / TorchInductor

### 架构概览

```
torch.compile 编译流水线

Python 代码
     │
     ▼
┌──────────────────────┐
│ TorchDynamo           │  ← Python 字节码级图捕获
│ • 拦截 Python 帧      │     处理动态控制流
│ • 生成 FX Graph       │     Graph Break 机制
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ AOTAutograd           │  ← 编译时展开自动微分
│ • 前向图 + 反向图     │     联合优化前向/反向
└──────────┬───────────┘
           ▼
┌──────────────────────┐
│ TorchInductor         │  ← 代码生成后端
│ • 图级别优化          │
│ • 生成 Triton Kernel  │  ← GPU 代码
│ • 生成 C++ 代码       │  ← CPU 代码
│ • 自动调优 (Autotune) │
└──────────────────────┘
```

### 使用实践

```python
import torch

model = MyModel().cuda()

# 基础用法
compiled = torch.compile(model)

# 高级用法：指定模式
# default: 平衡编译时间和运行性能
# reduce-overhead: 最小化 Python 开销（适合小模型）
# max-autotune: 最大性能（编译耗时最长）
compiled = torch.compile(model, mode="max-autotune")

# 指定后端
compiled = torch.compile(model, backend="inductor")    # 默认
compiled = torch.compile(model, backend="cudagraphs")  # CUDA Graphs
compiled = torch.compile(model, backend="eager")       # 不编译（调试用）

# 处理动态形状
compiled = torch.compile(model, dynamic=True)  # 支持动态 batch size

# 调试编译问题
import torch._dynamo
torch._dynamo.config.verbose = True
torch._dynamo.config.suppress_errors = True  # 编译失败时回退到 eager

# 查看生成的代码
torch._inductor.config.debug = True  # 输出生成的 Triton/C++ 代码
```

### 性能收益

```
torch.compile 性能收益（HuggingFace 模型）

模型                  Eager      Compiled    加速比
──────────────────────────────────────────────────
BERT-Large            8.2ms      5.1ms       1.6x
GPT-2                 12.3ms     7.8ms       1.6x
Llama-7B (推理)       45ms       28ms        1.6x
Stable Diffusion      3.2s       2.1s        1.5x
ResNet-50             4.1ms      2.5ms       1.6x

注: 加速比因模型和硬件而异，通常 1.3x - 2.0x
```

---

## XLA

### 概述

XLA（Accelerated Linear Algebra）是 Google 开发的 AI 编译器，主要服务于 JAX 和 TensorFlow 生态。

```
XLA 编译流水线

JAX / TensorFlow 代码
         │
         ▼
┌─────────────────────┐
│ HLO (High Level     │  ← 高层中间表示
│ Optimized IR)       │     与框架无关
└────────┬────────────┘
         ▼
┌─────────────────────┐
│ 图级别优化           │  ← 算子融合、CSE、DCE
│ • 融合 Pass         │     布局优化、批归一化重写
│ • 内存优化          │
└────────┬────────────┘
         ▼
┌─────────────────────┐
│ 目标代码生成         │
│ ├── GPU: CUDA/PTX   │
│ ├── TPU: TPU IR     │  ← 对 TPU 优化最好
│ └── CPU: LLVM IR    │
└─────────────────────┘
```

### JAX + XLA 实践

```python
import jax
import jax.numpy as jnp

# JAX 自动使用 XLA 编译
@jax.jit  # JIT 编译 → 触发 XLA
def transformer_layer(params, x):
    # 注意力
    q = x @ params['W_q']
    k = x @ params['W_k']
    v = x @ params['W_v']
    
    attn = jax.nn.softmax(q @ k.T / jnp.sqrt(64))
    out = attn @ v @ params['W_o']
    
    # 残差 + LayerNorm
    x = layer_norm(x + out)
    
    # FFN
    h = jax.nn.gelu(x @ params['W_1'])
    x = x + h @ params['W_2']
    return layer_norm(x)

# XLA 的优势场景
# 1. TPU 训练 → XLA 是唯一选择
# 2. 大规模并行 → XLA 的 SPMD 分区器
# 3. 科研探索 → JAX 的函数式编程 + XLA 优化

# 查看 XLA 优化后的 HLO
from jax import make_jaxpr
print(make_jaxpr(transformer_layer)(params, x))
```

### XLA 的关键能力

| 特性 | 说明 |
|------|------|
| 算子融合 | 自动融合逐元素操作和简单归约 |
| 内存优化 | 缓冲区复用、内存调度 |
| 布局优化 | 自动选择最优数据布局（NHWC/NCHW） |
| SPMD 分区 | 自动模型并行分区（与 GSPMD 结合） |
| TPU 支持 | 对 TPU 有最佳优化 |

---

## OpenAI Triton

### 概述

Triton 是 OpenAI 开发的 GPU 编程语言，让开发者用类 Python 语法编写高效的 CUDA Kernel。

```
Triton 在编程抽象层次中的位置

抽象层次     │ 工具                 │ 开发效率  │ 性能
高 ──────────┼─────────────────────┼─────────┼──────
             │ PyTorch (Eager)     │ ⭐⭐⭐⭐⭐  │ ⭐⭐
             │ torch.compile       │ ⭐⭐⭐⭐   │ ⭐⭐⭐⭐
             │ Triton              │ ⭐⭐⭐    │ ⭐⭐⭐⭐⭐
             │ CUDA C++            │ ⭐       │ ⭐⭐⭐⭐⭐
低 ──────────┼─────────────────────┼─────────┼──────

Triton 的定位: 接近 CUDA 性能，接近 Python 易用性
```

### Triton 编程示例

```python
import triton
import triton.language as tl
import torch

@triton.jit
def fused_add_relu_kernel(
    x_ptr, y_ptr, output_ptr,
    n_elements,
    BLOCK_SIZE: tl.constexpr,
):
    """融合 Add + ReLU 的 Triton Kernel"""
    # 计算当前块的索引
    pid = tl.program_id(0)
    block_start = pid * BLOCK_SIZE
    offsets = block_start + tl.arange(0, BLOCK_SIZE)
    mask = offsets < n_elements
    
    # 加载数据
    x = tl.load(x_ptr + offsets, mask=mask)
    y = tl.load(y_ptr + offsets, mask=mask)
    
    # 融合计算：Add + ReLU
    result = x + y
    result = tl.maximum(result, 0.0)  # ReLU
    
    # 写回结果
    tl.store(output_ptr + offsets, result, mask=mask)

def fused_add_relu(x: torch.Tensor, y: torch.Tensor) -> torch.Tensor:
    """Python 接口"""
    output = torch.empty_like(x)
    n_elements = x.numel()
    
    # 计算 grid 大小
    grid = lambda meta: (triton.cdiv(n_elements, meta['BLOCK_SIZE']),)
    
    # 启动 Kernel
    fused_add_relu_kernel[grid](x, y, output, n_elements, BLOCK_SIZE=1024)
    return output

# 使用
x = torch.randn(1000000, device='cuda')
y = torch.randn(1000000, device='cuda')
result = fused_add_relu(x, y)
```

### Triton 的核心概念

```
Triton 的块级编程模型

传统 CUDA:                        Triton:
┌──────────────────────┐          ┌──────────────────────┐
│ 线程级操作            │          │ 块级操作              │
│ thread_id → 1 element │         │ program_id → N 元素   │
│ 手动管理共享内存      │          │ 自动 Tiling           │
│ 手动 syncthreads     │          │ 自动共享内存          │
│ 手动循环展开         │          │ 自动向量化            │
└──────────────────────┘          └──────────────────────┘

开发者只需思考:
  1. 数据分块 (BLOCK_SIZE)
  2. 计算逻辑 (element-wise / reduction)
  3. 加载与存储 (tl.load / tl.store)

编译器自动处理:
  • 线程映射和调度
  • 共享内存分配和使用
  • 内存合并访问
  • 循环展开和向量化
```

---

## Apache TVM

### 概述

TVM 是一个端到端的深度学习编译框架，目标是在任意硬件上实现高效推理。

```
TVM 编译流程

PyTorch/TF/ONNX 模型
         │
         ▼
┌─────────────────────┐
│ Relay IR             │  ← 高层图 IR
│ (算子级别)           │     图优化、类型推断
└────────┬────────────┘
         ▼
┌─────────────────────┐
│ TIR                  │  ← 底层张量 IR
│ (Tensor IR)          │     循环优化、Tiling
└────────┬────────────┘
         ▼
┌─────────────────────┐
│ AutoTVM / Ansor      │  ← 自动调优
│ (Meta-Schedule)      │     搜索最优实现
└────────┬────────────┘
         ▼
┌─────────────────────┐
│ 目标代码             │
│ ├── CUDA            │
│ ├── Metal           │  ← Apple GPU
│ ├── OpenCL          │  ← 跨平台 GPU
│ ├── Vulkan          │
│ └── LLVM (CPU)      │
└─────────────────────┘
```

### TVM 使用示例

```python
import tvm
from tvm import relay
import onnx

# 1. 从 ONNX 导入模型
onnx_model = onnx.load("model.onnx")
mod, params = relay.frontend.from_onnx(onnx_model, shape={"input": (1, 3, 224, 224)})

# 2. 图级别优化
with tvm.transform.PassContext(opt_level=3):
    mod = relay.transform.InferType()(mod)
    mod = relay.transform.FoldConstant()(mod)
    mod = relay.transform.FuseOps()(mod)

# 3. 编译到目标硬件
target = tvm.target.cuda()  # 或 "llvm", "metal" 等
lib = relay.build(mod, target=target, params=params)

# 4. 运行推理
dev = tvm.cuda(0)
module = tvm.contrib.graph_executor.GraphModule(lib["default"](dev))
module.set_input("input", tvm.nd.array(input_data))
module.run()
output = module.get_output(0).numpy()

# 5. 自动调优（找到每个算子的最优实现）
from tvm import auto_scheduler

tasks, task_weights = auto_scheduler.extract_tasks(mod["main"], params, target)
tuner = auto_scheduler.TaskScheduler(tasks, task_weights)
tune_option = auto_scheduler.TuningOptions(
    num_measure_trials=1000,
    measure_callbacks=[auto_scheduler.RecordToFile("tuning_log.json")],
)
tuner.tune(tune_option)
```

---

## TensorRT

### 概述

TensorRT 是 NVIDIA 的推理优化引擎，在 NVIDIA GPU 上提供最优的推理性能。

```
TensorRT 优化流程

ONNX / PyTorch / TF 模型
         │
         ▼
┌─────────────────────┐
│ 网络定义解析         │
│ (导入模型结构)       │
└────────┬────────────┘
         ▼
┌─────────────────────┐
│ 图优化              │
│ • 层融合            │
│ • 精度校准 (INT8)   │  ← TensorRT 的 INT8 校准最成熟
│ • Kernel 自动选择   │
│ • 多流执行          │
└────────┬────────────┘
         ▼
┌─────────────────────┐
│ TensorRT Engine     │  ← 序列化的优化引擎
│ (特定 GPU 架构优化)  │     绑定到特定 GPU 型号
└─────────────────────┘
```

### TensorRT-LLM 用于大模型推理

```python
# TensorRT-LLM: 专为 LLM 优化的推理引擎
# 支持: Llama, GPT, Falcon, Qwen 等主流模型

# 构建 TensorRT-LLM 引擎
# trtllm-build \
#   --model_dir ./llama-7b \
#   --output_dir ./engine \
#   --dtype float16 \
#   --gemm_plugin float16 \
#   --max_batch_size 64 \
#   --max_input_len 2048 \
#   --max_output_len 512

# TensorRT-LLM 的关键优化:
# • FlashAttention 内置
# • KV Cache 量化 (FP8/INT8)
# • Tensor 并行
# • Inflight Batching
# • Paged KV Cache
# • Speculative Decoding
```

---

## 编译器对比

### 全面对比

| 维度 | torch.compile | XLA | Triton | TVM | TensorRT |
|------|--------------|-----|--------|-----|----------|
| 主要用途 | PyTorch 加速 | JAX/TF 加速 | 自定义 Kernel | 跨平台部署 | NVIDIA 推理 |
| 易用性 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ |
| GPU 性能 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| TPU 支持 | ❌ | ⭐⭐⭐⭐⭐ | ❌ | ⭐⭐ | ❌ |
| 训练支持 | ✅ | ✅ | ✅ | ❌ | ❌ |
| 推理优化 | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| 开源 | ✅ | ✅ | ✅ | ✅ | 部分 |
| 动态形状 | ✅ | 有限 | ✅ | 有限 | 有限 |
| 生态集成 | PyTorch | JAX/TF | PyTorch | 多框架 | NVIDIA |

### 选型决策

```
AI 编译器选型决策树

你的需求是？
│
├── 用 PyTorch 训练，想简单加速
│   └── torch.compile ← 一行代码，最简单
│
├── 用 JAX 训练或需要 TPU
│   └── XLA ← JAX 原生，TPU 唯一选择
│
├── 需要写自定义高性能 Kernel
│   └── Triton ← Python 语法，接近 CUDA 性能
│
├── 需要跨平台/跨硬件部署
│   └── TVM / ONNX Runtime ← 多硬件支持
│
├── NVIDIA GPU 上的生产推理
│   └── TensorRT / TensorRT-LLM ← 推理最优
│
└── 不确定
    └── 从 torch.compile 开始，按需升级
```

---

## 延伸阅读

- [PyTorch 2.0: torch.compile](https://pytorch.org/get-started/pytorch-2.0/)
- [Triton Tutorial](https://triton-lang.org/main/getting-started/tutorials/)
- [XLA Architecture](https://www.tensorflow.org/xla/architecture)
- [TVM Documentation](https://tvm.apache.org/docs/)
- [TensorRT-LLM GitHub](https://github.com/NVIDIA/TensorRT-LLM)
- [FlashAttention: Triton Implementation](https://github.com/Dao-AILab/flash-attention)

---

*上一篇：[01-ai-compiler-overview.md](01-ai-compiler-overview.md)* | *下一篇：[03-operator-optimization.md](03-operator-optimization.md)*

[返回目录](README.md) | [返回主页](../README.md)
