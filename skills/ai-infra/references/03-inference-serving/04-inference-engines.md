# 推理引擎详解

> TensorRT、TensorRT-LLM、ONNX Runtime — 把模型从"能跑"变成"跑得快"。

## 目录

- [什么是推理引擎](#什么是推理引擎)
- [核心优化原理](#核心优化原理)
- [TensorRT](#tensorrt)
- [TensorRT-LLM](#tensorrt-llm)
- [ONNX Runtime](#onnx-runtime)
- [引擎对比总表](#引擎对比总表)

---

## 什么是推理引擎

```
  生活类比：翻译 → 同声传译

  PyTorch 直接推理 = 拿着字典逐句翻译
    → 每个算子单独调度，有大量框架开销
    → "能用"但"不够快"

  推理引擎 = 同声传译
    → 提前准备好常用句型 (图优化)
    → 多个概念一句话说完 (算子融合)
    → 用最简洁的表达 (低精度计算)
    → 听到就能翻，不需要查字典 (编译优化)

  ┌─────────────────────────────────────────────────────────┐
  │  模型从训练到推理的过程:                                  │
  │                                                         │
  │  PyTorch 模型 (.pt)                                     │
  │       │                                                 │
  │       │ ① 导出为中间表示                                │
  │       ▼                                                 │
  │  ONNX / TorchScript                                     │
  │       │                                                 │
  │       │ ② 推理引擎编译优化                              │
  │       ▼                                                 │
  │  ┌─────────────────────────────────────────────┐        │
  │  │  推理引擎做了什么:                           │        │
  │  │  • 图优化 (去掉冗余操作)                     │        │
  │  │  • 算子融合 (合并多个操作为一个)              │        │
  │  │  • 精度转换 (FP16/INT8)                      │        │
  │  │  • 内存优化 (复用中间张量)                   │        │
  │  │  • 内核自动调优 (选最快的 CUDA kernel)        │        │
  │  └─────────────────────────────────────────────┘        │
  │       │                                                 │
  │       │ ③ 输出优化后的引擎                              │
  │       ▼                                                 │
  │  Engine / Plan (可直接在 GPU 上高效执行)                  │
  └─────────────────────────────────────────────────────────┘
```

---

## 核心优化原理

### 1. 算子融合 (Layer/Operator Fusion)

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  类比: 快递合并配送                                              │
  │                                                                  │
  │  不融合 = 每个包裹单独送一趟:                                    │
  │    送包裹A → 回仓库 → 送包裹B → 回仓库 → 送包裹C               │
  │    → 大量时间浪费在"回仓库"(GPU 和显存之间来回搬数据)           │
  │                                                                  │
  │  融合 = 三个包裹一趟送完:                                        │
  │    送包裹A+B+C → 完成!                                          │
  │    → 减少了"回仓库"的次数                                       │
  │                                                                  │
  ├──────────────────────────────────────────────────────────────────┤
  │  实际例子: Conv + BatchNorm + ReLU 融合                          │
  │                                                                  │
  │  未融合 (3 个 kernel 启动, 3 次显存读写):                        │
  │                                                                  │
  │    显存 ──读──→ Conv kernel ──写──→ 显存                         │
  │    显存 ──读──→ BN kernel   ──写──→ 显存                         │
  │    显存 ──读──→ ReLU kernel ──写──→ 显存                         │
  │                                                                  │
  │  融合后 (1 个 kernel 启动, 1 次显存读写):                        │
  │                                                                  │
  │    显存 ──读──→ [Conv+BN+ReLU] kernel ──写──→ 显存               │
  │                                                                  │
  │  性能提升: 减少 2/3 的显存访问! 对于 memory-bound 操作提升巨大   │
  │                                                                  │
  ├──────────────────────────────────────────────────────────────────┤
  │  Transformer 中常见的融合:                                       │
  │                                                                  │
  │  • QKV 投影融合: Q_proj + K_proj + V_proj → 一个大矩阵乘法      │
  │    原本: 3 次 [batch, seq, hidden] × [hidden, hidden]            │
  │    融合: 1 次 [batch, seq, hidden] × [hidden, 3×hidden]          │
  │                                                                  │
  │  • Attention + Softmax + Mask 融合:                              │
  │    写一个定制 CUDA kernel，一次完成所有步骤                       │
  │                                                                  │
  │  • LayerNorm + Linear 融合:                                      │
  │    避免中间结果写回显存                                           │
  └──────────────────────────────────────────────────────────────────┘
```

### 2. 图优化 (Graph Optimization)

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  类比: 代码优化 — 编译器做的事                                   │
  │                                                                  │
  │  ── 常量折叠 (Constant Folding) ──                               │
  │                                                                  │
  │  优化前: x = input × 2.0 × 3.0                                  │
  │  优化后: x = input × 6.0                                        │
  │  → 编译时就把 2.0×3.0=6.0 算好了                                │
  │                                                                  │
  │  ── 死代码消除 (Dead Code Elimination) ──                        │
  │                                                                  │
  │  训练时的 Dropout 层 → 推理时不需要 → 直接移除                   │
  │  BatchNorm 的均值方差 → 推理时是常量 → 折叠进权重                │
  │                                                                  │
  │  ── 算子替换 (Operator Substitution) ──                          │
  │                                                                  │
  │  通用 GEMM → 针对特定形状的优化 kernel                           │
  │  例: [1, 4096] × [4096, 4096] → 调用 cublasSgemm 的特化版本     │
  │                                                                  │
  │  ── 内存规划 (Memory Planning) ──                                │
  │                                                                  │
  │  分析张量的生命周期，让不同时间使用的张量复用同一块内存           │
  │                                                                  │
  │  张量 A: [──使用──]                                              │
  │  张量 B:            [──使用──]                                   │
  │  → A 和 B 不会同时存在，可以共享同一块显存!                      │
  │  → 大幅减少推理时的显存占用                                      │
  └──────────────────────────────────────────────────────────────────┘
```

### 3. 内核自动调优 (Kernel Auto-Tuning)

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  同一个矩阵乘法，有几十种实现方式:                               │
  │                                                                  │
  │  [1024, 1024] × [1024, 1024]:                                    │
  │    实现 A: tile size 64×64, 2 个 warp  → 1.2 ms                 │
  │    实现 B: tile size 128×64, 4 个 warp → 0.8 ms                 │
  │    实现 C: tile size 128×128, 使用 Tensor Core → 0.3 ms         │
  │    ...                                                           │
  │                                                                  │
  │  推理引擎在"编译"阶段会:                                        │
  │  1. 枚举所有候选 kernel                                          │
  │  2. 在目标 GPU 上实际运行每一个                                  │
  │  3. 选出最快的那个                                               │
  │                                                                  │
  │  类比: 赛马                                                      │
  │    不知道哪匹马最快? 让它们都跑一圈，选冠军!                     │
  │    → 这就是为什么 TensorRT 编译需要几分钟到几小时                │
  │    → 但编译一次，之后每次推理都用最快的 kernel                   │
  │                                                                  │
  │  注意: 不同 GPU 的最优 kernel 不同!                               │
  │    A100 上最快的 ≠ RTX 4090 上最快的                             │
  │    → 引擎文件不能跨 GPU 型号使用                                 │
  └──────────────────────────────────────────────────────────────────┘
```

---

## TensorRT

### 定位与原理

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  TensorRT = NVIDIA 的王牌推理引擎 (2016 年发布)                  │
  │                                                                  │
  │  定位: 通用模型推理 (CV、NLP、推荐等)                             │
  │  原理: 把计算图编译成高度优化的 CUDA 程序                        │
  │                                                                  │
  │  ┌─────────────────────────────────────────────────────────┐     │
  │  │  TensorRT 编译流程                                       │     │
  │  │                                                         │     │
  │  │  ONNX 模型                                              │     │
  │  │      │                                                  │     │
  │  │      ▼                                                  │     │
  │  │  ┌──────────────┐                                      │     │
  │  │  │ Parser        │ 解析模型结构                         │     │
  │  │  └──────┬───────┘                                      │     │
  │  │         ▼                                               │     │
  │  │  ┌──────────────┐                                      │     │
  │  │  │ Optimizer     │ 图优化 + 算子融合                    │     │
  │  │  └──────┬───────┘                                      │     │
  │  │         ▼                                               │     │
  │  │  ┌──────────────┐                                      │     │
  │  │  │ Builder       │ 内核自动调优 (最耗时的步骤)          │     │
  │  │  │               │ 尝试所有 kernel，选最快的            │     │
  │  │  └──────┬───────┘                                      │     │
  │  │         ▼                                               │     │
  │  │  ┌──────────────┐                                      │     │
  │  │  │ Engine (.plan)│ 优化后的推理引擎                     │     │
  │  │  │               │ 可序列化保存，下次直接加载           │     │
  │  │  └──────────────┘                                      │     │
  │  └─────────────────────────────────────────────────────────┘     │
  │                                                                  │
  │  典型加速效果:                                                    │
  │  ResNet-50:  PyTorch 5ms → TensorRT 0.8ms  (6x 加速)            │
  │  BERT-Base:  PyTorch 12ms → TensorRT 2ms   (6x 加速)            │
  │  GPT-2:     PyTorch 30ms → TensorRT 8ms    (3.7x 加速)          │
  └──────────────────────────────────────────────────────────────────┘
```

### 使用示例

```python
import tensorrt as trt

# Step 1: 创建 Builder 和 Network
logger = trt.Logger(trt.Logger.WARNING)
builder = trt.Builder(logger)
network = builder.create_network(
    1 << int(trt.NetworkDefinitionCreationFlag.EXPLICIT_BATCH)
)

# Step 2: 从 ONNX 解析模型
parser = trt.OnnxParser(network, logger)
with open("model.onnx", "rb") as f:
    parser.parse(f.read())

# Step 3: 配置优化选项
config = builder.create_builder_config()
config.set_flag(trt.BuilderFlag.FP16)          # 启用 FP16
config.set_memory_pool_limit(                   # 设置显存限制
    trt.MemoryPoolType.WORKSPACE, 1 << 30       # 1 GB
)

# Step 4: 编译引擎 (这步最耗时，会自动调优)
serialized_engine = builder.build_serialized_network(network, config)

# Step 5: 保存引擎 (下次可直接加载，跳过编译)
with open("model.plan", "wb") as f:
    f.write(serialized_engine)
```

---

## TensorRT-LLM

### 为什么需要专门的 LLM 推理引擎

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  TensorRT 的局限:                                                │
  │                                                                  │
  │  传统 TensorRT 是"静态图"优化 — 编译时确定所有形状               │
  │  但 LLM 推理的独特挑战:                                          │
  │                                                                  │
  │  1. 序列长度动态变化                                              │
  │     输入 "Hi" (2 token) 和 "Tell me about..." (100 token)        │
  │     → 静态图无法高效处理                                         │
  │                                                                  │
  │  2. KV Cache 持续增长                                             │
  │     每生成一个 token，KV Cache 就增大一点                        │
  │     → 需要动态内存管理                                           │
  │                                                                  │
  │  3. 自回归生成                                                    │
  │     一个 token 一个 token 地生成                                  │
  │     → 需要特殊的 Decode kernel                                   │
  │                                                                  │
  │  4. Continuous Batching                                           │
  │     不同请求的序列长度不同，需要动态拼 batch                     │
  │     → 传统静态 batch 效率低                                      │
  │                                                                  │
  │  → TensorRT-LLM = TensorRT + 专为 LLM 设计的功能                 │
  └──────────────────────────────────────────────────────────────────┘
```

### TensorRT-LLM 的关键技术

```
  ┌──────────────────────────────────────────────────────────────────┐
  │                                                                  │
  │  ── In-flight Batching (动态批处理) ──                            │
  │                                                                  │
  │  类比: 餐厅不等所有人点完再一起上菜                               │
  │    张三吃完了 → 李四可以立刻坐下点餐                              │
  │    不需要等整桌人都吃完                                           │
  │                                                                  │
  │  ── Paged KV Cache ──                                            │
  │                                                                  │
  │  借鉴操作系统的虚拟内存分页:                                     │
  │  KV Cache 不需要连续内存 → 按"页"分配                           │
  │  → 显存碎片减少，利用率提升 ~90%                                 │
  │                                                                  │
  │  ── 量化集成 ──                                                  │
  │                                                                  │
  │  支持 FP8 / INT8 / INT4 / SmoothQuant / AWQ                     │
  │  → 编译时自动插入量化/反量化节点                                 │
  │  → 利用 Tensor Core 的 INT8/FP8 指令                             │
  │                                                                  │
  │  ── 张量并行 ──                                                  │
  │                                                                  │
  │  多卡推理: 自动切分模型到多个 GPU                                 │
  │  支持 NVLink 通信优化                                             │
  │  → 70B 模型可以在 2×A100 上高效推理                              │
  │                                                                  │
  └──────────────────────────────────────────────────────────────────┘
```

### 使用示例

```python
# TensorRT-LLM 的高层 API (简洁版)
from tensorrt_llm import LLM, SamplingParams

# 自动完成: 模型转换 + 编译优化 + 推理
llm = LLM(model="meta-llama/Llama-2-7b-hf")

sampling_params = SamplingParams(
    temperature=0.8,
    top_p=0.95,
    max_tokens=256,
)

outputs = llm.generate(
    ["What is artificial intelligence?"],
    sampling_params=sampling_params,
)

# 底层流程实际上是:
# 1. 读取 HuggingFace 模型权重
# 2. 构建 TensorRT-LLM 计算图
# 3. 编译为 TensorRT Engine
# 4. 加载 Engine 执行推理
```

---

## ONNX Runtime

### 定位与原理

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  ONNX Runtime = 跨平台的"万能推理引擎"                           │
  │                                                                  │
  │  类比: USB — 统一接口标准                                        │
  │    不管你用什么框架训练 (PyTorch/TensorFlow/JAX)                  │
  │    → 都可以导出为 ONNX 格式                                      │
  │    → ONNX Runtime 在任何硬件上都能跑                             │
  │                                                                  │
  │  ┌───────────────────────────────────────────────────────────┐   │
  │  │  ONNX 生态                                                │   │
  │  │                                                           │   │
  │  │  训练框架:        中间格式:         硬件:                  │   │
  │  │  ┌──────────┐    ┌──────┐         ┌───────────┐          │   │
  │  │  │ PyTorch  │───→│      │───→     │ NVIDIA GPU│          │   │
  │  │  ├──────────┤    │ ONNX │         ├───────────┤          │   │
  │  │  │TensorFlow│───→│      │───→     │ AMD GPU   │          │   │
  │  │  ├──────────┤    │      │         ├───────────┤          │   │
  │  │  │   JAX    │───→│      │───→     │ Intel CPU │          │   │
  │  │  └──────────┘    │      │         ├───────────┤          │   │
  │  │                  │      │───→     │ Apple M系 │          │   │
  │  │                  │      │         ├───────────┤          │   │
  │  │                  │      │───→     │ Qualcomm  │          │   │
  │  │                  └──────┘         └───────────┘          │   │
  │  └───────────────────────────────────────────────────────────┘   │
  │                                                                  │
  │  ONNX Runtime 通过 Execution Provider 适配不同硬件:              │
  │  - CUDAExecutionProvider → NVIDIA GPU                            │
  │  - ROCMExecutionProvider → AMD GPU                               │
  │  - CPUExecutionProvider  → 任意 CPU                              │
  │  - TensorrtExecutionProvider → 调用 TensorRT (更快!)            │
  │  - CoreMLExecutionProvider → Apple 设备                          │
  │  - QNNExecutionProvider → Qualcomm 芯片                          │
  └──────────────────────────────────────────────────────────────────┘
```

### ONNX Runtime 的优化手段

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  三个优化层级:                                                    │
  │                                                                  │
  │  Level 1 — 基础图优化 (所有硬件通用)                              │
  │    • 常量折叠                                                    │
  │    • 冗余节点消除                                                │
  │    • 算子融合 (MatMul+Add → Gemm)                                │
  │                                                                  │
  │  Level 2 — 硬件特定优化                                           │
  │    • CUDA: 选择最优的 cuBLAS 算法                                │
  │    • CPU: AVX-512 向量化                                         │
  │    • 内存布局转换 (NCHW → NHWC)                                  │
  │                                                                  │
  │  Level 3 — 高级优化 (可能改变数值精度)                            │
  │    • FP16 转换                                                   │
  │    • 量化 (INT8)                                                 │
  │    • 混合精度执行                                                │
  │                                                                  │
  │  特色: Graph Optimization 可以离线保存                            │
  │    → 第一次运行时优化，后续直接加载优化后的图                    │
  └──────────────────────────────────────────────────────────────────┘
```

### 使用示例

```python
import onnxruntime as ort
import numpy as np

# 基础用法
session = ort.InferenceSession(
    "model.onnx",
    providers=['CUDAExecutionProvider', 'CPUExecutionProvider']
    # 优先用 GPU，不可用时回退到 CPU
)

# 查看输入输出信息
for input_info in session.get_inputs():
    print(f"Input: {input_info.name}, Shape: {input_info.shape}")

# 推理
input_data = np.random.randn(1, 3, 224, 224).astype(np.float32)
outputs = session.run(
    None,  # 获取所有输出
    {"input": input_data}
)

# 高级: 使用优化选项
session_options = ort.SessionOptions()
session_options.graph_optimization_level = ort.GraphOptimizationLevel.ORT_ENABLE_ALL
session_options.optimized_model_filepath = "model_optimized.onnx"  # 保存优化后的模型

# 高级: 从 PyTorch 导出 ONNX
import torch
model = ...  # PyTorch 模型
dummy_input = torch.randn(1, 3, 224, 224)
torch.onnx.export(
    model, dummy_input, "model.onnx",
    input_names=["input"],
    output_names=["output"],
    dynamic_axes={"input": {0: "batch_size"}, "output": {0: "batch_size"}},
    opset_version=17,
)
```

---

## 引擎对比总表

```
  ┌──────────────────────────────────────────────────────────────────────────────┐
  │                         推理引擎全面对比                                     │
  ├──────────┬──────────────┬──────────────────┬──────────────────────────────┤
  │  维度    │  TensorRT    │  TensorRT-LLM    │  ONNX Runtime               │
  ├──────────┼──────────────┼──────────────────┼──────────────────────────────┤
  │ 厂商     │ NVIDIA       │ NVIDIA           │ Microsoft                   │
  │ 适用模型 │ CNN/通用     │ LLM 专用         │ 通用 (任意模型)              │
  │ 硬件支持 │ NVIDIA GPU   │ NVIDIA GPU       │ GPU/CPU/NPU/多平台          │
  │ 优化深度 │ 极深         │ 极深 + LLM 特化   │ 中等 (可选 TRT 后端)        │
  │ 易用性   │ 中 (需编译)  │ 中               │ 高 (几行代码)               │
  │ 动态形状 │ 有限支持     │ 原生支持         │ 支持                        │
  │ 量化支持 │ INT8/FP16    │ INT4/INT8/FP8    │ INT8/FP16                   │
  │ KV Cache │ ❌           │ ✅ Paged         │ ❌                           │
  │ 编译时间 │ 分钟-小时    │ 分钟-小时        │ 秒级                        │
  │ 典型加速 │ 3-6x         │ 2-5x (vs vLLM)  │ 1.5-3x                      │
  │ 最佳场景 │ CV 生产部署  │ LLM 生产部署     │ 跨平台/快速原型              │
  │ 类比     │ F1 赛车      │ F1 赛车(LLM改装) │ 万能越野车                  │
  └──────────┴──────────────┴──────────────────┴──────────────────────────────┘

  选择建议:
  • LLM 在 NVIDIA GPU 上 → TensorRT-LLM (搭配 Triton Server)
  • CV/通用模型在 NVIDIA GPU 上 → TensorRT
  • 需要跨平台部署 → ONNX Runtime
  • 快速原型验证 → ONNX Runtime (最省事)
  • 需要极致性能 → TensorRT/TensorRT-LLM + 花时间编译调优
```

---

*下一篇：[05-llm-inference-kv-cache.md](05-llm-inference-kv-cache.md) - KV Cache 详解*

---

## 参考资料与引用

1. **NVIDIA.** *TensorRT Documentation.*  
   https://developer.nvidia.com/tensorrt

2. **ONNX Runtime.** *ONNX Runtime for Inference.*  
   https://onnxruntime.ai/

3. **NVIDIA.** *TensorRT-LLM.* — LLM 推理优化引擎  
   https://github.com/NVIDIA/TensorRT-LLM

4. **llama.cpp.** *CPU/GPU 混合推理引擎.*  
   https://github.com/ggerganov/llama.cpp
