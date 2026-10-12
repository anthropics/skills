# 模型推理部署详解

> 模型价值通过推理服务实现，推理成本往往远超训练。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [03-inference-serving/](./03-inference-serving/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | 推理与训练的差异 | [01-inference-vs-training.md](./03-inference-serving/01-inference-vs-training.md) |
> | 量化技术详解 | [02-quantization.md](./03-inference-serving/02-quantization.md) |
> | 剪枝与蒸馏 | [03-pruning-distillation.md](./03-inference-serving/03-pruning-distillation.md) |
> | 推理引擎详解 | [04-inference-engines.md](./03-inference-serving/04-inference-engines.md) |
> | LLM 推理-KV Cache | [05-llm-inference-kv-cache.md](./03-inference-serving/05-llm-inference-kv-cache.md) |
> | LLM 推理-Batching | [06-llm-inference-batching.md](./03-inference-serving/06-llm-inference-batching.md) |
> | LLM 推理-Attention 优化 | [07-llm-inference-attention.md](./03-inference-serving/07-llm-inference-attention.md) |
> | 服务框架详解 | [08-serving-frameworks.md](./03-inference-serving/08-serving-frameworks.md) |
> | 部署架构模式 | [09-deployment-architecture.md](./03-inference-serving/09-deployment-architecture.md) |
> | 性能调优 | [10-performance-tuning.md](./03-inference-serving/10-performance-tuning.md) |
> | Speculative Decoding 深入 | [11-speculative-decoding.md](./03-inference-serving/11-speculative-decoding.md) |
> | 多模态推理 | [12-multimodal-inference.md](./03-inference-serving/12-multimodal-inference.md) |
> | 端侧与边缘推理 | [13-edge-inference.md](./03-inference-serving/13-edge-inference.md) |

---

## 目录

- [推理与训练的差异](#推理与训练的差异)
- [推理优化技术](#推理优化技术)
- [推理引擎](#推理引擎)
- [LLM 推理特性](#llm-推理特性)
- [服务框架](#服务框架)
- [部署架构模式](#部署架构模式)
- [性能调优](#性能调优)
- [实战练习](#实战练习)

---

## 推理与训练的差异

### 关键差异对比

| 维度 | 训练 | 推理 |
|------|------|------|
| **目标** | 最小化 loss | 最大化吞吐/最小化延迟 |
| **Batch Size** | 越大越好 | 受延迟约束 |
| **精度** | FP32/FP16 | 可更低（INT8/INT4） |
| **内存访问** | 读写模型权重 | 只读 |
| **计算模式** | 前向+反向 | 仅前向 |
| **优化重点** | 计算效率 | 延迟 + 吞吐 |

### 推理优化空间

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       推理优化金字塔                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│                          ┌───────────┐                                  │
│                          │  应用层   │ ← Prompt 优化、Caching            │
│                          └─────┬─────┘                                  │
│                                │                                        │
│                    ┌───────────┴───────────┐                           │
│                    │      服务层           │ ← Batching、调度策略        │
│                    └───────────┬───────────┘                           │
│                                │                                        │
│              ┌─────────────────┴─────────────────┐                     │
│              │          模型层                    │ ← 量化、剪枝、蒸馏    │
│              └─────────────────┬─────────────────┘                     │
│                                │                                        │
│        ┌───────────────────────┴───────────────────────┐               │
│        │                  算子层                        │ ← Kernel 优化  │
│        └───────────────────────┬───────────────────────┘               │
│                                │                                        │
│   ┌────────────────────────────┴────────────────────────────┐          │
│   │                       硬件层                             │ ← GPU 选型│
│   └─────────────────────────────────────────────────────────┘          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 推理优化技术

### 量化（Quantization）

将高精度数值映射到低精度，减少计算量和内存带宽需求。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         量化类型对比                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   FP32 (32 bits)   FP16 (16 bits)   INT8 (8 bits)   INT4 (4 bits)      │
│   ┌────────────┐   ┌────────────┐   ┌──────────┐   ┌─────────┐         │
│   │ 1 │ 8 │ 23 │   │ 1 │ 5 │ 10 │   │  signed  │   │ signed  │         │
│   │ s │ e │  m │   │ s │ e │  m │   │  integer │   │ integer │         │
│   └────────────┘   └────────────┘   └──────────┘   └─────────┘         │
│                                                                         │
│   精度:  高           中             低            极低                  │
│   大小:  4B           2B             1B            0.5B                 │
│   速度:  1×           ~2×            ~4×           ~8×                  │
│                                                                         │
│   实际加速取决于硬件支持和算子实现                                         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

#### 量化方法分类

```python
# 1. Post-Training Quantization (PTQ) - 训练后量化
# 无需重新训练，快速但精度可能下降

from transformers import AutoModelForCausalLM
import torch

# 动态量化
model = AutoModelForCausalLM.from_pretrained("gpt2")
quantized_model = torch.quantization.quantize_dynamic(
    model, {torch.nn.Linear}, dtype=torch.qint8
)

# 2. Quantization-Aware Training (QAT) - 量化感知训练
# 训练时模拟量化，精度更高但需要重新训练

# 3. GPTQ - 基于二阶信息的权重量化
from transformers import AutoModelForCausalLM
model = AutoModelForCausalLM.from_pretrained(
    "TheBloke/Llama-2-7B-GPTQ",
    device_map="auto",
    trust_remote_code=True
)

# 4. AWQ - Activation-aware Weight Quantization
from awq import AutoAWQForCausalLM
model = AutoAWQForCausalLM.from_quantized(
    "TheBloke/Llama-2-7B-AWQ",
    fuse_layers=True
)

# 5. bitsandbytes - 动态量化
from transformers import BitsAndBytesConfig
bnb_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_quant_type="nf4",
    bnb_4bit_compute_dtype=torch.bfloat16
)
model = AutoModelForCausalLM.from_pretrained(
    "meta-llama/Llama-2-7b",
    quantization_config=bnb_config
)
```

### 剪枝（Pruning）

移除不重要的权重或神经元，减小模型规模。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         剪枝类型                                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   非结构化剪枝 (Unstructured)          结构化剪枝 (Structured)           │
│   ┌─────────────────────────┐         ┌─────────────────────────┐      │
│   │ × │ ○ │ × │ ○ │ ○ │    │         │ ○ │   │ ○ │ ○ │ ○ │    │      │
│   │ ○ │ × │ ○ │ × │ ○ │    │         │ ○ │   │ ○ │ ○ │ ○ │    │      │
│   │ × │ ○ │ × │ ○ │ × │    │         │ ○ │   │ ○ │ ○ │ ○ │    │      │
│   │ ○ │ ○ │ × │ ○ │ × │    │         │ ○ │   │ ○ │ ○ │ ○ │    │      │
│   └─────────────────────────┘         └─────────────────────────┘      │
│     单个权重置零                         整列/整行移除                   │
│     需要稀疏计算支持                     直接减小矩阵大小                 │
│     压缩比高，但加速难                   压缩比低，但易加速                │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 知识蒸馏（Knowledge Distillation）

用大模型（Teacher）指导小模型（Student）学习。

```python
# 蒸馏训练示例
import torch.nn.functional as F

def distillation_loss(student_logits, teacher_logits, labels, temperature=2.0, alpha=0.5):
    """
    student_logits: 学生模型输出
    teacher_logits: 教师模型输出 (detached)
    labels: 真实标签
    temperature: 温度参数，越高分布越平滑
    alpha: 蒸馏 loss 权重
    """
    # 软标签 loss (KL 散度)
    soft_loss = F.kl_div(
        F.log_softmax(student_logits / temperature, dim=-1),
        F.softmax(teacher_logits / temperature, dim=-1),
        reduction='batchmean'
    ) * (temperature ** 2)
    
    # 硬标签 loss (交叉熵)
    hard_loss = F.cross_entropy(student_logits, labels)
    
    return alpha * soft_loss + (1 - alpha) * hard_loss
```

---

## 推理引擎

### TensorRT

NVIDIA 的高性能推理优化器。

```python
# TensorRT 优化流程
import tensorrt as trt
import torch

# 1. 导出 ONNX
torch.onnx.export(model, dummy_input, "model.onnx")

# 2. 构建 TensorRT Engine
logger = trt.Logger(trt.Logger.INFO)
builder = trt.Builder(logger)
network = builder.create_network(
    1 << int(trt.NetworkDefinitionCreationFlag.EXPLICIT_BATCH)
)
parser = trt.OnnxParser(network, logger)

# 解析 ONNX
with open("model.onnx", "rb") as f:
    parser.parse(f.read())

# 配置优化选项
config = builder.create_builder_config()
config.set_memory_pool_limit(trt.MemoryPoolType.WORKSPACE, 1 << 30)  # 1GB
config.set_flag(trt.BuilderFlag.FP16)  # 启用 FP16

# 构建 engine
engine = builder.build_serialized_network(network, config)

# 3. 运行推理
context = engine.create_execution_context()
# ... 执行推理
```

### TensorRT-LLM

NVIDIA 专门为 LLM 优化的推理库。

```python
# TensorRT-LLM 使用示例
from tensorrt_llm import LLM, SamplingParams

# 加载优化后的模型
llm = LLM(model="meta-llama/Llama-2-7b-hf")

# 推理
prompts = ["What is AI infrastructure?"]
sampling_params = SamplingParams(temperature=0.8, top_p=0.95, max_tokens=256)
outputs = llm.generate(prompts, sampling_params)

for output in outputs:
    print(output.outputs[0].text)
```

### ONNX Runtime

跨平台的推理引擎。

```python
import onnxruntime as ort
import numpy as np

# 加载模型
session = ort.InferenceSession(
    "model.onnx",
    providers=['CUDAExecutionProvider', 'CPUExecutionProvider']
)

# 推理
inputs = {"input": np.random.randn(1, 3, 224, 224).astype(np.float32)}
outputs = session.run(None, inputs)
```

### 推理引擎对比

| 特性 | TensorRT | TensorRT-LLM | ONNX Runtime | PyTorch |
|------|----------|--------------|--------------|---------|
| **硬件支持** | NVIDIA GPU | NVIDIA GPU | 多平台 | 多平台 |
| **优化程度** | 极高 | 极高 | 中 | 低 |
| **LLM 优化** | 有限 | 专门优化 | 有限 | 基础 |
| **易用性** | 低 | 中 | 高 | 高 |
| **延迟** | 最低 | 最低 | 中 | 较高 |

---

## LLM 推理特性

### Autoregressive 生成的挑战

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    LLM 推理的独特挑战                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   自回归生成: 每次只生成一个 token                                        │
│                                                                         │
│   Prompt: "What is"                                                     │
│                                                                         │
│   Step 1: "What is" → " AI"        (处理 2 tokens，生成 1 token)        │
│   Step 2: "What is AI" → "?"       (处理 3 tokens，生成 1 token)        │
│   Step 3: "What is AI?" → " AI"    (处理 4 tokens，生成 1 token)        │
│   ...                                                                   │
│                                                                         │
│   问题:                                                                 │
│   1. 每步都要重新计算所有 token 的 Attention? → KV Cache 解决            │
│   2. 生成阶段 batch_size=1，GPU 利用率低? → Continuous Batching 解决     │
│   3. KV Cache 太大，显存放不下? → PagedAttention 解决                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### KV Cache

缓存已计算的 Key 和 Value，避免重复计算。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         KV Cache 原理                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   无 KV Cache (每步重复计算):                                            │
│                                                                         │
│   Step 1: Q₁, K₁, V₁ → Attention                                       │
│   Step 2: Q₁, Q₂, K₁, K₂, V₁, V₂ → Attention  (K₁,V₁ 重复计算)         │
│   Step 3: Q₁,Q₂,Q₃, K₁,K₂,K₃, V₁,V₂,V₃ → Attention  (重复更多)        │
│                                                                         │
│   有 KV Cache:                                                          │
│                                                                         │
│   Step 1: Q₁ → K₁, V₁ (存入 cache)                                     │
│   Step 2: Q₂ → K₂, V₂ (存入 cache), 使用 cache 中的 K₁,V₁             │
│   Step 3: Q₃ → K₃, V₃ (存入 cache), 使用 cache 中的 K₁,K₂,V₁,V₂       │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                      KV Cache 存储                               │   │
│   │                                                                 │   │
│   │   Layer 0: [K₁, K₂, K₃, ...]  [V₁, V₂, V₃, ...]                │   │
│   │   Layer 1: [K₁, K₂, K₃, ...]  [V₁, V₂, V₃, ...]                │   │
│   │   ...                                                           │   │
│   │   Layer N: [K₁, K₂, K₃, ...]  [V₁, V₂, V₃, ...]                │   │
│   │                                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   显存占用: 2 × num_layers × seq_len × hidden_size × batch_size         │
│   Llama-2 7B, seq_len=4096, batch=32: ~35GB KV Cache!                  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Continuous Batching

动态批处理，提高 GPU 利用率。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Static vs Continuous Batching                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Static Batching (传统):                                               │
│   ┌─────────────────────────────────────────────────────────┐          │
│   │ Time →                                                   │          │
│   │                                                          │          │
│   │ Req 1: ████████████░░░░░░░░  (生成完成，等待其他请求)      │          │
│   │ Req 2: ████████████████████  (最长请求)                   │          │
│   │ Req 3: ████████░░░░░░░░░░░░  (生成完成，等待)             │          │
│   │                                                          │          │
│   │        ↑ 所有请求必须等最长的完成才能返回下一批            │          │
│   │        ↑ 短请求浪费大量 GPU 时间                          │          │
│   └─────────────────────────────────────────────────────────┘          │
│                                                                         │
│   Continuous Batching (迭代级调度):                                     │
│   ┌─────────────────────────────────────────────────────────┐          │
│   │ Time →                                                   │          │
│   │                                                          │          │
│   │ Req 1: ████████████ → 完成，立即返回                      │          │
│   │ Req 2: █████████████████████                             │          │
│   │ Req 3: ████████ → 完成                                   │          │
│   │ Req 4:         ███████████████ → 新请求立即加入          │          │
│   │ Req 5:              █████████████████ → 继续加入         │          │
│   │                                                          │          │
│   │        ↑ 每个 token 生成后都可以动态调整 batch            │          │
│   │        ↑ GPU 始终满载，吞吐大幅提升                        │          │
│   └─────────────────────────────────────────────────────────┘          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### PagedAttention（vLLM）

借鉴操作系统虚拟内存的分页机制管理 KV Cache。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       PagedAttention 原理                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   传统 KV Cache (连续分配):                                              │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ GPU Memory                                                       │   │
│   │ ┌────────────────────┬──────────┬───────────────────────────┐  │   │
│   │ │ Req 1 KV (预分配)   │ Req 2 KV │ Req 3 KV (预分配最大长度)  │  │   │
│   │ └────────────────────┴──────────┴───────────────────────────┘  │   │
│   │   ████████░░░░░░░░░░  ████░░░░░  █░░░░░░░░░░░░░░░░░░░░░░░░░   │   │
│   │   ↑ 实际使用          ↑ 浪费的预分配空间                        │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│   问题: 必须预分配最大序列长度，显存碎片严重                              │
│                                                                         │
│   PagedAttention (分页分配):                                            │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ 逻辑视图 (每个请求)                物理存储 (GPU)                 │   │
│   │                                                                 │   │
│   │ Req 1: [Block 0][Block 1]         ┌──┬──┬──┬──┬──┬──┬──┬──┐   │   │
│   │        ↓        ↓                 │B0│B1│B2│B3│B4│B5│B6│B7│   │   │
│   │ Req 2: [Block 2]                  │R1│R1│R2│R3│R3│R4│  │  │   │   │
│   │        ↓                          └──┴──┴──┴──┴──┴──┴──┴──┘   │   │
│   │ Req 3: [Block 3][Block 4]              ↑ 物理 block 可不连续    │   │
│   │        ↓        ↓                      ↑ 按需分配，无浪费       │   │
│   │ Req 4: [Block 5]                                               │   │
│   │                                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   优势:                                                                 │
│   - 按需分配，无需预分配最大长度                                          │
│   - 近零显存浪费 (碎片 < 4%)                                             │
│   - 支持更大 batch size，吞吐提升 2-4×                                   │
│   - 支持 Copy-on-Write，加速 beam search                                │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### FlashAttention

优化 Attention 的内存访问模式，减少 HBM 读写。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    FlashAttention vs Standard Attention                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Standard Attention:                                                   │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                                                                 │   │
│   │   HBM → Q, K, V                                                │   │
│   │         ↓                                                       │   │
│   │   S = Q @ K.T  →  写入 HBM (O(N²) 大小!)                        │   │
│   │         ↓                                                       │   │
│   │   P = softmax(S)  →  写入 HBM                                  │   │
│   │         ↓                                                       │   │
│   │   O = P @ V  →  写入 HBM                                       │   │
│   │                                                                 │   │
│   │   问题: 中间结果 S, P 是 O(N²)，频繁读写 HBM                     │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   FlashAttention (Tiling + 重计算):                                     │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                                                                 │   │
│   │   for each tile of Q (in SRAM):                                │   │
│   │       for each tile of K, V (in SRAM):                         │   │
│   │           # 全部在 SRAM 中计算                                   │   │
│   │           S_tile = Q_tile @ K_tile.T                           │   │
│   │           P_tile = softmax(S_tile)  # 在线 softmax              │   │
│   │           O_tile += P_tile @ V_tile                            │   │
│   │       end                                                       │   │
│   │   end                                                           │   │
│   │   write O to HBM  # 只写最终结果                                │   │
│   │                                                                 │   │
│   │   优势: 避免写入 O(N²) 的中间结果，IO 复杂度 O(N)               │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   加速效果: 2-4× 速度提升，显存节省显著                                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Speculative Decoding

用小模型草稿，大模型验证，加速生成。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Speculative Decoding 原理                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   传统自回归:                                                            │
│   ┌───────────────────────────────────────────────────────────────┐     │
│   │ Token 1 → [Large Model] → Token 2 → [Large Model] → Token 3   │     │
│   │ 每个 token 都需要完整的大模型前向                               │     │
│   └───────────────────────────────────────────────────────────────┘     │
│                                                                         │
│   Speculative Decoding:                                                 │
│   ┌───────────────────────────────────────────────────────────────┐     │
│   │                                                               │     │
│   │   Step 1: 小模型快速生成 K 个草稿 token                        │     │
│   │   ┌──────────────────────────────────────┐                    │     │
│   │   │ [Draft Model] → t1, t2, t3, t4, t5   │  (便宜)            │     │
│   │   └──────────────────────────────────────┘                    │     │
│   │                                                               │     │
│   │   Step 2: 大模型并行验证所有草稿                               │     │
│   │   ┌──────────────────────────────────────┐                    │     │
│   │   │ [Target Model] 并行处理 t1-t5        │  (一次前向)        │     │
│   │   └──────────────────────────────────────┘                    │     │
│   │                                                               │     │
│   │   Step 3: 接受匹配的 token，从第一个不匹配处重新开始           │     │
│   │   假设 t1, t2, t3 被接受, t4 被拒绝                           │     │
│   │   → 实际生成 t1, t2, t3 + 大模型修正的 t4                     │     │
│   │                                                               │     │
│   └───────────────────────────────────────────────────────────────┘     │
│                                                                         │
│   加速原理: 如果接受率高，一次大模型前向生成多个 token                     │
│   典型加速: 2-3×，取决于草稿模型质量                                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 服务框架

### vLLM

最流行的 LLM 推理框架，PagedAttention 的发明者。

```python
from vllm import LLM, SamplingParams

# 初始化
llm = LLM(
    model="meta-llama/Llama-2-7b-chat-hf",
    tensor_parallel_size=2,  # 2 GPU 张量并行
    dtype="auto",  # 自动选择精度
    gpu_memory_utilization=0.9,  # 显存利用率
)

# 批量推理
prompts = [
    "What is machine learning?",
    "Explain quantum computing",
    "Write a poem about AI",
]

sampling_params = SamplingParams(
    temperature=0.8,
    top_p=0.95,
    max_tokens=256,
)

outputs = llm.generate(prompts, sampling_params)

for output in outputs:
    print(output.outputs[0].text)

# OpenAI 兼容 API 服务
# python -m vllm.entrypoints.openai.api_server \
#     --model meta-llama/Llama-2-7b-chat-hf \
#     --port 8000
```

### Text Generation Inference (TGI)

Hugging Face 的生产级推理服务器。

```bash
# Docker 启动
docker run --gpus all --shm-size 1g -p 8080:80 \
    ghcr.io/huggingface/text-generation-inference:latest \
    --model-id meta-llama/Llama-2-7b-chat-hf \
    --num-shard 2 \
    --quantize bitsandbytes-nf4

# 调用
curl 127.0.0.1:8080/generate \
    -X POST \
    -H 'Content-Type: application/json' \
    -d '{"inputs":"What is AI?","parameters":{"max_new_tokens":50}}'
```

### Triton Inference Server

NVIDIA 的通用推理服务器，支持多模型、多框架。

```python
# model_repository/
# └── llama/
#     ├── config.pbtxt
#     └── 1/
#         └── model.plan  (TensorRT engine)

# config.pbtxt
"""
name: "llama"
platform: "tensorrt_llm"
max_batch_size: 64
input [
  {
    name: "input_ids"
    data_type: TYPE_INT32
    dims: [ -1 ]
  }
]
output [
  {
    name: "output_ids"
    data_type: TYPE_INT32
    dims: [ -1 ]
  }
]
instance_group [
  {
    count: 1
    kind: KIND_GPU
    gpus: [ 0 ]
  }
]
"""

# 启动服务
# tritonserver --model-repository=/models
```

### 服务框架对比

| 特性 | vLLM | TGI | Triton | Ollama |
|------|------|-----|--------|--------|
| **易用性** | 高 | 高 | 中 | 极高 |
| **性能** | 极高 | 高 | 极高 | 中 |
| **PagedAttention** | ✅ | ✅ | ✅ | ❌ |
| **Continuous Batching** | ✅ | ✅ | ✅ | ❌ |
| **量化支持** | AWQ/GPTQ | bnb/GPTQ | 多种 | GGUF |
| **OpenAI API** | ✅ | ✅ | ❌ | ✅ |
| **多模型** | ❌ | ❌ | ✅ | ✅ |
| **适用场景** | LLM 服务 | LLM 服务 | 通用 ML | 本地开发 |

---

## 部署架构模式

### 单模型单实例

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    最简单架构：单模型单实例                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────┐      ┌─────────────────────┐      ┌─────────────────┐    │
│   │ Client  │ ──→  │   Load Balancer     │ ──→  │  vLLM Server    │    │
│   │         │      │   (nginx/ALB)       │      │  (GPU × 1)      │    │
│   └─────────┘      └─────────────────────┘      └─────────────────┘    │
│                                                                         │
│   适用: 小规模、开发测试                                                 │
│   限制: 单点故障、吞吐受限                                               │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 多副本负载均衡

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    生产架构：多副本 + 负载均衡                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│                          ┌───────────────┐                              │
│                          │     Nginx     │                              │
│                          │  Load Balancer│                              │
│                          └───────┬───────┘                              │
│                                  │                                      │
│            ┌─────────────────────┼─────────────────────┐                │
│            │                     │                     │                │
│            ▼                     ▼                     ▼                │
│   ┌─────────────────┐   ┌─────────────────┐   ┌─────────────────┐      │
│   │  vLLM Pod 0     │   │  vLLM Pod 1     │   │  vLLM Pod 2     │      │
│   │  GPU × 2 (TP)   │   │  GPU × 2 (TP)   │   │  GPU × 2 (TP)   │      │
│   └─────────────────┘   └─────────────────┘   └─────────────────┘      │
│                                                                         │
│   K8s HPA 根据 GPU 利用率/请求队列长度自动扩缩                            │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 分离 Prefill 和 Decode（PD 分离）

#### 为什么要分离？——两种截然不同的工作模式

LLM 推理有两个阶段，它们的计算特性**完全相反**：

| 特性 | Prefill（首次填充） | Decode（逐 token 生成） |
|------|-------------------|----------------------|
| **做什么** | 一次性处理整个 prompt | 每步生成 1 个 token |
| **计算量** | 巨大（处理数百~数千 token） | 极小（只算 1 个新 token） |
| **瓶颈** | **计算密集**（GPU 算力） | **内存密集**（显存带宽） |
| **GPU 利用率** | 高（80-95%） | 低（10-30%） |
| **耗时占比** | 短（一次完成） | 长（token 数 × 单步延迟） |
| **对应指标** | TTFT（首 token 延迟） | TPS（生成速度） |

> **生活类比**：想象一个餐厅——Prefill 是"后厨备菜"（集中、计算密集、一次性搞定），Decode 是"服务员一道道上菜"（反复跑，每次就端一盘，瓶颈在走路而非做菜）。把后厨和传菜分开管理，效率才最高。

#### 混合部署的问题

在传统架构中，Prefill 和 Decode 在同一块 GPU 上交替执行。问题是：

```
同一 GPU 上的 Prefill-Decode 冲突:

时间线 ──────────────────────────────────────────────────────────→

GPU 0: [==Prefill(Req-A)==][.Decode(A).][.Decode(A).][==Prefill(Req-B)==][.Decode(B).]
                                                      ↑
                                                新请求的 Prefill
                                                "插队"打断了 A 的 Decode
                                                → Req-A 的生成延迟突然飙升！

问题 1: Prefill 是大块计算，会抢占 GPU，导致正在 Decode 的请求延迟波动
问题 2: Decode 阶段 GPU 利用率很低（~20%），但 GPU 不能分给别人
问题 3: Prefill 需要大算力，Decode 需要大显存带宽——同一 GPU 无法同时优化
```

> **量化说明**：一个 4K token prompt 的 Prefill 耗时约 200ms（在 A100 上），期间会占满 GPU 算力。如果此时有 10 个请求在 Decode 阶段，它们全部被"暂停"等待，每个请求的 TPS 骤降——这就是 P99 延迟恶化的根源。

#### PD 分离架构

核心思想：让**不同硬件**做**各自擅长的事**。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Prefill-Decode 分离架构                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────┐      ┌─────────────────────────────────────────────┐      │
│   │ Client  │ ──→  │              Router                         │      │
│   └─────────┘      └───────────────────┬─────────────────────────┘      │
│                                        │                                │
│                    ┌───────────────────┴───────────────────┐           │
│                    │                                       │           │
│                    ▼                                       ▼           │
│   ┌───────────────────────────────┐     ┌───────────────────────────┐  │
│   │      Prefill Workers          │     │      Decode Workers       │  │
│   │   高算力 GPU (H100 SXM)       │     │   高显存带宽 GPU           │  │
│   │                               │     │                           │  │
│   │   输入: prompt tokens          │     │   输入: KV Cache + 上下文  │  │
│   │   输出: KV Cache + 第 1 token  │ ──→ │   输出: 后续 tokens       │  │
│   │                               │     │                           │  │
│   │   特点: 短时高算力任务          │     │   特点: 长时低算力任务     │  │
│   │   GPU 利用率: 80-95%          │     │   显存带宽利用率: 高       │  │
│   └───────────────────────────────┘     └───────────────────────────┘  │
│                           │                                            │
│                    KV Cache 传输                                       │
│                (高速网络: RDMA / NVLink-over-Fabric)                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

#### 请求生命周期

```
一次请求的完整旅程:

1. 请求到达 Router
   "请帮我写一首关于春天的诗"
        │
        ▼
2. Router → Prefill Worker (选一个空闲的)
   Prefill Worker 处理 prompt:
   - 一次性计算所有 prompt token 的 attention
   - 生成完整的 KV Cache (大小 ∝ prompt长度 × 层数 × 隐藏维度)
   - 输出第一个 token: "春"
   - 耗时: ~100-500ms (取决于 prompt 长度)
        │
        ▼
3. KV Cache 通过高速网络传输到 Decode Worker
   传输量: 7B 模型, 4K prompt → KV Cache ≈ 2GB
   RDMA 传输: ~10-50ms (100Gbps 网络)
        │
        ▼
4. Decode Worker 接管，逐 token 生成
   "春" → "风" → "拂" → "面" → "花" → "开" → ...
   每个 token 耗时: ~20-50ms
   持续: 数百 ms 到数秒
        │
        ▼
5. 流式返回给 Client
```

#### KV Cache 传输：PD 分离的关键挑战

PD 分离能否成功，取决于 KV Cache 传输速度能否足够快：

```
KV Cache 大小估算:

  KV Cache = 2 × num_layers × hidden_dim × seq_len × dtype_size

  LLaMA-7B (32层, hidden=4096, FP16):
    prompt 2K tokens → KV Cache ≈ 1GB
    prompt 4K tokens → KV Cache ≈ 2GB
    prompt 8K tokens → KV Cache ≈ 4GB

  LLaMA-70B (80层, hidden=8192, FP16):
    prompt 4K tokens → KV Cache ≈ 20GB!

传输时间:
  ┌────────────────────────────────────────────────────────┐
  │  网络类型        带宽       传输 2GB KV Cache 耗时       │
  │  ─────────     ──────     ─────────────────────        │
  │  25Gbps TCP    ~2 GB/s    ~1000ms  ← 太慢，不可用      │
  │  100Gbps RDMA  ~12 GB/s   ~170ms   ← 勉强可用          │
  │  200Gbps RDMA  ~24 GB/s   ~85ms    ← 推荐              │
  │  400Gbps RDMA  ~48 GB/s   ~42ms    ← 理想              │
  │  NVLink(节点内) ~600 GB/s  ~3ms     ← 最优              │
  └────────────────────────────────────────────────────────┘
```

> **结论**：PD 分离需要至少 100Gbps RDMA 网络才实用。如果用普通 TCP 网络，KV Cache 传输延迟就超过了 Prefill 本身的耗时，分离反而更慢。

#### 什么时候该用 PD 分离？

| 场景 | 是否适合 | 原因 |
|------|---------|------|
| **长 prompt + 短输出**（RAG/总结） | ✅ 最适合 | Prefill 重、Decode 轻，分离收益大 |
| **高并发在线服务** | ✅ 适合 | 消除 Prefill 对 Decode 的干扰，P99 显著改善 |
| **短 prompt + 长输出**（创作） | ⚠️ 收益有限 | Prefill 本身就很快，分离的额外传输成本不划算 |
| **单用户低并发** | ❌ 不适合 | 无互相干扰问题，增加传输延迟反而更慢 |
| **无 RDMA 网络** | ❌ 不可用 | KV Cache 传输太慢 |

#### 代表系统

| 系统 | 特点 |
|------|------|
| **Splitwise** (微软) | 首个提出 PD 分离的论文，证明吞吐提升 1.4× |
| **DistServe** (北大) | 优化了 KV Cache 传输调度，支持异构 GPU |
| **Mooncake** (月之暗面) | Kimi 的生产系统，用 KVCache-centric 分离架构 |
| **TensorRT-LLM** | NVIDIA 方案，支持通过配置开启 PD 分离模式 |

---

## 性能调优

### 关键性能指标

| 指标 | 定义 | 优化方向 |
|------|------|----------|
| **TTFT** | Time To First Token | 减少 prefill 时间 |
| **TPS** | Tokens Per Second (每请求) | 优化单请求延迟 |
| **Throughput** | 总 tokens/秒 | 增加并发 |
| **Latency P99** | 99 分位延迟 | 减少长尾 |

### 调优 Checklist

```python
# 1. 选择合适的量化
# INT4 > INT8 > FP16，在精度可接受的前提下选择最低

# 2. 调整 batch size
# vLLM 自动管理，可通过 max_num_seqs 控制
llm = LLM(model="...", max_num_seqs=256)

# 3. 启用 tensor parallel
llm = LLM(model="...", tensor_parallel_size=4)

# 4. 调整 GPU 显存利用率
llm = LLM(model="...", gpu_memory_utilization=0.95)

# 5. 使用合适的采样参数
sampling_params = SamplingParams(
    temperature=0,  # greedy 最快
    max_tokens=256,  # 限制最大生成长度
)

# 6. 开启 Speculative Decoding（如果有草稿模型）
llm = LLM(
    model="large-model",
    speculative_model="small-draft-model",
    num_speculative_tokens=5
)
```

### 监控与可观测性

```python
# Prometheus 指标（vLLM 自带）
# - vllm:num_requests_running
# - vllm:num_requests_waiting
# - vllm:gpu_cache_usage_perc
# - vllm:generation_tokens_total

# Grafana Dashboard 关键面板
# 1. 请求队列长度 (排队等待)
# 2. GPU KV Cache 使用率
# 3. Token 生成速率
# 4. 延迟分布 (P50/P95/P99)
```

---

## 实战练习

### 练习 1：vLLM 服务部署

```python
# serve.py
from vllm import LLM, SamplingParams
from fastapi import FastAPI
from pydantic import BaseModel
import uvicorn

app = FastAPI()

# 全局加载模型
llm = LLM(model="Qwen/Qwen2-0.5B", dtype="auto")

class GenerateRequest(BaseModel):
    prompt: str
    max_tokens: int = 256
    temperature: float = 0.7

@app.post("/generate")
def generate(request: GenerateRequest):
    sampling_params = SamplingParams(
        temperature=request.temperature,
        max_tokens=request.max_tokens
    )
    outputs = llm.generate([request.prompt], sampling_params)
    return {"text": outputs[0].outputs[0].text}

if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)

# 测试: curl -X POST "http://localhost:8000/generate" \
#       -H "Content-Type: application/json" \
#       -d '{"prompt": "Hello, how are you?"}'
```

### 练习 2：量化模型对比

```python
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
import time

model_name = "meta-llama/Llama-2-7b-hf"
prompt = "The future of AI is"

def benchmark(model, tokenizer, name):
    inputs = tokenizer(prompt, return_tensors="pt").to(model.device)
    
    # 预热
    model.generate(**inputs, max_new_tokens=10)
    
    # 计时
    start = time.time()
    for _ in range(10):
        outputs = model.generate(**inputs, max_new_tokens=50)
    elapsed = time.time() - start
    
    tokens_generated = 50 * 10
    print(f"{name}: {tokens_generated / elapsed:.1f} tokens/sec")

# FP16
model_fp16 = AutoModelForCausalLM.from_pretrained(
    model_name, torch_dtype=torch.float16, device_map="auto"
)
tokenizer = AutoTokenizer.from_pretrained(model_name)
benchmark(model_fp16, tokenizer, "FP16")

# INT8 (bitsandbytes)
from transformers import BitsAndBytesConfig
bnb_config = BitsAndBytesConfig(load_in_8bit=True)
model_int8 = AutoModelForCausalLM.from_pretrained(
    model_name, quantization_config=bnb_config, device_map="auto"
)
benchmark(model_int8, tokenizer, "INT8")

# INT4
bnb_config_4bit = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_compute_dtype=torch.float16
)
model_int4 = AutoModelForCausalLM.from_pretrained(
    model_name, quantization_config=bnb_config_4bit, device_map="auto"
)
benchmark(model_int4, tokenizer, "INT4")
```

### 练习 3：性能压测

```python
# benchmark.py
import asyncio
import aiohttp
import time
from statistics import mean, stdev

async def send_request(session, url, prompt):
    start = time.time()
    async with session.post(url, json={"prompt": prompt, "max_tokens": 100}) as resp:
        result = await resp.json()
    latency = time.time() - start
    return latency, len(result.get("text", "").split())

async def benchmark(url, num_requests=100, concurrency=10):
    connector = aiohttp.TCPConnector(limit=concurrency)
    async with aiohttp.ClientSession(connector=connector) as session:
        prompts = [f"Question {i}: What is AI?" for i in range(num_requests)]
        
        start = time.time()
        tasks = [send_request(session, url, p) for p in prompts]
        results = await asyncio.gather(*tasks)
        total_time = time.time() - start
        
        latencies = [r[0] for r in results]
        tokens = [r[1] for r in results]
        
        print(f"Total requests: {num_requests}")
        print(f"Concurrency: {concurrency}")
        print(f"Total time: {total_time:.2f}s")
        print(f"Throughput: {num_requests / total_time:.1f} req/s")
        print(f"Latency (mean): {mean(latencies):.2f}s")
        print(f"Latency (std): {stdev(latencies):.2f}s")
        print(f"Tokens/sec: {sum(tokens) / total_time:.1f}")

if __name__ == "__main__":
    asyncio.run(benchmark("http://localhost:8000/generate"))
```

---

## 参考资料与引用

### 必读论文

1. Kwon, W., et al. (2023). *Efficient Memory Management for Large Language Model Serving with PagedAttention*. SOSP 2023. arXiv:2309.06180. https://arxiv.org/abs/2309.06180
2. Dao, T., et al. (2022). *FlashAttention: Fast and Memory-Efficient Exact Attention with IO-Awareness*. arXiv:2205.14135. https://arxiv.org/abs/2205.14135
3. Dao, T. (2023). *FlashAttention-2: Faster Attention with Better Parallelism and Work Partitioning*. arXiv:2307.08691. https://arxiv.org/abs/2307.08691
4. Leviathan, Y., et al. (2022). *Fast Inference from Transformers via Speculative Decoding*. arXiv:2211.17192. https://arxiv.org/abs/2211.17192
5. Frantar, E., et al. (2022). *GPTQ: Accurate Post-Training Quantization for Generative Pre-trained Transformers*. arXiv:2210.17323. https://arxiv.org/abs/2210.17323
6. Lin, J., et al. (2023). *AWQ: Activation-aware Weight Quantization for LLM Compression and Acceleration*. arXiv:2306.00978. https://arxiv.org/abs/2306.00978

### 官方文档

- [vLLM Documentation](https://docs.vllm.ai/). UC Berkeley.
- [TensorRT-LLM GitHub](https://github.com/NVIDIA/TensorRT-LLM). NVIDIA.
- [Text Generation Inference (TGI)](https://huggingface.co/docs/text-generation-inference). HuggingFace.
- [Triton Inference Server Documentation](https://docs.nvidia.com/deeplearning/triton-inference-server/). NVIDIA.

### 推荐博客

- [vLLM Blog](https://blog.vllm.ai/).
- [Optimizing LLM Inference](https://huggingface.co/blog/optimize-llm). HuggingFace.

---

*下一篇：[04-mlops-llmops.md](04-mlops-llmops.md) - MLOps/LLMOps 详解*
