# 推理引擎详解

> TensorRT、TensorRT-LLM、ONNX Runtime 的原理和使用。

## 推理引擎对比

| 引擎 | 厂商 | 特点 | 适用场景 |
|------|------|------|----------|
| TensorRT | NVIDIA | 极致优化 | CV/通用模型 |
| TensorRT-LLM | NVIDIA | LLM 专用 | 大语言模型 |
| ONNX Runtime | Microsoft | 跨平台 | 多硬件部署 |

## TensorRT

### 核心优化

```
1. 层融合 (Layer Fusion)
   Conv + BN + ReLU → 单个算子

2. 精度校准
   FP32 → FP16/INT8 自动转换

3. 内核自动调优
   针对特定 GPU 选择最优实现

4. 内存优化
   复用中间张量内存
```

### 使用示例

```python
import tensorrt as trt

# 构建引擎 (TensorRT 8.x+)
builder = trt.Builder(logger)
network = builder.create_network(
    1 << int(trt.NetworkDefinitionCreationFlag.EXPLICIT_BATCH)
)
parser = trt.OnnxParser(network, logger)

with open("model.onnx", "rb") as f:
    parser.parse(f.read())

config = builder.create_builder_config()
config.set_flag(trt.BuilderFlag.FP16)

serialized_engine = builder.build_serialized_network(network, config)
```

## TensorRT-LLM

### 特点

- LLM 专用优化 (KV Cache, Paged Attention)
- 支持张量并行和流水线并行
- 集成量化 (INT8/FP8/INT4)

### 使用示例

```python
from tensorrt_llm import LLM

llm = LLM(model="meta-llama/Llama-2-7b-hf")
output = llm.generate("What is AI?")
```

## ONNX Runtime

### 优势

- 跨平台 (CPU/GPU/NPU)
- 支持多种模型格式
- 易于集成

```python
import onnxruntime as ort

session = ort.InferenceSession(
    "model.onnx",
    providers=['CUDAExecutionProvider']
)

outputs = session.run(None, {"input": input_data})
```

---

*下一篇：[05-llm-inference-kv-cache.md](05-llm-inference-kv-cache.md) - KV Cache 详解*
