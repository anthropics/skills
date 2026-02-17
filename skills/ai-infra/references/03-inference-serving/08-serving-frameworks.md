# 服务框架详解

> vLLM、SGLang、TGI、Triton 的对比和使用。

## 框架对比

| 框架 | 开发者 | 特点 | 适用场景 |
|------|--------|------|----------|
| **vLLM** | UC Berkeley | PagedAttention | 高并发 LLM |
| **SGLang** | LMSYS | RadixAttention, 结构化生成 | 复杂推理链、Agent |
| **TGI** | Hugging Face | 易用性 | 快速部署 |
| **Triton** | NVIDIA | 企业级 | 多模型服务 |

## vLLM

### 特点

- PagedAttention 显存管理
- Continuous Batching
- 高吞吐量

### 使用

```python
from vllm import LLM, SamplingParams

llm = LLM(model="meta-llama/Llama-2-7b-hf")

prompts = ["Hello, my name is", "The future of AI is"]
sampling_params = SamplingParams(temperature=0.8, max_tokens=100)

outputs = llm.generate(prompts, sampling_params)
for output in outputs:
    print(output.outputs[0].text)
```

### 服务器模式

```bash
python -m vllm.entrypoints.openai.api_server \
    --model meta-llama/Llama-2-7b-hf \
    --port 8000

# 兼容 OpenAI API
curl http://localhost:8000/v1/completions \
    -H "Content-Type: application/json" \
    -d '{"model": "meta-llama/Llama-2-7b-hf", "prompt": "Hello"}'
```

## SGLang

### 特点

- **RadixAttention**：基于前缀树 (Radix Tree) 的 KV Cache 复用
- **结构化生成**：原生支持 JSON Schema、正则约束输出
- **多调用优化**：编译多轮 LLM 调用为高效执行图
- **高吞吐低延迟**：大量并发请求下性能优于 vLLM

### RadixAttention 原理

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    RadixAttention (前缀树 KV Cache)                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   传统 KV Cache: 每个请求独立的 KV Cache                                   │
│   Request 1: "You are a helpful assistant. What is AI?"                    │
│   Request 2: "You are a helpful assistant. Explain ML."                    │
│   → 两份完整的 KV Cache (system prompt 重复计算)                           │
│                                                                             │
│   RadixAttention: 用前缀树共享公共前缀                                     │
│                                                                             │
│   Radix Tree:                                                               │
│                "You are a helpful assistant."                               │
│                     [共享 KV Cache]                                         │
│                    /                \                                        │
│           "What is AI?"      "Explain ML."                                  │
│          [增量 KV Cache]    [增量 KV Cache]                                 │
│                                                                             │
│   优势:                                                                     │
│   • 多轮对话: system prompt 只计算一次                                     │
│   • Few-shot: 共享示例的 KV Cache                                          │
│   • Tree-of-thought: 共享推理分支前缀                                      │
│   • TTFT 显著降低 (共享前缀部分跳过 Prefill)                               │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 使用

```python
# 服务器模式 (兼容 OpenAI API)
# python -m sglang.launch_server --model meta-llama/Llama-3.1-8B-Instruct --port 30000

import openai
client = openai.Client(base_url="http://localhost:30000/v1", api_key="EMPTY")

response = client.chat.completions.create(
    model="meta-llama/Llama-3.1-8B-Instruct",
    messages=[{"role": "user", "content": "What is AI?"}],
    temperature=0.8,
    max_tokens=100,
)
```

```python
# SGLang 原生前端 (结构化生成)
import sglang as sgl

@sgl.function
def multi_turn_qa(s, question1, question2):
    s += sgl.system("You are a helpful assistant.")
    s += sgl.user(question1)
    s += sgl.assistant(sgl.gen("answer1", max_tokens=256))
    s += sgl.user(question2)
    s += sgl.assistant(sgl.gen("answer2", max_tokens=256))

# 批量执行，自动利用 RadixAttention 共享前缀
results = multi_turn_qa.run_batch([
    {"question1": "What is AI?", "question2": "Give examples."},
    {"question1": "What is AI?", "question2": "What are risks?"},
    # 两个请求共享 "What is AI?" 的前缀 KV Cache
])
```

---

## Text Generation Inference (TGI)

### 特点

- Hugging Face 官方
- 支持量化
- 简单易用

### 使用

```bash
# Docker 部署
docker run --gpus all \
    -p 8080:80 \
    -v ~/.cache/huggingface:/data \
    ghcr.io/huggingface/text-generation-inference:latest \
    --model-id meta-llama/Llama-2-7b-hf

# 调用
curl localhost:8080/generate \
    -X POST \
    -d '{"inputs":"What is AI?","parameters":{"max_new_tokens":100}}' \
    -H 'Content-Type: application/json'
```

## Triton Inference Server

### 特点

- 多模型服务
- 多框架支持
- 企业级功能

### 模型配置

```
# models/llama/config.pbtxt
name: "llama"
backend: "python"
max_batch_size: 8

input [
  {name: "input_ids", data_type: TYPE_INT64, dims: [-1]}
]
output [
  {name: "output_ids", data_type: TYPE_INT64, dims: [-1]}
]
```

## 选择建议

| 场景 | 推荐 |
|------|------|
| 高并发 LLM | vLLM 或 SGLang |
| 多轮对话 / Agent | SGLang (RadixAttention) |
| 结构化 JSON 输出 | SGLang |
| 快速原型 | TGI |
| 企业多模型 | Triton |
| OpenAI 兼容 | vLLM 或 SGLang |

---

*下一篇：[09-deployment-architecture.md](09-deployment-architecture.md) - 部署架构模式*
