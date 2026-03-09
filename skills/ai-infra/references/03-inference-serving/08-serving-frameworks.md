# 服务框架详解

> vLLM、SGLang、TGI、Triton — 每个框架的设计哲学和核心技术。

## 为什么需要专门的 LLM 服务框架

```
  类比: 为什么餐厅需要专业的点单系统，而不是直接让厨师接电话？

  "直接用 PyTorch 起个 Flask 服务":
    → 只能处理一个请求 (串行)
    → 没有 Continuous Batching (GPU 利用率 5%)
    → 没有 PagedAttention (显存浪费 60%)
    → 没有量化/FlashAttention 集成

  专业服务框架 = 餐厅管理系统:
    前台接单 (HTTP Server) + 排队调度 (Scheduler) +
    后厨生产 (Inference Engine) + 并行出餐 (Streaming)
```

## 框架对比

| 框架 | 开发者 | 核心技术 | 类比 |
|------|--------|----------|------|
| **vLLM** | UC Berkeley | PagedAttention | 高效仓库管理 |
| **SGLang** | LMSYS | RadixAttention | 智能前缀共享 |
| **TGI** | Hugging Face | 易集成 | 即插即用 |
| **Triton** | NVIDIA | 多模型服务 | 企业级平台 |

## vLLM

### 设计哲学

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  vLLM 的核心贡献: PagedAttention                                  │
  │                                                                  │
  │  灵感来源: 操作系统的虚拟内存管理                                 │
  │    OS 用分页管理物理内存 → vLLM 用分页管理 KV Cache              │
  │                                                                  │
  │  三大能力:                                                       │
  │  1. PagedAttention: KV Cache 分页管理 → 显存利用率 90%+          │
  │  2. Continuous Batching: 请求动态进出 → GPU 不空转               │
  │  3. OpenAI 兼容 API: 无缝替换 → 一行换后端                      │
  │                                                                  │
  │  适合: 需要高吞吐、高并发的 LLM 在线服务                         │
  │  不足: 对多轮对话的前缀复用不如 SGLang                           │
  └──────────────────────────────────────────────────────────────────┘
```

### 使用

```python
from vllm import LLM, SamplingParams

# 离线批量推理
llm = LLM(model="meta-llama/Llama-2-7b-hf")
outputs = llm.generate(
    ["Hello, my name is", "The future of AI is"],
    SamplingParams(temperature=0.8, max_tokens=100)
)
for output in outputs:
    print(output.outputs[0].text)
```

```bash
# 在线服务 (兼容 OpenAI API)
python -m vllm.entrypoints.openai.api_server \
    --model meta-llama/Llama-2-7b-hf \
    --port 8000

# 调用 (和 OpenAI 完全一样!)
curl http://localhost:8000/v1/completions \
    -H "Content-Type: application/json" \
    -d '{"model": "meta-llama/Llama-2-7b-hf", "prompt": "Hello"}'
```

## SGLang

### 设计哲学

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  SGLang 的核心贡献: RadixAttention (前缀树 KV Cache 复用)        │
  │                                                                  │
  │  发现: 实际场景中大量请求共享相同前缀                             │
  │    多轮对话: 所有回合共享 system prompt                           │
  │    Few-shot: 所有请求共享示例 (examples)                         │
  │    Agent: 多次调用共享系统指令                                    │
  │                                                                  │
  │  vLLM: 每个请求独立 KV Cache (即使前缀相同也重算!)               │
  │  SGLang: 用前缀树自动发现和复用共享前缀                          │
  │                                                                  │
  │  Radix Tree:                                                     │
  │              "You are a helpful assistant."                       │
  │                   [共享 KV Cache]                                 │
  │                  /                \                               │
  │         "What is AI?"      "Explain ML."                         │
  │        [增量 KV Cache]    [增量 KV Cache]                        │
  │                                                                  │
  │  效果:                                                           │
  │  • system prompt 只计算一次 (而不是每个请求都算)                 │
  │  • TTFT 显著降低 (共享前缀跳过 Prefill)                         │
  │  • 多轮对话场景吞吐量比 vLLM 高 2-5x                            │
  │                                                                  │
  │  另一大特色: 结构化生成                                           │
  │  • 原生支持 JSON Schema 约束输出                                 │
  │  • 正则表达式约束生成                                            │
  │  • Agent / Tool calling 场景首选                                 │
  └──────────────────────────────────────────────────────────────────┘
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
)
```

```python
# SGLang 原生前端 (利用 RadixAttention)
import sglang as sgl

@sgl.function
def multi_turn_qa(s, question1, question2):
    s += sgl.system("You are a helpful assistant.")  # 共享前缀!
    s += sgl.user(question1)
    s += sgl.assistant(sgl.gen("answer1", max_tokens=256))
    s += sgl.user(question2)
    s += sgl.assistant(sgl.gen("answer2", max_tokens=256))

# 批量执行，自动利用 RadixAttention 共享 system prompt
results = multi_turn_qa.run_batch([
    {"question1": "What is AI?", "question2": "Give examples."},
    {"question1": "What is AI?", "question2": "What are risks?"},
])
```

## Text Generation Inference (TGI)

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  TGI = Hugging Face 官方的推理服务                                │
  │                                                                  │
  │  设计哲学: "开箱即用"                                            │
  │    与 HuggingFace Hub 深度集成                                   │
  │    一行 Docker 命令启动                                          │
  │    自动加载模型配置和 tokenizer                                  │
  │                                                                  │
  │  核心技术:                                                       │
  │  • Continuous Batching                                           │
  │  • FlashAttention                                                │
  │  • 量化支持 (bitsandbytes, GPTQ, AWQ)                           │
  │  • Rust 实现的 HTTP Server (高性能)                              │
  │                                                                  │
  │  适合: 快速部署原型、HuggingFace 生态用户                        │
  │  不足: 性能不如 vLLM/SGLang 极致优化                              │
  └──────────────────────────────────────────────────────────────────┘
```

```bash
# Docker 一键部署
docker run --gpus all -p 8080:80 \
    -v ~/.cache/huggingface:/data \
    ghcr.io/huggingface/text-generation-inference:latest \
    --model-id meta-llama/Llama-2-7b-hf

curl localhost:8080/generate \
    -X POST \
    -d '{"inputs":"What is AI?","parameters":{"max_new_tokens":100}}' \
    -H 'Content-Type: application/json'
```

## Triton Inference Server

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  Triton = NVIDIA 企业级多模型推理平台                             │
  │                                                                  │
  │  设计哲学: "一个平台服务所有模型"                                 │
  │                                                                  │
  │  不只是 LLM! 支持:                                               │
  │  • LLM (通过 TensorRT-LLM backend)                              │
  │  • CV 模型 (TensorRT / ONNX Runtime)                             │
  │  • 推荐模型 (TensorFlow / PyTorch)                               │
  │  • 音频/视频模型                                                 │
  │                                                                  │
  │  核心能力:                                                       │
  │  • 多模型共存: 一个 GPU 上同时服务多个模型                       │
  │  • 模型编排 (Ensemble): A 模型输出接 B 模型输入                  │
  │  • 动态 batching                                                 │
  │  • 模型热更新: 不停服更换模型版本                                │
  │  • 多框架后端: TensorRT / PyTorch / ONNX / custom                │
  │                                                                  │
  │  适合: 企业级生产环境，多模型混合部署                             │
  │  不足: 配置复杂，LLM 单项性能不如专用框架                        │
  └──────────────────────────────────────────────────────────────────┘
```

## 如何选择

```
  ┌──────────────────────────────────────────────────────────────────────────────┐
  │                    框架选择决策树                                             │
  ├──────────────────────────────────────────────────────────────────────────────┤
  │                                                                              │
  │  你的场景是什么？                                                            │
  │      │                                                                       │
  │      ├─── 高并发在线 LLM 服务                                               │
  │      │        → vLLM (最成熟) 或 SGLang (前缀复用更强)                       │
  │      │                                                                       │
  │      ├─── 多轮对话 / Agent / 共享 system prompt 多                           │
  │      │        → SGLang (RadixAttention 前缀复用)                             │
  │      │                                                                       │
  │      ├─── 需要结构化 JSON 输出                                               │
  │      │        → SGLang (原生支持)                                            │
  │      │                                                                       │
  │      ├─── 快速原型 / HuggingFace 生态                                       │
  │      │        → TGI (一行 Docker)                                            │
  │      │                                                                       │
  │      ├─── 企业级多模型混合服务                                               │
  │      │        → Triton (多框架多模型)                                        │
  │      │                                                                       │
  │      └─── 要兼容 OpenAI API                                                 │
  │               → vLLM 或 SGLang (都兼容)                                     │
  │                                                                              │
  └──────────────────────────────────────────────────────────────────────────────┘
```

---

*下一篇：[09-deployment-architecture.md](09-deployment-architecture.md) - 部署架构模式*
