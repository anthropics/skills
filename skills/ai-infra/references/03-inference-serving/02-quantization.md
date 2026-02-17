# 量化技术详解

> 用更少的位数表示权重，加速推理并节省显存。

## 目录

- [量化基础](#量化基础)
- [量化类型](#量化类型)
- [主流量化方法](#主流量化方法)
- [实践指南](#实践指南)

---

## 量化基础

### 量化原理

```
原始 FP16:  每个权重 16 bits
量化 INT8:  每个权重 8 bits   → 模型大小减半
量化 INT4:  每个权重 4 bits   → 模型大小减到 1/4

量化公式:
q = round(x / scale) + zero_point
x_dequant = (q - zero_point) * scale
```

### 量化收益

| 量化精度 | 模型大小 | 速度提升 | 精度损失 |
|----------|----------|----------|----------|
| FP16 | 1x | 1x | 无 |
| INT8 | 0.5x | ~2x | 极小 |
| INT4 | 0.25x | ~1.5-2.5x | 小-中 |

---

## 量化类型

### PTQ vs QAT

| 类型 | 全称 | 特点 |
|------|------|------|
| **PTQ** | Post-Training Quantization | 训练后量化，简单快速 |
| **QAT** | Quantization-Aware Training | 训练时量化，精度更好 |

### 对称 vs 非对称

```
对称量化: zero_point = 0
q = round(x / scale)
适合: 权重分布对称

非对称量化: zero_point ≠ 0
q = round(x / scale) + zero_point
适合: 激活值 (常为非负)
```

---

## 主流量化方法

### GPTQ (Post-Training Weight Quantization)

```python
# GPTQ: 逐层量化，使用校准数据
from transformers import AutoModelForCausalLM, GPTQConfig

quantization_config = GPTQConfig(
    bits=4,
    dataset="c4",
    tokenizer=tokenizer,
)

model = AutoModelForCausalLM.from_pretrained(
    "meta-llama/Llama-2-7b-hf",
    quantization_config=quantization_config,
    device_map="auto",
)
```

### AWQ (Activation-aware)

```python
# AWQ: 基于激活值重要性的量化
from awq import AutoAWQForCausalLM

model = AutoAWQForCausalLM.from_pretrained(
    "meta-llama/Llama-2-7b-hf"
)
model.quantize(
    tokenizer,
    quant_config={"w_bit": 4, "q_group_size": 128}
)
```

### bitsandbytes

```python
# 最简单的量化方式
from transformers import BitsAndBytesConfig

bnb_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_quant_type="nf4",
    bnb_4bit_compute_dtype=torch.bfloat16,
    bnb_4bit_use_double_quant=True,
)

model = AutoModelForCausalLM.from_pretrained(
    "meta-llama/Llama-2-7b-hf",
    quantization_config=bnb_config,
)
```

---

## 实践指南

### 方法选择

| 场景 | 推荐方法 | 理由 |
|------|----------|------|
| 快速实验 | bitsandbytes | 一行代码 |
| 生产部署 | AWQ/GPTQ | 速度更快 |
| 最高精度 | QAT | 训练时优化 |
| vLLM 部署 | AWQ | 原生支持 |

### 量化效果评估

```python
def evaluate_quantization(model, tokenizer, dataset):
    """评估量化模型效果"""
    # 困惑度
    perplexity = compute_perplexity(model, tokenizer, dataset)
    
    # 推理速度
    latency = benchmark_inference(model, tokenizer)
    
    # 显存占用
    memory = torch.cuda.max_memory_allocated() / 1e9
    
    print(f"Perplexity: {perplexity:.2f}")
    print(f"Latency: {latency:.2f} ms/token")
    print(f"Memory: {memory:.1f} GB")
```

---

*下一篇：[03-pruning-distillation.md](03-pruning-distillation.md) - 剪枝与蒸馏*
