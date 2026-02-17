# 硬件选型指南

> 根据场景需求选择合适的 GPU 硬件。

## 目录

- [场景分析](#场景分析)
- [显存需求估算](#显存需求估算)
- [GPU 选型推荐](#gpu-选型推荐)
- [选型决策树](#选型决策树)

---

## 场景分析

### 按场景选择

| 场景 | 推荐 GPU | 理由 |
|------|----------|------|
| **LLM 推理（小规模）** | RTX 4090 / L40S | 性价比高，24GB/48GB 显存够用 |
| **LLM 推理（生产）** | A100 40GB / H100 | 高带宽，Tensor Core 优化 |
| **LLM 训练（中小模型）** | A100 80GB × 8 | 显存充足，NVLink 互联 |
| **LLM 训练（大模型）** | H100 80GB × 8+ | 最强性能，Transformer Engine |
| **研究/实验** | RTX 3090/4090 | 成本低，快速迭代 |
| **边缘推理** | Jetson Orin | 低功耗，嵌入式场景 |

---

## 显存需求估算

### 推理显存公式

```python
def estimate_inference_memory(params_billion, precision="fp16"):
    """推理显存 = 模型参数 + KV Cache"""
    bytes_per_param = {"fp32": 4, "fp16": 2, "int8": 1, "int4": 0.5}[precision]
    model_gb = params_billion * bytes_per_param
    kv_cache_gb = params_billion * 0.5  # 估算
    return model_gb + kv_cache_gb

# 示例
print(f"7B FP16 推理: ~{estimate_inference_memory(7):.0f} GB")
print(f"70B FP16 推理: ~{estimate_inference_memory(70):.0f} GB")
```

### 训练显存公式

```python
def estimate_training_memory(params_billion):
    """
    训练显存 = 模型 + 梯度 + 优化器 + 激活值
    FP16 + AdamW ≈ 参数量 × 16-20 bytes
    """
    return params_billion * 18  # GB

# 示例
print(f"7B 模型训练: ~{estimate_training_memory(7):.0f} GB")
print(f"70B 模型训练: ~{estimate_training_memory(70):.0f} GB")
```

### 模型规模与 GPU 需求

| 模型 | 推理显存 | 训练显存 | 推荐配置 |
|------|---------|---------|----------|
| 7B | ~14 GB | ~126 GB | 推理: 1×A100, 训练: 2×A100 80GB |
| 13B | ~26 GB | ~234 GB | 推理: 1×A100, 训练: 4×A100 80GB |
| 30B | ~60 GB | ~540 GB | 推理: 2×A100, 训练: 8×A100 80GB |
| 70B | ~140 GB | ~1.26 TB | 推理: 2×H100, 训练: 8×H100 + ZeRO |

---

## GPU 选型推荐

### 消费级 GPU

| GPU | 显存 | FP16 算力 | 价格 | 适用 |
|-----|------|----------|------|------|
| RTX 4060 | 8 GB | 15 TFLOPS | ~$300 | 小模型推理 |
| RTX 4070 | 12 GB | 29 TFLOPS | ~$550 | 中小模型推理 |
| RTX 4080 | 16 GB | 48 TFLOPS | ~$1000 | 中等模型 |
| RTX 4090 | 24 GB | 82 TFLOPS | ~$1600 | 7B 推理/训练 |

### 数据中心 GPU

| GPU | 显存 | FP16 算力 | 适用场景 |
|-----|------|----------|----------|
| A100 40GB | 40 GB | 312 TFLOPS | 主流推理 |
| A100 80GB | 80 GB | 312 TFLOPS | 大模型训练 |
| H100 SXM | 80 GB | 1,979 TFLOPS | 最强训练 |
| L40S | 48 GB | 733 TFLOPS | 推理优化 |
| B200 | 192 GB | 4,500 TFLOPS | 超大模型 |

---

## 选型决策树

```
┌─────────────────────────────────────────────────────────────┐
│                    GPU 选型决策树                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                    你的主要任务是什么？                        │
│                          │                                   │
│           ┌──────────────┼──────────────┐                   │
│           ▼              ▼              ▼                   │
│        训练           推理          研究/实验                 │
│           │              │              │                   │
│     模型多大？      延迟要求？      预算多少？                  │
│           │              │              │                   │
│   ┌───────┼───────┐  ┌──┼──┐      ┌────┼────┐             │
│   ▼       ▼       ▼  ▼     ▼      ▼         ▼             │
│ <7B    7-70B    >70B 宽松  严格   有限     充足              │
│   │       │       │   │     │      │         │             │
│   ▼       ▼       ▼   ▼     ▼      ▼         ▼             │
│ A100×1  A100×8  H100  L40S  H100  RTX4090  A100/H100       │
│ 80GB    80GB    ×8+                                        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 关键考量因素

1. **显存容量**：能否装下模型？
2. **计算性能**：满足延迟/吞吐要求？
3. **互联带宽**：多卡通信效率？
4. **预算**：总体拥有成本？
5. **功耗**：散热和电力供应？

---

## 实战练习

### 练习：查询 GPU 信息

```python
import torch

def gpu_info():
    if not torch.cuda.is_available():
        print("CUDA 不可用")
        return
    
    props = torch.cuda.get_device_properties(0)
    
    print(f"GPU: {props.name}")
    print(f"显存: {props.total_memory / 1024**3:.1f} GB")
    print(f"SM 数量: {props.multi_processor_count}")
    print(f"计算能力: {props.major}.{props.minor}")
    
    # 检查 Tensor Core
    if props.major >= 7:
        print("Tensor Core: 支持")
    
    # 当前使用
    print(f"已分配: {torch.cuda.memory_allocated() / 1024**2:.1f} MB")

gpu_info()
```

---

## 小结

- **按需选型**：根据模型规模和使用场景选择
- **显存优先**：显存是 LLM 的第一瓶颈
- **考虑扩展**：预留多卡扩展空间
- **成本平衡**：性能与预算的权衡

---

*返回：[README.md](README.md) - 章节索引*
