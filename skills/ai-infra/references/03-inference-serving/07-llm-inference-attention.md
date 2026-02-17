# LLM 推理特性 - Attention 优化

> FlashAttention 和 Speculative Decoding。

## FlashAttention

### 原理

```
标准 Attention: O(N²) 显存
- 需要存储完整 NxN 的 attention matrix

FlashAttention: O(N) 显存
- 分块计算，不存储完整 attention matrix
- 利用 GPU SRAM (shared memory)
- IO 感知算法
```

### 效果

| 方面 | 改进 |
|------|------|
| 显存 | 减少 10-20x |
| 速度 | 提升 2-4x |
| 精度 | 完全一致 |

### 使用

```python
# PyTorch 2.0+ 内置
import torch.nn.functional as F

# 自动使用 FlashAttention
output = F.scaled_dot_product_attention(query, key, value)
```

## Speculative Decoding

### 原理

```
思想: 用小模型预测多个 token，大模型验证

Draft Model (小): 快速生成 k 个候选 token
Target Model (大): 一次验证 k 个 token

流程:
1. Draft 生成: [t1, t2, t3, t4, t5] (5个候选)
2. Target 验证: 接受 [t1, t2, t3], 拒绝 [t4, t5]
3. 输出 [t1, t2, t3], 从 t4 重新生成

加速比: 取决于接受率，通常 2-3x
```

### 示例配置

```python
# vLLM Speculative Decoding
llm = LLM(
    model="meta-llama/Llama-2-70b-hf",  # Target
    speculative_model="meta-llama/Llama-2-7b-hf",  # Draft
    num_speculative_tokens=5,
)
```

## 其他优化

### Multi-Query Attention (MQA)

```
标准 MHA: 每个 head 有独立的 K, V
MQA: 所有 head 共享 K, V

KV Cache 减少: N_heads 倍
代表模型: Falcon, PaLM
```

### Grouped-Query Attention (GQA)

```
MHA 和 MQA 的折中
N_heads 分成几组，组内共享 K, V

代表模型: LLaMA-2 (70B 使用 8 组)
```

---

*下一篇：[08-serving-frameworks.md](08-serving-frameworks.md) - 服务框架详解*
