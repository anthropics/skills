# 模型并行详解

> 理解张量并行的切分原理和 Transformer 中的应用。

## 目录

- [张量并行原理](#张量并行原理)
- [列切分与行切分](#列切分与行切分)
- [Transformer 中的张量并行](#transformer-中的张量并行)
- [使用示例](#使用示例)

---

## 张量并行原理

### 核心思想

将每层的权重矩阵切分到多个 GPU，每个 GPU 只持有部分权重。

```
原始 Linear: Y = XW
W: [hidden, output]

切分后:
W = [W₀ | W₁ | W₂ | W₃]  (列切分)
或
W = [W₀; W₁; W₂; W₃]     (行切分)
```

---

## 列切分与行切分

### 列切分 (Column Parallel)

```
┌─────────────────────────────────────────────────────────────┐
│                     列切分示意                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   W: [hidden, output]  →  切分 output 维度                  │
│                                                             │
│      W                    W₀      W₁      W₂      W₃       │
│   ┌─────┐              ┌────┐  ┌────┐  ┌────┐  ┌────┐      │
│   │     │   切分为     │    │  │    │  │    │  │    │      │
│   │     │   ─────→    │    │  │    │  │    │  │    │      │
│   │     │              │    │  │    │  │    │  │    │      │
│   └─────┘              └────┘  └────┘  └────┘  └────┘      │
│                        GPU 0   GPU 1   GPU 2   GPU 3       │
│                                                             │
│   计算: Y_i = X @ W_i  (每 GPU 独立计算，无需通信)           │
│   结果: Y = [Y₀ | Y₁ | Y₂ | Y₃] (拼接)                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**特点**：前向无需通信，但输出是分片的。

### 行切分 (Row Parallel)

```
┌─────────────────────────────────────────────────────────────┐
│                     行切分示意                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   W: [input, hidden]  →  切分 input 维度                    │
│                                                             │
│      W                   W₀       W₁       W₂       W₃     │
│   ┌─────┐              ┌────┐   ┌────┐   ┌────┐   ┌────┐   │
│   │     │   切分为     │    │   │    │   │    │   │    │   │
│   │     │   ─────→    ├────┤   ├────┤   ├────┤   ├────┤   │
│   │     │              │    │   │    │   │    │   │    │   │
│   └─────┘              └────┘   └────┘   └────┘   └────┘   │
│                        GPU 0    GPU 1    GPU 2    GPU 3    │
│                                                             │
│   需要切分输入: X = [X₀ | X₁ | X₂ | X₃]                    │
│   计算: Y_i = X_i @ W_i                                    │
│   结果: Y = AllReduce(Y₀ + Y₁ + Y₂ + Y₃)                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**特点**：需要 AllReduce 合并结果。

---

## Transformer 中的张量并行

### MLP Block

```
┌─────────────────────────────────────────────────────────────┐
│              Transformer MLP 的张量并行                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   Input X                                                   │
│      │                                                      │
│      ▼                                                      │
│   Linear 1 (hidden → 4h)  ← Column Parallel (列切分)       │
│   无需通信，每 GPU 计算部分输出                              │
│      │                                                      │
│      ▼                                                      │
│   GeLU (每 GPU 独立计算)                                    │
│      │                                                      │
│      ▼                                                      │
│   Linear 2 (4h → hidden)  ← Row Parallel (行切分)          │
│   需要 AllReduce 合并结果                                   │
│      │                                                      │
│      ▼                                                      │
│   Output                                                    │
│                                                             │
│   通信次数: 每个 MLP block 1 次 AllReduce                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Self-Attention

```
Q, K, V Projection: Column Parallel (按 head 切分)
     ↓
Attention 计算: 每 GPU 计算部分 head
     ↓
Output Projection: Row Parallel + AllReduce
```

---

## 使用示例

### Megatron-LM 风格

```python
# 伪代码示意
class ColumnParallelLinear(nn.Module):
    def __init__(self, input_size, output_size, tp_size):
        super().__init__()
        self.weight = nn.Parameter(
            torch.empty(output_size // tp_size, input_size)
        )
    
    def forward(self, x):
        # 每 GPU 独立计算部分输出列
        return F.linear(x, self.weight)

class RowParallelLinear(nn.Module):
    def __init__(self, input_size, output_size, tp_size):
        super().__init__()
        self.weight = nn.Parameter(
            torch.empty(output_size, input_size // tp_size)
        )
    
    def forward(self, x):
        # 计算后 AllReduce
        out = F.linear(x, self.weight)
        dist.all_reduce(out)
        return out
```

### 配置参数

```python
# Megatron-LM
tensor_model_parallel_size = 8  # TP=8

# DeepSpeed
ds_config = {
    "tensor_parallel": {
        "tp_size": 8
    }
}
```

---

## 注意事项

1. **需要高带宽互联**：每层都有通信，建议 NVLink
2. **TP 通常 2-8**：过大会通信瓶颈
3. **节点内使用**：跨节点带宽不足

---

*下一篇：[05-pipeline-parallelism.md](05-pipeline-parallelism.md) - 流水线并行详解*

---

## 参考资料与引用

1. **Shoeybi, M., et al. (2020).** *Megatron-LM: Training Multi-Billion Parameter Language Models Using Model Parallelism.* — 张量并行原论文  
   https://arxiv.org/abs/1909.08053

2. **Narayanan, D., et al. (2021).** *Efficient Large-Scale Language Model Training on GPU Clusters.* — Megatron-LM 张量并行实践  
   https://arxiv.org/abs/2104.04473

3. **NVIDIA.** *Megatron-LM GitHub Repository.*  
   https://github.com/NVIDIA/Megatron-LM

4. **Dean, J., et al. (2012).** *Large Scale Distributed Deep Networks.* NeurIPS 2012. — 模型并行先驱工作  
   https://papers.nips.cc/paper/2012/hash/6aca97005c68f1206823815f66102863-Abstract.html
