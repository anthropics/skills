# 流水线并行详解

> 理解流水线并行的按层切分、调度策略和气泡优化。

## 目录

- [流水线并行原理](#流水线并行原理)
- [调度策略](#调度策略)
- [气泡问题与优化](#气泡问题与优化)
- [配置示例](#配置示例)

---

## 流水线并行原理

### 按层切分

```
模型 24 层，4 GPU

GPU 0: Layer 0-5   (Stage 0)
GPU 1: Layer 6-11  (Stage 1)
GPU 2: Layer 12-17 (Stage 2)
GPU 3: Layer 18-23 (Stage 3)

数据流: Stage 0 → Stage 1 → Stage 2 → Stage 3
        (前向)
        Stage 3 → Stage 2 → Stage 1 → Stage 0
        (反向)
```

### 与张量并行的区别

| 特性 | 张量并行 (TP) | 流水线并行 (PP) |
|------|--------------|----------------|
| 切分方式 | 层内切分 | 按层切分 |
| 通信 | 每层 AllReduce | 相邻 Stage 传输 |
| 带宽要求 | 高 (NVLink) | 中等 |
| 气泡 | 无 | 有 |

---

## 调度策略

### 朴素流水线

```
Time →
GPU 0: │ F0 │ F1 │ F2 │ F3 │    │    │    │    │ B3 │ B2 │ B1 │ B0 │
GPU 1: │    │ F0 │ F1 │ F2 │ F3 │    │    │ B3 │ B2 │ B1 │ B0 │    │
GPU 2: │    │    │ F0 │ F1 │ F2 │ F3 │ B3 │ B2 │ B1 │ B0 │    │    │
GPU 3: │    │    │    │ F0 │ F1 │ F2 │ F3 │ B3 │ B2 │ B1 │ B0 │    │
       └─────────────────────────────────────────────────────────────┘
                       ↑ 气泡（空闲） ↑

气泡率: (P-1) / P ≈ 75% (4 GPU)
```

### GPipe 调度

切分为多个 micro-batch：

```
Global batch → [micro-batch 0, 1, 2, 3, 4, 5, 6, 7]

Time →
GPU 0: │F0│F1│F2│F3│F4│F5│F6│F7│  │B7│B6│B5│B4│B3│B2│B1│B0│
GPU 1: │  │F0│F1│F2│F3│F4│F5│F6│F7│  │B7│B6│B5│B4│B3│B2│B1│B0│
GPU 2: │  │  │F0│F1│F2│F3│F4│F5│F6│F7│  │B7│B6│B5│B4│B3│B2│B1│B0│
GPU 3: │  │  │  │F0│F1│F2│F3│F4│F5│F6│F7│  │B7│B6│B5│B4│B3│B2│B1│B0│

气泡率降低: (P-1) / (P + M - 1)，M 为 micro-batch 数
```

### 1F1B 调度

前向和反向交替执行：

```
Time →
GPU 0: │F0│F1│F2│F3│B0│F4│B1│F5│B2│F6│B3│F7│B4│B5│B6│B7│
GPU 1: │  │F0│F1│F2│F3│B0│F4│B1│F5│B2│F6│B3│F7│B4│B5│B6│B7│
...

优势: 内存占用更少，前向完成立即反向
```

---

## 气泡问题与优化

### 气泡率计算

```
朴素: bubble_rate = (P - 1) / P
GPipe: bubble_rate = (P - 1) / (P + M - 1)
1F1B: bubble_rate ≈ (P - 1) / M

P = pipeline stages
M = micro-batches
```

### 优化建议

1. **增加 micro-batch 数量**：M 越大气泡越少
2. **平衡各 Stage 计算量**：均匀分配层数
3. **考虑通信开销**：PP 通信量小于 TP

---

## 配置示例

### DeepSpeed Pipeline

```python
ds_config = {
    "train_batch_size": 1024,
    "train_micro_batch_size_per_gpu": 4,
    "gradient_accumulation_steps": 64,  # micro-batches
    
    "pipeline": {
        "stages": 4,
        "partition_method": "uniform"  # 或 "parameters"
    }
}
```

### Megatron-LM

```bash
python pretrain_gpt.py \
    --pipeline-model-parallel-size 4 \
    --micro-batch-size 1 \
    --global-batch-size 512 \
    ...
```

---

## 小结

- **流水线并行**：按层切分模型到不同 Stage
- **气泡问题**：GPU 等待导致空闲
- **调度优化**：GPipe/1F1B 通过 micro-batch 减少气泡
- **适用场景**：层数多、跨节点通信

---

*下一篇：[06-3d-parallelism.md](06-3d-parallelism.md) - 3D 并行实践*
