# 为什么需要分布式训练

> 理解大模型训练面临的三大瓶颈及其解决方案。

## 目录

- [单卡训练的瓶颈](#单卡训练的瓶颈)
- [显存瓶颈分析](#显存瓶颈分析)
- [计算瓶颈分析](#计算瓶颈分析)
- [解决方案概述](#解决方案概述)

---

## 单卡训练的瓶颈

### 三大瓶颈

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    大模型训练的三大瓶颈                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. 显存瓶颈 (Memory)                                                   │
│     ├── 模型参数: 7B FP16 = 14GB                                        │
│     ├── 梯度: 14GB                                                      │
│     ├── 优化器状态 (AdamW): 84GB (FP32副本+momentum+variance)     │
│     ├── 激活值: 取决于 batch size                                       │
│     └── 总计: 7B 模型训练需要 ~112GB+                                  │
│         (单卡 A100 80GB 装不下！)                                       │
│                                                                         │
│  2. 计算瓶颈 (Compute)                                                  │
│     ├── GPT-3 175B 训练: ~3.14×10²³ FLOPs                              │
│     ├── 单 A100 (312 TFLOPS FP16): 需要 1,000+ 年                       │
│     └── 1024 GPU 并行: ~1个月                                           │
│                                                                         │
│  3. 数据瓶颈 (Data)                                                     │
│     ├── 大规模数据集读取                                                 │
│     └── 预处理速度跟不上 GPU 消费                                        │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 显存瓶颈分析

### 训练显存组成

```python
def analyze_training_memory(params_billion: float):
    """
    分析训练显存组成 (FP16 + AdamW)
    """
    params = params_billion * 1e9
    
    # 模型参数 (FP16): 2 bytes
    model_gb = params * 2 / 1e9
    
    # 梯度 (FP16): 2 bytes
    gradient_gb = params * 2 / 1e9
    
    # 优化器状态 (AdamW):
    # - FP32 主权重副本: 4 bytes
    # - FP32 momentum: 4 bytes
    # - FP32 variance: 4 bytes
    optimizer_gb = params * 12 / 1e9
    
    total = model_gb + gradient_gb + optimizer_gb
    
    print(f"模型参数: {model_gb:.1f} GB")
    print(f"梯度:     {gradient_gb:.1f} GB")
    print(f"优化器:   {optimizer_gb:.1f} GB")
    print(f"总计:     {total:.1f} GB (不含激活值)")
    
    return total

# 分析不同规模模型
for size in [7, 13, 70, 175]:
    print(f"\n=== {size}B 模型 ===")
    analyze_training_memory(size)
```

输出示例：
```
=== 7B 模型 ===
模型参数: 14.0 GB
梯度:     14.0 GB
优化器:   84.0 GB
总计:     112.0 GB (不含激活值)

=== 70B 模型 ===
模型参数: 140.0 GB
梯度:     140.0 GB
优化器:   840.0 GB
总计:     1120.0 GB (不含激活值)
```

### 激活值显存

激活值是训练中容易被忽视的显存大户：

```python
def estimate_activation_memory(
    params_billion: float,
    seq_length: int = 2048,
    batch_size: int = 1
):
    """估算激活值显存"""
    # 假设隐藏维度和层数
    hidden_dim = int(params_billion * 512)
    num_layers = min(96, int(params_billion * 4))
    
    # 每层激活值 (简化估算)
    # 包括: attention 输出、MLP 中间层、残差连接等
    activation_per_layer = batch_size * seq_length * hidden_dim * 4 * 2  # bytes
    total_activation = activation_per_layer * num_layers
    
    return total_activation / 1e9  # GB

print(f"7B 模型激活值 (bs=1, seq=2048): {estimate_activation_memory(7):.1f} GB")
```

---

## 计算瓶颈分析

### 训练时间估算

```python
def estimate_training_time(
    params_billion: float,
    tokens_trillion: float,
    gpu_tflops: float,
    num_gpus: int,
    utilization: float = 0.5
):
    """
    估算训练时间
    
    FLOPs per token ≈ 6 × params (前向2倍 + 反向4倍)
    """
    total_flops = 6 * params_billion * 1e9 * tokens_trillion * 1e12
    
    effective_tflops = gpu_tflops * num_gpus * utilization
    
    seconds = total_flops / (effective_tflops * 1e12)
    days = seconds / 86400
    
    print(f"总 FLOPs: {total_flops:.2e}")
    print(f"有效算力: {effective_tflops:.1f} TFLOPS")
    print(f"预计时间: {days:.1f} 天")
    
    return days

# GPT-3 175B 训练估算
print("=== GPT-3 175B (300B tokens, 1024 A100) ===")
estimate_training_time(
    params_billion=175,
    tokens_trillion=0.3,
    gpu_tflops=312,
    num_gpus=1024
)
```

---

## 解决方案概述

### 分布式训练策略

```
                    ┌─────────────────────┐
                    │   分布式训练策略     │
                    └──────────┬──────────┘
                               │
         ┌─────────────────────┼─────────────────────┐
         │                     │                     │
         ▼                     ▼                     ▼
    ┌─────────┐          ┌─────────┐          ┌─────────┐
    │数据并行  │          │模型并行  │          │流水线并行│
    │  (DP)   │          │  (MP)   │          │  (PP)   │
    └────┬────┘          └────┬────┘          └────┬────┘
         │                     │                     │
         ▼                     ▼                     ▼
    复制模型              切分模型               切分层
    切分数据              每卡存部分             按阶段执行
```

### 策略选择建议

| 瓶颈类型 | 解决方案 | 说明 |
|----------|----------|------|
| 计算慢 | 数据并行 | 多卡处理更多数据 |
| 显存不足 (优化器) | ZeRO Stage 1/2 | 切分优化器状态/梯度 |
| 显存不足 (模型) | ZeRO Stage 3 / 模型并行 | 切分模型参数 |
| 单层过大 | 张量并行 | 切分每层的矩阵运算 |
| 层数过多 | 流水线并行 | 按层分配到不同设备 |

---

## 小结

- **显存瓶颈**：模型+梯度+优化器占用大量显存，7B 模型需要 112GB+
- **计算瓶颈**：大模型训练需要数千 GPU 并行数周
- **解决思路**：分而治之，将数据、模型、计算分散到多个设备

---

*下一篇：[02-parallelism-overview.md](02-parallelism-overview.md) - 并行策略总览*
