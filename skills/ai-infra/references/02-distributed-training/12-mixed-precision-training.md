# 混合精度训练详解

> 用更少的显存和更快的速度训练同样质量的模型。

## 目录

- [数值精度基础](#数值精度基础)
- [混合精度训练原理](#混合精度训练原理)
- [Loss Scaling](#loss-scaling)
- [BF16 vs FP16](#bf16-vs-fp16)
- [FP8 训练](#fp8-训练)
- [实践指南](#实践指南)

---

## 数值精度基础

### 浮点数格式

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      浮点数格式对比                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   FP32 (单精度): [1 sign][8 exponent][23 mantissa] = 32 bits               │
│   范围: ±3.4×10^38, 精度: ~7 位有效数字                                    │
│                                                                             │
│   FP16 (半精度): [1 sign][5 exponent][10 mantissa] = 16 bits               │
│   范围: ±65504, 精度: ~3.3 位有效数字                                      │
│                                                                             │
│   BF16 (Brain Float): [1 sign][8 exponent][7 mantissa] = 16 bits           │
│   范围: ±3.4×10^38 (与 FP32 相同!), 精度: ~2.4 位有效数字                  │
│                                                                             │
│   FP8 E4M3: [1 sign][4 exponent][3 mantissa] = 8 bits                     │
│   范围: ±448, 精度: ~1.8 位有效数字                                        │
│   用途: 前向传播（权重和激活值）                                            │
│                                                                             │
│   FP8 E5M2: [1 sign][5 exponent][2 mantissa] = 8 bits                     │
│   范围: ±57344, 精度: ~1.5 位有效数字                                      │
│   用途: 反向传播（梯度，需要更大动态范围）                                  │
│                                                                             │
│   显存占用对比 (7B 参数):                                                   │
│   ┌──────────────────────────────────────────────────────────────┐          │
│   │ FP32: 7B × 4 bytes = 28 GB                                  │          │
│   │ FP16: 7B × 2 bytes = 14 GB      (节省 50%)                  │          │
│   │ FP8:  7B × 1 byte  = 7 GB       (节省 75%)                  │          │
│   └──────────────────────────────────────────────────────────────┘          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 混合精度训练原理

### 核心思想

混合精度训练不是所有计算都用低精度，而是**在不同阶段使用不同精度**：

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     混合精度训练流程                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌────────────────────────────────────────────────────────────────┐       │
│   │              Master Weights (FP32)                              │       │
│   │              存储在优化器中，用于参数更新                        │       │
│   └───────┬────────────────────────────────────────────────────────┘       │
│           │ 每步开始: FP32 → FP16/BF16 拷贝                                │
│           ▼                                                                 │
│   ┌────────────────────────────────────────────────────────────────┐       │
│   │              FP16/BF16 Weights (工作副本)                       │       │
│   └───────┬────────────────────────────────────────────────────────┘       │
│           │                                                                 │
│           ▼  前向传播 (FP16/BF16)                                          │
│   ┌────────────────────────────────────────────────────────────────┐       │
│   │   Input → Linear(FP16) → Activation → ... → Loss              │       │
│   │   Tensor Core 加速: 2-8x 吞吐提升                              │       │
│   └───────┬────────────────────────────────────────────────────────┘       │
│           │                                                                 │
│           ▼  Loss Scaling (放大 loss)                                       │
│   ┌────────────────────────────────────────────────────────────────┐       │
│   │   scaled_loss = loss × scale_factor (如 1024)                  │       │
│   └───────┬────────────────────────────────────────────────────────┘       │
│           │                                                                 │
│           ▼  反向传播 (FP16/BF16)                                          │
│   ┌────────────────────────────────────────────────────────────────┐       │
│   │   FP16 梯度 (被放大了 scale_factor 倍)                         │       │
│   └───────┬────────────────────────────────────────────────────────┘       │
│           │ Unscale: gradients / scale_factor                               │
│           │ 检查 Inf/NaN: 如有则跳过本步更新                               │
│           ▼                                                                 │
│   ┌────────────────────────────────────────────────────────────────┐       │
│   │   优化器更新 (FP32):  FP32_weights -= lr × FP32_gradients     │       │
│   │   在 FP32 精度下累加，避免精度损失                              │       │
│   └────────────────────────────────────────────────────────────────┘       │
│                                                                             │
│   显存占用: FP32 master weights + FP16 工作副本 + FP16 梯度                │
│   = 4Ψ + 2Ψ + 2Ψ = 8Ψ (+ 优化器状态 8Ψ, 共 16Ψ)                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 为什么需要 FP32 Master Weights？

```python
# 问题演示: FP16 精度下的参数更新问题
import torch

# FP16 的最小可表示增量 (约 2^-10 ≈ 0.001)
weight_fp16 = torch.tensor(1.0, dtype=torch.float16)
update = torch.tensor(0.0001, dtype=torch.float16)

# 这个更新会被完全忽略!
result = weight_fp16 + update
print(f"FP16: {weight_fp16} + {update} = {result}")  # 1.0 + 0.0 = 1.0

# FP32 可以正确累积小更新
weight_fp32 = torch.tensor(1.0, dtype=torch.float32)
update_fp32 = torch.tensor(0.0001, dtype=torch.float32)
result = weight_fp32 + update_fp32
print(f"FP32: {weight_fp32} + {update_fp32} = {result}")  # 1.0 + 0.0001 = 1.0001
```

---

## Loss Scaling

### 为什么需要 Loss Scaling

FP16 的最小正规范数约为 6.1×10⁻⁵，很多梯度值会**下溢到零**：

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    FP16 梯度分布与下溢问题                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   典型梯度分布 (对数刻度):                                                  │
│                                                                             │
│   Count                                                                     │
│   │    ████                                                                 │
│   │   ██████                                                                │
│   │  ████████                                                               │
│   │ ██████████                                                              │
│   │████████████                                                             │
│   │██████████████                                                           │
│   └──────────────────────────────────────────────────── Magnitude           │
│   10^-8  10^-6  10^-4  10^-2  10^0                                         │
│     ▲                    ▲                                                  │
│     │                    │                                                  │
│   这些梯度在 FP16       FP16 最小                                           │
│   中变成 0 (下溢)       正规范数                                            │
│                                                                             │
│   Loss Scaling 效果:                                                        │
│   将整个分布右移 → 小梯度不再下溢                                           │
│   之后 unscale 还原真实值                                                   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Dynamic Loss Scaling

```python
# PyTorch AMP 的动态 Loss Scaling
scaler = torch.cuda.amp.GradScaler(
    init_scale=2**16,       # 初始 scale = 65536
    growth_factor=2.0,       # 连续成功后 scale 翻倍
    backoff_factor=0.5,      # 出现 Inf/NaN 后 scale 减半
    growth_interval=2000,    # 每 2000 步尝试增大 scale
)

for data, target in dataloader:
    optimizer.zero_grad()
    
    # 前向传播使用混合精度
    with torch.cuda.amp.autocast(dtype=torch.float16):
        output = model(data)
        loss = criterion(output, target)
    
    # 反向传播使用 scaled loss
    scaler.scale(loss).backward()
    
    # Unscale 梯度 + 检查 Inf/NaN + 优化器更新
    scaler.unscale_(optimizer)
    torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
    scaler.step(optimizer)  # 如果有 Inf/NaN 则跳过更新
    scaler.update()         # 动态调整 scale factor
```

---

## BF16 vs FP16

### 关键区别

| 特性 | FP16 | BF16 |
|------|------|------|
| **指数位** | 5 | 8 |
| **尾数位** | 10 | 7 |
| **动态范围** | ±65504 | ±3.4×10³⁸ |
| **精度** | ~3.3 位有效数字 | ~2.4 位有效数字 |
| **需要 Loss Scaling** | **是** | **通常不需要** |
| **硬件要求** | Volta+ | Ampere+ (A100/H100) |
| **溢出/下溢风险** | 高 | 低（范围与 FP32 相同） |

### 推荐选择

```
你的 GPU 是什么?
├── Volta (V100) → 只能用 FP16 + Loss Scaling
├── Ampere (A100) → 推荐 BF16 (更稳定, 无需 Loss Scaling)
├── Hopper (H100) → BF16 或 FP8 (Transformer Engine)
└── Ada (RTX 4090) → BF16 推荐
```

### BF16 训练示例

```python
# BF16 混合精度 - 更简洁，通常不需要 GradScaler
with torch.cuda.amp.autocast(dtype=torch.bfloat16):
    output = model(data)
    loss = criterion(output, target)

loss.backward()
optimizer.step()  # 直接更新，无需 scaler

# DeepSpeed 配置
ds_config = {
    "bf16": {
        "enabled": True,
    },
    # 不需要 fp16 + loss scaling 配置
}
```

---

## FP8 训练

### NVIDIA Transformer Engine

Hopper (H100) 架构引入了 FP8 Tensor Core，配合 NVIDIA Transformer Engine 实现 FP8 训练。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                   FP8 训练 (Transformer Engine)                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   前向传播:                                                                 │
│   权重: FP8 E4M3  (更高精度, 范围 ±448)                                   │
│   激活: FP8 E4M3                                                           │
│   Tensor Core: FP8 × FP8 → FP16/FP32 累加                                │
│                                                                             │
│   反向传播:                                                                 │
│   梯度: FP8 E5M2  (更大动态范围, 范围 ±57344)                             │
│   权重梯度: FP8 E5M2                                                       │
│                                                                             │
│   关键技术: Per-Tensor Scaling (延迟缩放)                                   │
│   ┌─────────────────────────────────────────────────────────────────┐      │
│   │  每个张量维护一个缩放因子 (scale factor)                         │      │
│   │  根据前一步的张量统计信息动态调整                                 │      │
│   │  amax_history → 计算合适的 scale → 量化到 FP8                   │      │
│   └─────────────────────────────────────────────────────────────────┘      │
│                                                                             │
│   性能提升 (H100 vs BF16):                                                 │
│   • GEMM 吞吐: ~2× (3958 vs 1979 TFLOPS, 稀疏)                           │
│   • 显存节省: ~50% (权重 + 激活值)                                         │
│   • 端到端训练: ~30% 加速 (受限于非 GEMM 部分)                             │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Transformer Engine 使用

```python
import transformer_engine.pytorch as te

# 替换标准层为 TE 层
class TransformerBlock(nn.Module):
    def __init__(self, d_model, nhead, d_ffn):
        super().__init__()
        # 使用 Transformer Engine 的 FP8 层
        self.attention = te.MultiheadAttention(
            d_model, nhead,
            fuse_qkv_params=True,
        )
        self.layernorm1 = te.LayerNorm(d_model)
        self.ffn = te.LayerNormMLP(
            d_model, d_ffn,
            activation='gelu',
        )
    
    def forward(self, x):
        # TE 自动处理 FP8 量化/反量化
        x = x + self.attention(self.layernorm1(x))
        x = x + self.ffn(x)
        return x

# 训练循环中启用 FP8
with te.fp8_autocast(enabled=True):
    output = model(input_data)
    loss = criterion(output, target)
loss.backward()
optimizer.step()
```

### Megatron-LM + FP8 配置

```bash
torchrun --nproc_per_node 8 pretrain_gpt.py \
    --fp8-format hybrid \            # E4M3 前向 + E5M2 反向
    --fp8-amax-history-len 1024 \    # amax 历史窗口
    --fp8-amax-compute-algo max \    # 使用 max 计算缩放因子
    --transformer-impl transformer_engine \
    --bf16                           # 非 GEMM 部分使用 BF16
```

---

## 实践指南

### 常见问题排查

| 症状 | 可能原因 | 解决方案 |
|------|----------|----------|
| Loss 变 NaN | FP16 溢出 | 改用 BF16 或增大 loss scaling |
| Loss 不收敛 | 梯度下溢 | 增大 loss scale 初始值 |
| 训练变慢 | GradScaler 频繁跳步 | 减小学习率或检查模型 |
| FP8 精度下降 | scale factor 不稳定 | 增大 amax_history_len |

### 精度选择决策树

```
需要从头训练大模型?
├── 是 → 有 H100?
│   ├── 是 → BF16 + FP8 Transformer Engine (最优)
│   └── 否 → 有 A100?
│       ├── 是 → BF16 (推荐)
│       └── 否 → FP16 + Dynamic Loss Scaling
└── 否 → 微调/推理?
    ├── 微调 → QLoRA (4-bit 量化 + FP16 适配器)
    └── 推理 → INT8/INT4 量化 (GPTQ/AWQ)
```

### PyTorch 最佳实践

```python
import torch
from torch.cuda.amp import autocast, GradScaler

# 方案 1: FP16 + GradScaler (V100 等)
scaler = GradScaler()
for batch in dataloader:
    with autocast(dtype=torch.float16):
        loss = model(batch)
    scaler.scale(loss).backward()
    scaler.step(optimizer)
    scaler.update()

# 方案 2: BF16 无 Scaler (A100+, 推荐)
for batch in dataloader:
    with autocast(dtype=torch.bfloat16):
        loss = model(batch)
    loss.backward()
    optimizer.step()

# 方案 3: FSDP + BF16
from torch.distributed.fsdp import FullyShardedDataParallel as FSDP, MixedPrecision

mp_policy = MixedPrecision(
    param_dtype=torch.bfloat16,    # 参数精度
    reduce_dtype=torch.bfloat16,   # 通信精度
    buffer_dtype=torch.bfloat16,   # buffer 精度
)

model = FSDP(model, mixed_precision=mp_policy)
```

---

## 📚 延伸阅读

- [Mixed Precision Training (Micikevicius et al., 2018)](https://arxiv.org/abs/1710.03740) - 原始论文
- [FP8 Formats for Deep Learning (NVIDIA, 2022)](https://arxiv.org/abs/2209.05433) - FP8 标准
- [NVIDIA Transformer Engine Documentation](https://docs.nvidia.com/deeplearning/transformer-engine/)
- [PyTorch AMP Documentation](https://pytorch.org/docs/stable/amp.html)

---

*返回目录：[README](README.md)*
