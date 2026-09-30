# 激活重计算（Activation Checkpointing）

> 用计算换显存——大模型训练中最常用的显存优化技术之一。

## 目录

- [为什么需要激活重计算](#为什么需要激活重计算)
- [核心原理](#核心原理)
- [策略选择](#策略选择)
- [PyTorch 实现](#pytorch-实现)
- [与其他技术的组合](#与其他技术的组合)

---

## 为什么需要激活重计算

### 激活值的显存问题

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     训练中的显存占用分析 (LLaMA-7B)                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  模型参数 (FP16):        14 GB                                             │
│  梯度 (FP16):            14 GB                                             │
│  优化器状态 (AdamW):     84 GB   ← ZeRO 可以切分                           │
│  激活值:                 ?? GB   ← 随 batch size 和序列长度线性增长!         │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  激活值 = 前向传播中间结果，反向传播时需要                                   │
│                                                                             │
│  每层的激活值 ≈ 2 × batch × seq_len × hidden_dim × 层数                    │
│                                                                             │
│  例: batch=8, seq=2048, hidden=4096, 32层                                  │
│      ≈ 2 × 8 × 2048 × 4096 × 32 × 2 bytes ≈ 34 GB                       │
│                                                                             │
│  这比模型参数本身还大!                                                      │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 生活类比

```
类比: 做一道复杂菜需要很多中间步骤

  传统做法 (不用 Activation Checkpointing):
  ─────────────────────────────────────────
  切菜 → 放一旁 → 腌肉 → 放一旁 → 调汁 → 放一旁 → 炒菜 → 用上所有中间结果
  问题: 桌面 (显存) 很快就被各种碗碟 (激活值) 占满了!

  激活重计算:
  ─────────────────────────────────────────
  切菜 → 只记住"第一步是切菜" → 腌肉 → 只记住"第二步是腌肉" → ...
  到需要时 → 重新做一遍那个步骤
  好处: 桌面清爽了! 代价: 有些步骤要做两遍
```

---

## 核心原理

### 标准训练 vs 激活重计算

```
标准训练 (保存所有激活值):
═══════════════════════════════════════════════

前向传播:
Layer 1 → [保存 a₁] → Layer 2 → [保存 a₂] → ... → Layer N → [保存 aₙ] → Loss

反向传播:
Loss → 用 aₙ 算梯度 → 用 aₙ₋₁ 算梯度 → ... → 用 a₁ 算梯度

显存: O(N) — 保存所有 N 层的激活值


激活重计算 (只保存检查点):
═══════════════════════════════════════════════

前向传播:
Layer 1 → [保存 a₁✓] → Layer 2 → [丢弃] → Layer 3 → [保存 a₃✓] → Layer 4 → [丢弃] → ...

反向传播:
需要 a₄ → 从 a₃ 重新计算 Layer 4 的激活 → 用它算梯度
需要 a₂ → 从 a₁ 重新计算 Layer 2 的激活 → 用它算梯度

显存: O(√N) — 只保存 √N 个检查点
计算: 多了约 33% 的前向传播计算量
```

### 显存节省量化

| 策略 | 显存 | 额外计算 | 适用场景 |
|------|------|----------|----------|
| 无 Checkpointing | 100% | 0% | 显存充裕 |
| 每隔 1 层 Checkpoint | ~50% | ~33% | 常见选择 |
| 选择性 Checkpoint | 60-80% | 10-20% | 精细优化 |
| 全量 Checkpoint (每层) | ~30% | ~33% | 显存极紧张 |

---

## 策略选择

### 1. 全量重计算（Full Recomputation）

每个 Transformer 层的输入作为检查点，层内所有中间激活值丢弃后重新计算。

```python
# PyTorch 实现
from torch.utils.checkpoint import checkpoint

class TransformerBlock(nn.Module):
    def forward(self, x):
        # 注意力 + FFN 的中间激活值不保存
        x = x + self.attention(self.norm1(x))
        x = x + self.ffn(self.norm2(x))
        return x

class TransformerModel(nn.Module):
    def forward(self, x):
        for block in self.blocks:
            # 用 checkpoint 包裹每个 block
            x = checkpoint(block, x, use_reentrant=False)
        return x
```

### 2. 选择性重计算（Selective Recomputation）

只重计算计算量小但显存占用大的操作（如 Attention Score 矩阵），保留计算量大的操作（如矩阵乘法）。

```
┌─────────────────────────────────────────────────────────────────┐
│  选择性重计算的决策逻辑                                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  对每个操作，比较:                                               │
│    保存成本 = 激活值大小                                        │
│    重算成本 = 前向计算 FLOPs                                    │
│                                                                 │
│  Attention Score (Q×K^T):                                       │
│    保存成本: O(batch × heads × seq² ) — 很大!                   │
│    重算成本: O(batch × heads × seq × dim) — 较小                │
│    → 值得重算! ✓                                                │
│                                                                 │
│  FFN 输出 (大矩阵乘法):                                        │
│    保存成本: O(batch × seq × 4×hidden) — 中等                   │
│    重算成本: O(batch × seq × hidden × 4×hidden) — 很大          │
│    → 保留不重算 ✗                                               │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

Megatron-LM 的选择性重计算策略：
- **重计算**: Softmax(QK^T) 的结果、Dropout mask
- **保留**: Q/K/V 投影、FFN 线性层输出

### 3. 分段重计算

将 N 层分成 √N 个段，只保存每段的输入，段内重计算。

---

## PyTorch 实现

### 基础用法

```python
import torch
from torch.utils.checkpoint import checkpoint, checkpoint_sequential

# 方式 1: 包装单个函数
def forward(self, x):
    # use_reentrant=False 是推荐的新 API（PyTorch 2.x）
    x = checkpoint(self.block1, x, use_reentrant=False)
    x = checkpoint(self.block2, x, use_reentrant=False)
    return x

# 方式 2: 包装 Sequential 模块
def forward(self, x):
    # segments: 分成几段（段数 ≈ √层数 是最优的）
    x = checkpoint_sequential(self.layers, segments=4, input=x, use_reentrant=False)
    return x
```

### 与 FSDP 结合

```python
from torch.distributed.fsdp import FullyShardedDataParallel as FSDP
from torch.distributed.fsdp.wrap import transformer_auto_wrap_policy

# 1. 先对每个 Transformer 层启用 Activation Checkpointing
from torch.distributed.algorithms._checkpoint.checkpoint_wrapper import (
    checkpoint_wrapper,
    CheckpointImpl,
    apply_activation_checkpointing,
)

model = MyTransformer()

# 对所有 TransformerBlock 应用 activation checkpointing
apply_activation_checkpointing(
    model,
    checkpoint_impl=CheckpointImpl.NO_REENTRANT,
    check_fn=lambda module: isinstance(module, TransformerBlock),
)

# 2. 再包装 FSDP
model = FSDP(
    model,
    auto_wrap_policy=transformer_auto_wrap_policy,
    mixed_precision=MixedPrecision(param_dtype=torch.bfloat16),
)
```

### DeepSpeed 配置

```json
{
  "activation_checkpointing": {
    "partition_activations": true,
    "contiguous_memory_optimization": true,
    "cpu_checkpointing": false,
    "number_checkpoints": null,
    "synchronize_checkpoint_boundary": false,
    "profile": false
  }
}
```

---

## 与其他技术的组合

### 组合效果

```
┌─────────────────────────────────────────────────────────────────┐
│  7B 模型训练的显存优化组合 (单 A100 80GB)                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  基线 (DDP, 无优化):                                            │
│    参数 14 + 梯度 14 + 优化器 84 + 激活值 34 = 146 GB (OOM!)   │
│                                                                 │
│  + 混合精度 (BF16):                                             │
│    激活值减半 → 参数 14 + 梯度 14 + 优化器 84 + 激活 17 = 129 GB │
│                                                                 │
│  + Activation Checkpointing:                                    │
│    激活值降至 ~5 GB → 14 + 14 + 84 + 5 = 117 GB                │
│                                                                 │
│  + ZeRO Stage 2 (8卡):                                         │
│    优化器 + 梯度切分 → 14 + 14/8 + 84/8 + 5 = 31.25 GB  ✓     │
│                                                                 │
│  + ZeRO Stage 3 (8卡):                                         │
│    全部切分 → (14+14+84)/8 + 5 = 19 GB  ✓✓                     │
│                                                                 │
│  关键: Activation Checkpointing + ZeRO 是大模型训练的标配组合    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 实用建议

| 场景 | 推荐策略 |
|------|----------|
| 7B 模型，8×A100 | FSDP + 全量 Checkpoint + BF16 |
| 70B 模型，64×H100 | ZeRO-3 + 选择性 Checkpoint + BF16 |
| 超长序列 (>32K) | + 序列并行 + FlashAttention |
| 显存仍不够 | + ZeRO-Offload (CPU 卸载) |

### 注意事项

1. **`use_reentrant=False`**: PyTorch 2.x 推荐使用非可重入版本，支持更多场景且更安全
2. **与 FlashAttention 的关系**: FlashAttention 本身已经不保存 attention score 矩阵，相当于内置了选择性重计算
3. **性能影响**: 全量重计算增加约 33% 的训练时间，选择性重计算约 10-15%
4. **调试**: Activation Checkpointing 可能影响梯度 NaN 的排查，建议问题排查时先关闭

---

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **Chen, T., et al. (2016).** *Training Deep Nets with Sublinear Memory Cost.* — Gradient/Activation Checkpointing 原论文  
   https://arxiv.org/abs/1604.06174

2. **Korthikanti, V., et al. (2022).** *Reducing Activation Recomputation in Large Transformer Models.* — Selective Checkpointing  
   https://arxiv.org/abs/2205.05198

3. **PyTorch Documentation.** *torch.utils.checkpoint.*  
   https://pytorch.org/docs/stable/checkpoint.html

4. **DeepSpeed Documentation.** *Activation Checkpointing.*  
   https://www.deepspeed.ai/tutorials/activation-checkpointing/
