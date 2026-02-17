# 训练框架对比

> 选择适合你的分布式训练框架。

## 目录

- [主流框架概览](#主流框架概览)
- [框架对比](#框架对比)
- [选择建议](#选择建议)
- [快速上手](#快速上手)

---

## 主流框架概览

| 框架 | 开发者 | 特点 |
|------|--------|------|
| PyTorch DDP/FSDP | Meta | 原生支持，易用 |
| DeepSpeed | Microsoft | ZeRO 优化，功能丰富 |
| Megatron-LM | NVIDIA | 超大模型，3D 并行 |
| ColossalAI | HPC-AI Tech | 封装好，易上手 |

---

## 框架对比

### 功能对比

| 特性 | DDP/FSDP | DeepSpeed | Megatron-LM | ColossalAI |
|------|----------|-----------|-------------|------------|
| 数据并行 | ✅ | ✅ ZeRO | ✅ | ✅ |
| 张量并行 | ❌ | ✅ 有限 | ✅ 最成熟 | ✅ |
| 流水线并行 | ❌ | ✅ | ✅ | ✅ |
| 序列并行 | ❌ | ✅ Ulysses | ✅ | ✅ |
| CPU Offload | ✅ | ✅ Infinity | ❌ | ✅ |
| 混合精度 | ✅ | ✅ | ✅ | ✅ |

### 易用性对比

| 框架 | 学习曲线 | 文档质量 | 社区支持 |
|------|----------|----------|----------|
| PyTorch DDP/FSDP | 低 | 优秀 | 最活跃 |
| DeepSpeed | 中 | 良好 | 活跃 |
| Megatron-LM | 高 | 一般 | 中等 |
| ColossalAI | 中低 | 良好 | 活跃 |

---

## 选择建议

### 决策树

```
                     模型规模？
                        │
         ┌──────────────┼──────────────┐
         │              │              │
         ▼              ▼              ▼
      < 10B         10B-100B        > 100B
         │              │              │
         ▼              ▼              ▼
   PyTorch FSDP    DeepSpeed      Megatron-LM
   或 DDP          ZeRO-3         + DeepSpeed
```

### 场景推荐

| 场景 | 推荐框架 | 理由 |
|------|----------|------|
| 快速实验 | PyTorch DDP | 简单直接 |
| 7B 模型微调 | FSDP | 原生支持 |
| 30B+ 训练 | DeepSpeed | ZeRO 显存优化 |
| 100B+ 训练 | Megatron-LM | 3D 并行最成熟 |
| 入门大模型 | ColossalAI | 封装友好 |

---

## 快速上手

### PyTorch DDP

```python
# 最简单的多卡训练
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP

dist.init_process_group("nccl")
model = DDP(model.cuda(), device_ids=[local_rank])

# 启动: torchrun --nproc_per_node=4 train.py
```

### DeepSpeed

```python
import deepspeed

model, optimizer, _, _ = deepspeed.initialize(
    model=model,
    config="ds_config.json"
)

# 启动: deepspeed --num_gpus=8 train.py
```

### FSDP

```python
from torch.distributed.fsdp import FullyShardedDataParallel as FSDP

model = FSDP(model)

# 启动: torchrun --nproc_per_node=4 train.py
```

---

## 小结

- **小模型 (< 10B)**：PyTorch DDP/FSDP 足够
- **中等模型 (10-100B)**：DeepSpeed ZeRO-3
- **超大模型 (> 100B)**：Megatron-LM + DeepSpeed

---

*下一篇：[08-communication-optimization.md](08-communication-optimization.md) - 通信优化*
