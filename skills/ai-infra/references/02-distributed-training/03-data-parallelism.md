# 数据并行详解

> 掌握 DDP、ZeRO、FSDP 的原理和使用。

## 目录

- [数据并行原理](#数据并行原理)
- [PyTorch DDP](#pytorch-ddp)
- [ZeRO 优化器](#zero-优化器)
- [PyTorch FSDP](#pytorch-fsdp)

---

## 数据并行原理

### 工作流程

```
1. 每个 GPU 复制完整模型
2. 数据按 batch 切分到各 GPU
3. 各 GPU 独立前向+反向计算
4. AllReduce 同步梯度 (求平均)
5. 各 GPU 用相同梯度更新参数
```

### 通信模式

```
GPU 0: grad_0
GPU 1: grad_1    →  AllReduce  →  avg_grad (所有 GPU)
GPU 2: grad_2
GPU 3: grad_3
```

---

## PyTorch DDP

### 基本使用

```python
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP

def setup(rank, world_size):
    dist.init_process_group("nccl", rank=rank, world_size=world_size)
    torch.cuda.set_device(rank)

def train(rank, world_size):
    setup(rank, world_size)
    
    # 模型包装为 DDP
    model = MyModel().to(rank)
    model = DDP(model, device_ids=[rank])
    
    # 使用 DistributedSampler
    sampler = torch.utils.data.distributed.DistributedSampler(
        dataset, num_replicas=world_size, rank=rank
    )
    dataloader = DataLoader(dataset, sampler=sampler, batch_size=32)
    
    optimizer = torch.optim.AdamW(model.parameters())
    
    for epoch in range(epochs):
        sampler.set_epoch(epoch)  # 确保每 epoch 数据不同
        for batch in dataloader:
            loss = model(batch).loss
            loss.backward()  # DDP 自动同步梯度
            optimizer.step()
            optimizer.zero_grad()
    
    dist.destroy_process_group()

# 启动: torchrun --nproc_per_node=4 train.py
```

### DDP 关键参数

```python
model = DDP(
    model,
    device_ids=[rank],
    output_device=rank,
    find_unused_parameters=False,  # 有未使用参数时设为 True
    bucket_cap_mb=25,              # 梯度聚合桶大小
)
```

---

## ZeRO 优化器

### 三阶段原理

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          ZeRO 三阶段                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   假设 N 个 GPU，模型参数量 Ψ (bytes/param 如下)                        │
│   FP16 参数: 2Ψ, 梯度: 2Ψ, 优化器(Adam): 12Ψ (FP32副本4Ψ+m4Ψ+v4Ψ)   │
│                                                                         │
│   标准 DDP: 每 GPU 存储 2Ψ + 2Ψ + 12Ψ = 16Ψ bytes                     │
│                                                                         │
│   ZeRO Stage 1: 切分优化器状态                                           │
│   每 GPU: 2Ψ + 2Ψ + 12Ψ/N = (4 + 12/N)Ψ bytes                        │
│                                                                         │
│   ZeRO Stage 2: + 切分梯度                                              │
│   每 GPU: 2Ψ + 2Ψ/N + 12Ψ/N = (2 + 14/N)Ψ bytes                      │
│                                                                         │
│   ZeRO Stage 3: + 切分模型参数                                          │
│   每 GPU: 2Ψ/N + 2Ψ/N + 12Ψ/N = 16Ψ/N bytes                          │
│                                                                         │
│   显存节省: Stage 3 相比 DDP 节省 N 倍！(N=64 时节省 64 倍)             │
│   代价: 前向/反向需要 AllGather 收集参数                                  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### DeepSpeed ZeRO 配置

```json
{
    "zero_optimization": {
        "stage": 3,
        "offload_optimizer": {
            "device": "cpu",
            "pin_memory": true
        },
        "offload_param": {
            "device": "cpu",
            "pin_memory": true
        },
        "overlap_comm": true,
        "contiguous_gradients": true,
        "reduce_bucket_size": 5e8,
        "stage3_prefetch_bucket_size": 5e8,
        "stage3_param_persistence_threshold": 1e6
    }
}
```

### DeepSpeed 使用示例

```python
import deepspeed

model = MyModel()

model_engine, optimizer, _, _ = deepspeed.initialize(
    model=model,
    model_parameters=model.parameters(),
    config="ds_config.json"
)

for batch in dataloader:
    loss = model_engine(batch).loss
    model_engine.backward(loss)
    model_engine.step()

# 启动: deepspeed --num_gpus=8 train.py
```

---

## PyTorch FSDP

### FSDP vs ZeRO

FSDP 是 PyTorch 原生的 ZeRO-3 实现：

| 特性 | ZeRO (DeepSpeed) | FSDP (PyTorch) |
|------|------------------|----------------|
| 实现方式 | 独立库 | PyTorch 原生 |
| Stage 1/2/3 | ✅ | ✅ |
| CPU Offload | ✅ | ✅ |
| 易用性 | 配置文件 | API 配置 |

### FSDP 使用示例

```python
from torch.distributed.fsdp import (
    FullyShardedDataParallel as FSDP,
    ShardingStrategy,
    MixedPrecision,
)
from torch.distributed.fsdp.wrap import transformer_auto_wrap_policy

# 配置混合精度
mixed_precision = MixedPrecision(
    param_dtype=torch.bfloat16,
    reduce_dtype=torch.bfloat16,
    buffer_dtype=torch.bfloat16,
)

# 包装模型
model = FSDP(
    model,
    sharding_strategy=ShardingStrategy.FULL_SHARD,  # ZeRO-3
    # ShardingStrategy.SHARD_GRAD_OP,  # ZeRO-2
    # ShardingStrategy.NO_SHARD,  # DDP
    mixed_precision=mixed_precision,
    auto_wrap_policy=transformer_auto_wrap_policy,
    device_id=torch.cuda.current_device(),
)

# 训练循环与 DDP 相同
for batch in dataloader:
    loss = model(batch).loss
    loss.backward()
    optimizer.step()
    optimizer.zero_grad()
```

### FSDP 分片策略

| 策略 | 等价 ZeRO | 显存节省 |
|------|-----------|----------|
| `NO_SHARD` | DDP | 无 |
| `SHARD_GRAD_OP` | Stage 2 | 中等 |
| `FULL_SHARD` | Stage 3 | 最大 |
| `HYBRID_SHARD` | 混合 | 平衡 |

---

## 选择建议

| 场景 | 推荐方案 |
|------|----------|
| 模型 < 10B，单机 | DDP |
| 模型 10B-100B | FSDP 或 DeepSpeed ZeRO-3 |
| 需要 CPU Offload | DeepSpeed ZeRO-Infinity |
| PyTorch 原生体验 | FSDP |
| 更多优化选项 | DeepSpeed |

---

*下一篇：[04-model-parallelism.md](04-model-parallelism.md) - 模型并行详解*
