# 通信优化

> 理解集合通信原语和 NCCL 优化技巧。

## 目录

- [集合通信原语](#集合通信原语)
- [NCCL 优化](#nccl-优化)
- [通信与计算重叠](#通信与计算重叠)
- [梯度压缩](#梯度压缩)

---

## 集合通信原语

### 常用操作

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       常用集合通信操作                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   AllReduce: 所有节点数据求和后广播                                      │
│   ┌───┐ ┌───┐ ┌───┐ ┌───┐        ┌───┐ ┌───┐ ┌───┐ ┌───┐             │
│   │ A │ │ B │ │ C │ │ D │   →    │Sum│ │Sum│ │Sum│ │Sum│             │
│   └───┘ └───┘ └───┘ └───┘        └───┘ └───┘ └───┘ └───┘             │
│   用途: DDP 梯度同步                                                    │
│                                                                         │
│   AllGather: 收集所有节点数据                                           │
│   ┌───┐ ┌───┐ ┌───┐ ┌───┐        ┌────────────────┐ (每节点)           │
│   │ A │ │ B │ │ C │ │ D │   →    │ A │ B │ C │ D │                    │
│   └───┘ └───┘ └───┘ └───┘        └────────────────┘                    │
│   用途: ZeRO-3 收集模型参数                                              │
│                                                                         │
│   ReduceScatter: 规约后分散                                             │
│   ┌────────────────┐ (×4)        ┌───┐ ┌───┐ ┌───┐ ┌───┐             │
│   │ A │ B │ C │ D │        →    │ΣA │ │ΣB │ │ΣC │ │ΣD │             │
│   └────────────────┘              └───┘ └───┘ └───┘ └───┘             │
│   用途: ZeRO 梯度切分                                                    │
│                                                                         │
│   Broadcast: 一对多广播                                                 │
│   用途: 模型初始化同步                                                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### PyTorch 使用

```python
import torch.distributed as dist

# AllReduce
dist.all_reduce(tensor, op=dist.ReduceOp.SUM)

# AllGather
gathered = [torch.zeros_like(tensor) for _ in range(world_size)]
dist.all_gather(gathered, tensor)

# Broadcast
dist.broadcast(tensor, src=0)
```

---

## NCCL 优化

### 环境变量

```python
import os

# 使用 NCCL 后端 (GPU 最优)
dist.init_process_group(backend='nccl')

# 异步错误处理
os.environ['NCCL_ASYNC_ERROR_HANDLING'] = '1'

# 缓冲区大小 (16MB)
os.environ['NCCL_BUFFSIZE'] = '16777216'

# 调试信息
os.environ['NCCL_DEBUG'] = 'INFO'
```

### DDP 优化

```python
model = DDP(
    model,
    device_ids=[rank],
    bucket_cap_mb=25,           # 梯度聚合桶大小
    find_unused_parameters=False,
    gradient_as_bucket_view=True,  # 减少内存拷贝
)
```

---

## 通信与计算重叠

### 原理

在 GPU 计算时同时进行通信，隐藏通信延迟。

### DeepSpeed 配置

```json
{
    "zero_optimization": {
        "stage": 2,
        "overlap_comm": true,
        "contiguous_gradients": true,
        "reduce_bucket_size": 5e8
    }
}
```

### FSDP 配置

```python
from torch.distributed.fsdp import BackwardPrefetch

model = FSDP(
    model,
    backward_prefetch=BackwardPrefetch.BACKWARD_PRE,
    forward_prefetch=True,
)
```

---

## 梯度压缩

### 1-bit Adam

```json
{
    "zero_optimization": {
        "stage": 2
    },
    "optimizer": {
        "type": "OneBitAdam",
        "params": {
            "lr": 1e-4,
            "freeze_step": 400,
            "cuda_aware": true
        }
    }
}
```

### 效果

- 通信量减少 32 倍
- 训练效果基本不变
- 适合带宽受限场景

---

*下一篇：[09-checkpoint-fault-tolerance.md](09-checkpoint-fault-tolerance.md) - Checkpoint 与容错*
