# 3D 并行实践

> 掌握 Megatron-LM 和 DeepSpeed 的 3D 并行配置。

## 目录

- [3D 并行原理](#3d-并行原理)
- [Megatron-LM 配置](#megatron-lm-配置)
- [DeepSpeed 配置](#deepspeed-配置)
- [配置建议](#配置建议)

---

## 3D 并行原理

### 组合策略

```
3D 并行 = 数据并行 (DP) + 张量并行 (TP) + 流水线并行 (PP)

GPU 总数 = DP × TP × PP

例: 64 GPU, DP=4, TP=4, PP=4
```

### GPU 分组

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        64 GPU 3D 并行布局                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   DP Group 0-3: 4 个数据并行组                                           │
│                                                                         │
│   每个 DP Group 内:                                                     │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │  PP Stage 0          PP Stage 1         PP Stage 2    PP Stage 3│  │
│   │  ┌─────────────┐    ┌─────────────┐    ┌───────────┐ ┌─────────┐│  │
│   │  │TP: GPU 0-3 │    │TP: GPU 4-7 │    │TP: 8-11  │ │TP: 12-15││  │
│   │  │(层 0-23)   │ →  │(层 24-47)  │ →  │(层 48-71)│→│(层 72-95)││  │
│   │  └─────────────┘    └─────────────┘    └───────────┘ └─────────┘│  │
│   └─────────────────────────────────────────────────────────────────┘  │
│                                                                         │
│   TP: 同一 Stage 内 4 GPU 切分每层                                       │
│   PP: 4 个 Stage 串行执行                                               │
│   DP: 4 个这样的组并行处理不同数据                                        │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Megatron-LM 配置

### 启动命令

```bash
torchrun \
    --nproc_per_node 8 \
    --nnodes 8 \
    --master_addr $MASTER_ADDR \
    --master_port $MASTER_PORT \
    pretrain_gpt.py \
    --tensor-model-parallel-size 8 \
    --pipeline-model-parallel-size 4 \
    --num-layers 96 \
    --hidden-size 12288 \
    --num-attention-heads 96 \
    --seq-length 2048 \
    --micro-batch-size 1 \
    --global-batch-size 1536 \
    --lr 1e-4 \
    --train-iters 100000 \
    --fp16
```

### 关键参数

| 参数 | 说明 |
|------|------|
| `tensor-model-parallel-size` | TP 大小，建议 2-8 |
| `pipeline-model-parallel-size` | PP 大小 |
| `micro-batch-size` | 每 GPU 每次处理的 batch |
| `global-batch-size` | 总 batch size |

---

## DeepSpeed 配置

### ds_config.json

```json
{
    "train_batch_size": 512,
    "train_micro_batch_size_per_gpu": 2,
    "gradient_accumulation_steps": 64,
    
    "zero_optimization": {
        "stage": 1,
        "offload_optimizer": {
            "device": "cpu"
        }
    },
    
    "fp16": {
        "enabled": true,
        "loss_scale": 0,
        "loss_scale_window": 1000
    },
    
    "pipeline": {
        "stages": 4,
        "partition_method": "uniform"
    },
    
    "tensor_parallel": {
        "tp_size": 4
    },
    
    "gradient_clipping": 1.0
}
```

### 代码配置

```python
import deepspeed

model = MyLargeModel()

model_engine, optimizer, _, _ = deepspeed.initialize(
    model=model,
    model_parameters=model.parameters(),
    config="ds_config.json"
)

# 训练循环
for batch in dataloader:
    loss = model_engine(batch).loss
    model_engine.backward(loss)
    model_engine.step()
```

---

## 配置建议

### 并行度选择

| 模型规模 | TP | PP | DP |
|----------|----|----|-----|
| 7B | 1-2 | 1 | 最大化 |
| 30B | 4 | 2 | 剩余 |
| 70B | 8 | 4 | 剩余 |
| 175B | 8 | 8 | 剩余 |

### 经验法则

1. **TP 优先节点内**：需要 NVLink 高带宽
2. **PP 可跨节点**：通信量较小
3. **DP 填充剩余**：`DP = N_GPU / (TP × PP)`
4. **平衡显存和效率**：TP/PP 太大会增加通信开销

---

*下一篇：[07-training-frameworks.md](07-training-frameworks.md) - 训练框架对比*
