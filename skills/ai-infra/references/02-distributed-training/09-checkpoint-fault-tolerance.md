# Checkpoint 与容错

> 掌握大模型训练的保存策略和容错机制。

## 目录

- [Checkpoint 策略](#checkpoint-策略)
- [分片 Checkpoint](#分片-checkpoint)
- [容错训练](#容错训练)
- [最佳实践](#最佳实践)

---

## Checkpoint 策略

### 基本保存

```python
def save_checkpoint(model, optimizer, epoch, loss, path):
    torch.save({
        'epoch': epoch,
        'model_state_dict': model.state_dict(),
        'optimizer_state_dict': optimizer.state_dict(),
        'loss': loss,
    }, path)

def load_checkpoint(model, optimizer, path):
    checkpoint = torch.load(path, weights_only=False)
    model.load_state_dict(checkpoint['model_state_dict'])
    optimizer.load_state_dict(checkpoint['optimizer_state_dict'])
    return checkpoint['epoch']
```

### 定期保存

```python
for step, batch in enumerate(dataloader):
    loss = train_step(batch)
    
    # 每 1000 步保存
    if step % 1000 == 0:
        save_checkpoint(model, optimizer, step, f"ckpt_{step}.pt")
    
    # 保留最近 3 个
    if step > 3000:
        os.remove(f"ckpt_{step-3000}.pt")
```

---

## 分片 Checkpoint

### FSDP 分片保存

```python
from torch.distributed.checkpoint import (
    save_state_dict,
    load_state_dict,
    FileSystemWriter,
    FileSystemReader
)

# 分片保存 (每 GPU 保存自己的部分)
writer = FileSystemWriter("checkpoint_dir")
save_state_dict(
    state_dict={"model": model.state_dict()},
    storage_writer=writer,
)

# 分片加载
reader = FileSystemReader("checkpoint_dir")
load_state_dict(
    state_dict={"model": model.state_dict()},
    storage_reader=reader,
)
```

### DeepSpeed Checkpoint

```python
# 保存
model_engine.save_checkpoint(
    save_dir="checkpoints",
    tag=f"step_{step}"
)

# 加载
model_engine.load_checkpoint(
    load_dir="checkpoints",
    tag="step_1000"
)
```

---

## 容错训练

### DeepSpeed 弹性训练

```json
{
    "elasticity": {
        "enabled": true,
        "max_train_batch_size": 2048,
        "micro_batch_sizes": [4, 8, 16],
        "min_gpus": 32,
        "max_gpus": 128,
        "prefer_larger_batch_size": true
    }
}
```

### 故障恢复

```python
# 自动恢复训练
checkpoint_dir = "checkpoints"

try:
    # 尝试加载最新 checkpoint
    model_engine.load_checkpoint(checkpoint_dir)
    print("Resumed from checkpoint")
except:
    print("Starting fresh training")

# 训练循环
for step, batch in enumerate(dataloader):
    try:
        loss = model_engine(batch).loss
        model_engine.backward(loss)
        model_engine.step()
    except Exception as e:
        print(f"Error at step {step}: {e}")
        # 保存并退出
        model_engine.save_checkpoint(checkpoint_dir)
        raise
    
    # 定期保存
    if step % save_interval == 0:
        model_engine.save_checkpoint(checkpoint_dir)
```

---

## 最佳实践

### Checkpoint 策略

| 策略 | 频率 | 适用场景 |
|------|------|----------|
| 按步数 | 每 N 步 | 长时间训练 |
| 按时间 | 每 N 分钟 | 不稳定环境 |
| 按 epoch | 每 epoch | 小数据集 |
| 最优模型 | 验证最优时 | 微调任务 |

### 存储建议

1. **使用高速存储**：NVMe SSD 或分布式存储
2. **异步保存**：不阻塞训练
3. **压缩**：对大模型 checkpoint 压缩
4. **多副本**：重要 checkpoint 备份

### 恢复检查清单

```python
def validate_checkpoint(checkpoint_path):
    """验证 checkpoint 完整性"""
    ckpt = torch.load(checkpoint_path, map_location='cpu')
    
    assert 'model_state_dict' in ckpt
    assert 'optimizer_state_dict' in ckpt
    assert 'epoch' in ckpt or 'step' in ckpt
    
    print(f"Checkpoint validated: {checkpoint_path}")
    print(f"Keys: {ckpt.keys()}")
    return True
```

---

## 小结

- **定期保存**：防止长时间训练丢失
- **分片 Checkpoint**：大模型必须分片保存
- **弹性训练**：支持 GPU 数量变化
- **故障恢复**：自动从最近 checkpoint 恢复

---

*返回：[README.md](README.md) - 章节索引*
