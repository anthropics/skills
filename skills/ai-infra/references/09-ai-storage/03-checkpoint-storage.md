# Checkpoint 存储

> Checkpoint 是大模型训练的"存档点"——训练可能持续数周，如果没有可靠的 Checkpoint 策略，一次故障就会让一切从头来过。

## 目录

- [为什么 Checkpoint 是最大的存储挑战](#为什么-checkpoint-是最大的存储挑战)
- [Checkpoint 的组成与大小](#checkpoint-的组成与大小)
- [同步 vs 异步 Checkpoint](#同步-vs-异步-checkpoint)
- [分布式 Checkpoint (DCP)](#分布式-checkpoint-dcp)
- [增量 Checkpoint](#增量-checkpoint)
- [GPUDirect Storage](#gpudirect-storage)
- [Checkpoint 管理策略](#checkpoint-管理策略)
- [生产级方案设计](#生产级方案设计)
- [延伸阅读](#延伸阅读)

---

## 为什么 Checkpoint 是最大的存储挑战

### 生活类比：游戏存档

```
大模型训练就像玩一个超长的 RPG 游戏:

  模型参数 = 角色属性和技能
  优化器状态 = 游戏进度和隐藏状态
  Checkpoint = 存档

  问题:
    存档文件巨大: 70B 模型的 Checkpoint ≈ 560 GB
    存档很频繁: 每 15-30 分钟存一次
    所有玩家同时存档: 256 个 GPU 同时写
    → 相当于 256 个人同时保存 2GB 的存档文件

  如果存档系统崩了:
    → 训练了 3 天的进度全部丢失
    → 数万美元的 GPU 算力浪费
    → 这就是为什么 Checkpoint 是 AI 存储最大的挑战
```

### 量化分析

```
┌─────────────────────────────────────────────────────────────────┐
│              Checkpoint 存储压力量化                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  模型: 70B 参数，BF16 训练，256 GPU，ZeRO Stage 3               │
│                                                                 │
│  Checkpoint 组成:                                                │
│    模型参数 (BF16): 70B × 2 bytes = 140 GB                      │
│    优化器 m (FP32): 70B × 4 bytes = 280 GB                      │
│    优化器 v (FP32): 70B × 4 bytes = 280 GB                      │
│    梯度 (BF16):     70B × 2 bytes = 140 GB                      │
│    ──────────────────────────────────────                        │
│    单次 Checkpoint 总量: ~840 GB                                 │
│                                                                 │
│  存储压力:                                                       │
│    保存频率: 每 30 分钟                                          │
│    保留数量: 最近 5 个                                            │
│    存储需求: 840 GB × 5 = 4.2 TB                                │
│    日写入量: 840 GB × 48 次/天 = ~40 TB/天                      │
│                                                                 │
│  带宽需求:                                                       │
│    目标: 30 秒内完成 Checkpoint                                  │
│    所需带宽: 840 GB / 30 s = 28 GB/s                             │
│                                                                 │
│  如果用同步保存:                                                 │
│    训练暂停 30 秒 × 48 次/天 = 24 分钟/天 的训练时间浪费         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Checkpoint 的组成与大小

### 各规模模型的 Checkpoint 大小

| 模型规模 | 参数(BF16) | 优化器(FP32) | 总 Checkpoint | 保留5个 |
|---------|-----------|------------|--------------|--------|
| 7B | 14 GB | 56 GB | ~84 GB | 420 GB |
| 13B | 26 GB | 104 GB | ~156 GB | 780 GB |
| 70B | 140 GB | 560 GB | ~840 GB | 4.2 TB |
| 175B | 350 GB | 1.4 TB | ~2.1 TB | 10.5 TB |
| 405B | 810 GB | 3.24 TB | ~4.86 TB | 24.3 TB |

### Checkpoint 内容详解

```python
"""Checkpoint 内容结构（PyTorch 为例）"""
import torch

# 一个典型的 Checkpoint 包含:
checkpoint = {
    # 1. 模型参数 (最核心，推理只需这个)
    "model_state_dict": model.state_dict(),
    # 大小: 参数量 × 精度字节数
    # 70B BF16 = 140 GB
    
    # 2. 优化器状态 (恢复训练需要)
    "optimizer_state_dict": optimizer.state_dict(),
    # Adam: 每个参数有 m (一阶矩) + v (二阶矩)，FP32
    # 大小: 参数量 × 4 bytes × 2 = 参数量 × 8 bytes
    # 70B Adam FP32 = 560 GB
    
    # 3. 学习率调度器
    "scheduler_state_dict": scheduler.state_dict(),
    # 大小: 很小 (几 KB)
    
    # 4. 训练元信息
    "epoch": epoch,
    "global_step": global_step,
    "loss": current_loss,
    "config": training_config,
    # 大小: 几 KB
    
    # 5. 随机状态 (保证可复现)
    "rng_states": {
        "python": random.getstate(),
        "numpy": np.random.get_state(),
        "torch": torch.random.get_rng_state(),
        "cuda": torch.cuda.get_rng_state_all(),
    },
    # 大小: 几 MB
}

# 总大小约等于: model_params + optimizer_states
# 对于 70B BF16 + Adam FP32: ~700 GB
```

---

## 同步 vs 异步 Checkpoint

### 同步 Checkpoint（传统方式）

```
同步 Checkpoint:

  ┌────────────────────────────────────────────────┐
  │  训练 ███████████ │等待│ 训练 ███████████ │等待│ │
  │                   │    │                   │    │ │
  │                   │ CP │                   │ CP │ │
  │                   │写入│                   │写入│ │
  └────────────────────────────────────────────────┘
                      ▲                        ▲
                      │                        │
                训练暂停 30s              训练暂停 30s

  问题: GPU 在 Checkpoint 期间完全空闲
  浪费: 每天浪费 24+ 分钟的 GPU 时间
  对于 256×H100 集群: 约 $2,000/天 的浪费
```

### 异步 Checkpoint

```
异步 Checkpoint:

  ┌────────────────────────────────────────────────┐
  │  训练 ██████████████████████████████████████████│
  │                   │                   │        │
  │  后台             │ CP 写入 ──────▶   │ CP ──▶ │
  │  线程             │ (不阻塞训练)      │        │
  └────────────────────────────────────────────────┘
                      ▲                   ▲
                      │                   │
                 仅暂停 ~1s          仅暂停 ~1s
                 (拷贝到CPU)        (拷贝到CPU)

  步骤:
    1. GPU → CPU 内存: 拷贝模型参数到 CPU（~1s，训练短暂暂停）
    2. CPU → NVMe/共享存储: 后台线程异步写入（不阻塞训练）
    3. 训练继续进行
```

### PyTorch 异步 Checkpoint 实现

```python
"""PyTorch 异步 Checkpoint 实现"""
import torch
import torch.distributed as dist
from torch.distributed.checkpoint import (
    save as dcp_save,
    load as dcp_load,
)
import threading
import shutil
import os

class AsyncCheckpointer:
    """异步 Checkpoint 管理器"""
    
    def __init__(
        self,
        checkpoint_dir: str,
        max_to_keep: int = 5,
    ):
        self.checkpoint_dir = checkpoint_dir
        self.max_to_keep = max_to_keep
        self._save_thread = None
        self._pending_state = None
        
    def save(self, model, optimizer, scheduler, step: int):
        """异步保存 Checkpoint"""
        # 1. 等待上一次保存完成
        if self._save_thread and self._save_thread.is_alive():
            self._save_thread.join()
        
        # 2. 快速拷贝到 CPU（阻塞，但很快）
        cpu_state = {
            "model": {k: v.cpu().clone() for k, v in model.state_dict().items()},
            "optimizer": optimizer.state_dict(),
            "scheduler": scheduler.state_dict(),
            "step": step,
        }
        
        # 3. 后台线程写入存储
        save_path = os.path.join(self.checkpoint_dir, f"step_{step}")
        self._save_thread = threading.Thread(
            target=self._background_save,
            args=(cpu_state, save_path),
        )
        self._save_thread.start()
        
        # 训练立即继续，不等待写入完成
        
    def _background_save(self, state, path):
        """后台保存线程"""
        os.makedirs(path, exist_ok=True)
        torch.save(state, os.path.join(path, "checkpoint.pt"))
        
        # 清理旧 Checkpoint
        self._cleanup_old_checkpoints()
        
    def _cleanup_old_checkpoints(self):
        """保留最近 N 个 Checkpoint"""
        checkpoints = sorted([
            d for d in os.listdir(self.checkpoint_dir)
            if d.startswith("step_")
        ], key=lambda x: int(x.split("_")[1]))
        
        while len(checkpoints) > self.max_to_keep:
            oldest = checkpoints.pop(0)
            shutil.rmtree(os.path.join(self.checkpoint_dir, oldest))

# 使用
checkpointer = AsyncCheckpointer("/nvme/checkpoints", max_to_keep=5)

for step in range(total_steps):
    loss = train_step(model, data)
    
    if step % checkpoint_interval == 0:
        checkpointer.save(model, optimizer, scheduler, step)
    # 训练不暂停，继续下一个 step
```

---

## 分布式 Checkpoint (DCP)

### 原理

```
传统 Checkpoint:                分布式 Checkpoint (DCP):
                               
  所有 rank 汇总到 rank 0:       每个 rank 保存自己的分片:

  Rank 0 ──┐                    Rank 0 ──▶ shard_0.pt
  Rank 1 ──┤                    Rank 1 ──▶ shard_1.pt
  Rank 2 ──┼──▶ Rank 0 ──▶     Rank 2 ──▶ shard_2.pt
  Rank 3 ──┤    (汇总)          Rank 3 ──▶ shard_3.pt
  ...      │    checkpoint.pt   ...
  Rank N ──┘                    Rank N ──▶ shard_N.pt

  问题:                         优势:
  - Rank 0 内存压力巨大          - 每个 rank 只保存自己的分片
  - 串行写入，速度慢             - 并行写入，速度 N 倍提升
  - Rank 0 成为瓶颈              - 无单点瓶颈
  - 不支持弹性恢复               - 支持不同数量 GPU 恢复
```

### PyTorch DCP 使用

```python
"""PyTorch Distributed Checkpoint (DCP) 使用"""
import torch.distributed.checkpoint as dcp
from torch.distributed.checkpoint.state_dict import (
    get_model_state_dict,
    get_optimizer_state_dict,
    set_model_state_dict,
    set_optimizer_state_dict,
    StateDictOptions,
)

# 保存 DCP
def save_distributed_checkpoint(model, optimizer, step, path):
    """使用 DCP 保存分布式 Checkpoint"""
    model_state = get_model_state_dict(model)
    optim_state = get_optimizer_state_dict(model, optimizer)
    
    state_dict = {
        "model": model_state,
        "optimizer": optim_state,
        "step": step,
    }
    
    dcp.save(state_dict, checkpoint_id=path)
    # 每个 rank 自动保存自己的分片到 path 目录

# 加载 DCP（支持不同并行度恢复）
def load_distributed_checkpoint(model, optimizer, path):
    """加载 DCP（自动处理 resharding）"""
    model_state = get_model_state_dict(model)
    optim_state = get_optimizer_state_dict(model, optimizer)
    
    state_dict = {
        "model": model_state,
        "optimizer": optim_state,
    }
    
    dcp.load(state_dict, checkpoint_id=path)
    # 自动处理 GPU 数量变化的 resharding
    
    set_model_state_dict(model, state_dict["model"])
    set_optimizer_state_dict(
        model, optimizer, state_dict["optimizer"]
    )
    
    return state_dict.get("step", 0)
```

---

## 增量 Checkpoint

```
增量 Checkpoint: 只保存变化的部分

  全量保存:  每次 840 GB
  增量保存:  首次 840 GB → 之后每次 ~50-100 GB

  原理:
    优化器状态每步只有小幅变化
    可以只保存 delta (差异)

  实现方式:
  ┌──────────────────────────────────────────────┐
  │  Step 1000: 全量 Checkpoint (840 GB)          │
  │  Step 1030: 增量 (仅变化部分, ~80 GB)         │
  │  Step 1060: 增量 (~80 GB)                     │
  │  Step 1090: 增量 (~80 GB)                     │
  │  Step 1120: 全量 Checkpoint (840 GB)          │ ← 定期全量
  │  ...                                          │
  └──────────────────────────────────────────────┘

  优势: 减少 80-90% 的写入量
  风险: 恢复时需要全量+所有增量，链条断了则无法恢复
  最佳实践: 每 N 次增量后做一次全量
```

---

## GPUDirect Storage

```
┌─────────────────────────────────────────────────────────────────┐
│              GPUDirect Storage (GDS)                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  传统路径:                                                       │
│    GPU → PCIe → CPU 内存 → 文件系统 → NVMe                      │
│    两次 PCIe 传输 + CPU 参与                                     │
│                                                                 │
│  GDS 路径:                                                       │
│    GPU → PCIe → NVMe (直接 DMA，绕过 CPU)                        │
│    一次 PCIe 传输，CPU 不参与                                    │
│                                                                 │
│  性能提升:                                                       │
│    Checkpoint 写入速度: 提升 50-100%                              │
│    CPU 负载: 减少 70%+                                           │
│    延迟: 减少 40-60%                                             │
│                                                                 │
│  要求:                                                           │
│    硬件: NVIDIA A100/H100 + NVMe SSD                             │
│    软件: CUDA 11.4+, NVIDIA GDS driver, cuFile API               │
│    文件系统: ext4, XFS, Lustre(实验), GPFS(实验)                 │
│                                                                 │
│  使用:                                                           │
│    export CUFILE_ENV_PATH_JSON=/etc/cufile.json                  │
│    # 代码中使用 cuFile API 替代 POSIX read/write                 │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Checkpoint 管理策略

### 保留策略

```python
"""Checkpoint 保留策略"""

class CheckpointRetentionPolicy:
    """
    多层保留策略:
    - 最近 N 个: 保留最新的 N 个 Checkpoint
    - 里程碑: 保留关键训练节点（如 loss 突破）
    - 定期归档: 每 K 个 Checkpoint 永久保留一个
    """
    
    def __init__(
        self,
        keep_recent: int = 5,
        keep_milestone: bool = True,
        archive_every: int = 20,
    ):
        self.keep_recent = keep_recent
        self.keep_milestone = keep_milestone
        self.archive_every = archive_every
        self.milestones = []
    
    def should_keep(self, step: int, loss: float) -> str:
        """
        返回: 'keep', 'archive', 'delete'
        """
        # 里程碑检测
        if self.keep_milestone and self._is_milestone(loss):
            self.milestones.append(step)
            return "keep"
        
        # 定期归档
        if step % (self.archive_every * 100) == 0:
            return "archive"  # 移动到冷存储
        
        # 最近 N 个
        return "keep"  # 由清理逻辑处理

    def _is_milestone(self, loss: float) -> bool:
        """检测是否为训练里程碑"""
        # 实现: 检测 loss 显著下降、达到特定阈值等
        return False  # 简化实现
```

### 存储层级策略

```
Checkpoint 分层存储:

  热 (Hot) — 本地 NVMe:
    最近 2-3 个 Checkpoint
    用途: 快速恢复（故障后 < 1 分钟恢复）
    性能: 6-14 GB/s

  温 (Warm) — 共享并行 FS:
    最近 5-10 个 Checkpoint
    用途: 跨节点恢复、实验对比
    性能: 10-100 GB/s

  冷 (Cold) — 对象存储 (S3 Standard):
    里程碑 + 定期归档 Checkpoint
    用途: 长期保存、审计
    性能: 1-10 GB/s
    成本: $0.023/GB/月

  冰 (Glacier) — 归档存储:
    所有历史 Checkpoint
    用途: 合规保留、灾备
    性能: 恢复需要数小时
    成本: $0.004/GB/月
```

---

## 生产级方案设计

### 256 GPU 集群 Checkpoint 方案

```
┌─────────────────────────────────────────────────────────────────┐
│         256 GPU 集群 Checkpoint 生产方案                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  硬件配置:                                                       │
│    32 节点 × 8 GPU，每节点 4× NVMe 3.84TB (总 15.36TB/节点)     │
│    共享存储: Lustre 200 TB (100+ GB/s 聚合带宽)                  │
│    对象存储: S3 (无限容量)                                       │
│                                                                 │
│  Checkpoint 流程:                                                │
│    1. 训练暂停 (~0.5s): GPU → CPU 内存拷贝                      │
│    2. 训练恢复                                                   │
│    3. 异步: CPU → 本地 NVMe (~3s @14 GB/s)                      │
│    4. 异步: NVMe → Lustre (后台，~30s @10 GB/s)                 │
│    5. 定期: Lustre → S3 (每天归档旧 Checkpoint)                 │
│                                                                 │
│  恢复策略:                                                       │
│    单节点故障: 从本地 NVMe 恢复 (< 30s)                         │
│    多节点故障: 从 Lustre 恢复 (< 2min)                           │
│    集群重建: 从 S3 恢复 (< 30min)                                │
│                                                                 │
│  使用 DCP: 每个 rank 保存自己的分片                              │
│    32 节点 × 8 GPU = 256 个分片文件                              │
│    每个分片 ~3.3 GB (840 GB / 256)                               │
│    并行写入 → 总写入时间 < 1s (本地 NVMe)                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 延伸阅读

- [PyTorch Distributed Checkpoint](https://pytorch.org/docs/stable/distributed.checkpoint.html)
- [DeepSpeed Checkpoint Engine](https://www.deepspeed.ai/docs/config-json/#checkpoint-options)
- [NVIDIA GPUDirect Storage](https://docs.nvidia.com/gpudirect-storage/)
- [Megatron-LM Checkpoint](https://github.com/NVIDIA/Megatron-LM)
- 论文: *CheckFreq: Frequent, Fine-Grained DNN Checkpointing* (FAST '21)

---

*上一篇：[02-distributed-filesystems.md](02-distributed-filesystems.md)* | *下一篇：[04-object-storage.md](04-object-storage.md)*

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **PyTorch.** *Distributed Checkpoint (DCP).*  
   https://pytorch.org/docs/stable/distributed.checkpoint.html

2. **NVIDIA.** *GPUDirect Storage for Checkpoint.*  
   https://developer.nvidia.com/gpudirect-storage

3. **Mohan, J., et al. (2021).** *CheckFreq: Frequent, Fine-Grained DNN Checkpointing.* FAST 2021.  
   https://www.usenix.org/conference/fast21/presentation/mohan
