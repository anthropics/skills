# Checkpoint 与容错

> 掌握大模型训练的保存策略和容错机制。

## 目录

- [为什么 Checkpoint 如此关键](#为什么-checkpoint-如此关键)
- [Checkpoint 策略](#checkpoint-策略)
- [分片 Checkpoint](#分片-checkpoint)
- [容错训练](#容错训练)
- [最佳实践](#最佳实践)

---

## 为什么 Checkpoint 如此关键

### 生活类比：游戏存档

```
大模型训练就像玩一个超长的 RPG 游戏：
  - LLaMA-70B 训练：2 万亿 tokens，用 2048 张 A100 跑 21 天
  - 一次训练的 GPU 费用：约 200 万美元

如果不存档会怎样？
  → 第 18 天一张 GPU 坏了，所有进度全部丢失
  → 200 万美元 × 18/21 ≈ 171 万美元付之东流

Checkpoint = 自动存档
  → 每隔一段时间保存训练状态
  → 硬件故障后从最近的存档恢复
  → 只损失"上次存档到故障点"之间的训练进度
```

### 大模型训练的故障现实

```
Google PaLM 训练日志揭示的故障频率：

┌──────────────────────────────────────────────────────────────┐
│  6144 张 TPU v4，训练 60 天                                   │
│                                                               │
│  硬件故障:         ~20 次                                     │
│  网络故障:         ~5 次                                      │
│  软件异常 (NaN):   ~10 次                                    │
│  ────────────────────────                                    │
│  总中断次数:       ~35 次 → 平均不到 2 天就中断一次           │
│                                                               │
│  Meta LLaMA-3 训练报告：                                      │
│  16384 张 H100，训练中经历了 400+ 次故障                      │
│  平均每天约 3 次故障                                          │
│                                                               │
│  结论：大规模训练不是"会不会故障"，而是"多久故障一次"        │
│  Checkpoint 不是可选项，而是生存的必需品                      │
└──────────────────────────────────────────────────────────────┘
```

### Checkpoint 到底保存什么？

```
一个完整的 Checkpoint 包含恢复训练所需的所有状态：

┌─ Checkpoint ─────────────────────────────────────────────┐
│                                                           │
│  1. 模型参数 (model_state_dict)                           │
│     所有层的 weight 和 bias                               │
│     FP16/BF16 格式，LLaMA-7B ≈ 14 GB                    │
│                                                           │
│  2. 优化器状态 (optimizer_state_dict)                     │
│     Adam: 一阶动量 m, 二阶动量 v, step 计数              │
│     FP32 格式，LLaMA-7B ≈ 84 GB（是参数的 6 倍！）      │
│                                                           │
│  3. 学习率调度器 (lr_scheduler)                           │
│     当前 warmup 到第几步，下一个 lr 是多少                │
│                                                           │
│  4. 训练进度 (metadata)                                   │
│     当前 step/epoch, global_step, consumed_tokens         │
│     随机数种子 (RNG state) —— 保证数据顺序一致            │
│                                                           │
│  5. 数据加载器状态                                         │
│     DataLoader 读到数据集的哪个位置                       │
│     不保存则恢复后可能重复使用/跳过数据                   │
│                                                           │
│  LLaMA-7B 完整 Checkpoint 大小:                          │
│  14 GB (params) + 84 GB (optimizer) ≈ 100 GB             │
│                                                           │
│  LLaMA-70B: ≈ 1 TB！                                    │
└───────────────────────────────────────────────────────────┘

为什么优化器状态这么大？
  Adam 对每个参数维护 2 个 FP32 状态：
  m_t = β₁·m_{t-1} + (1-β₁)·g_t     ← 4 bytes/param
  v_t = β₂·v_{t-1} + (1-β₂)·g_t²    ← 4 bytes/param
  加上 FP32 参数副本                  ← 4 bytes/param
  总计: 12 bytes/param  vs  参数本身 2 bytes/param (FP16)
```

---

## Checkpoint 策略

### 按步数保存（最常用）

```python
def save_checkpoint(model, optimizer, scheduler, step, path):
    """保存完整训练状态"""
    torch.save({
        'step': step,
        'model_state_dict': model.state_dict(),
        'optimizer_state_dict': optimizer.state_dict(),
        'scheduler_state_dict': scheduler.state_dict(),
        'rng_state': torch.cuda.get_rng_state(),  # GPU 随机状态
    }, path)

def load_checkpoint(model, optimizer, scheduler, path):
    """恢复训练状态"""
    checkpoint = torch.load(path, weights_only=False, map_location='cpu')
    model.load_state_dict(checkpoint['model_state_dict'])
    optimizer.load_state_dict(checkpoint['optimizer_state_dict'])
    scheduler.load_state_dict(checkpoint['scheduler_state_dict'])
    torch.cuda.set_rng_state(checkpoint['rng_state'])
    return checkpoint['step']
```

### 保存频率的权衡

```
保存太频繁：
  每 100 步保存，LLaMA-7B 每次 100GB
  I/O 时间: 100GB / 2GB/s(网络存储) = 50 秒
  训练速度损失: 如果每步 0.5 秒，100 步 = 50 秒
  相当于训练时间翻倍！

保存太稀疏：
  每 10000 步保存，故障后最多丢失 10000 步
  以每步 0.5 秒算 = 5000 秒 ≈ 83 分钟训练白费

实际经验值：
┌────────────────────────────────────────────────────────┐
│ 模型规模        │ 建议间隔     │ 理由                   │
├────────────────┼─────────────┼───────────────────────┤
│ < 7B           │ 每 1000 步  │ Checkpoint 小，I/O 快  │
│ 7B - 70B       │ 每 500 步   │ 故障频率增加           │
│ > 70B          │ 每 200 步   │ 每步时间长，丢不起     │
│ 不稳定环境      │ 每 15 分钟  │ 按时间而非步数         │
└────────────────────────────────────────────────────────┘
```

### 滚动保存（Rolling Checkpoint）

```python
# 只保留最近 K 个 Checkpoint，避免磁盘爆满

class RollingCheckpointManager:
    def __init__(self, save_dir, max_keep=3):
        self.save_dir = save_dir
        self.max_keep = max_keep
        self.saved = []  # 保存历史列表
    
    def save(self, state, step):
        path = os.path.join(self.save_dir, f"ckpt_step_{step}")
        torch.save(state, path)
        self.saved.append(path)
        
        # 超过限制，删除最旧的
        while len(self.saved) > self.max_keep:
            oldest = self.saved.pop(0)
            if os.path.exists(oldest):
                os.remove(oldest)
                print(f"Deleted old checkpoint: {oldest}")

# 使用
manager = RollingCheckpointManager("checkpoints/", max_keep=3)

for step in range(total_steps):
    loss = train_step(batch)
    if step % save_interval == 0:
        manager.save(training_state, step)

# 磁盘上始终只有 3 个 Checkpoint:
# checkpoints/ckpt_step_2000  (最旧)
# checkpoints/ckpt_step_2500
# checkpoints/ckpt_step_3000  (最新)
```

---

## 分片 Checkpoint

### 为什么需要分片？

```
问题：分布式训练中，模型参数和优化器状态分布在多个 GPU 上

方案 1: 聚合保存（传统方式）
  所有 GPU 将状态发送到 GPU 0 → GPU 0 保存到磁盘
  
  问题：
  1. GPU 0 需要 N 倍内存（收集所有分片） → OOM
  2. 所有 GPU 等 GPU 0 写完才能继续 → 串行瓶颈
  3. LLaMA-70B + 64 GPU: GPU 0 需要收集 1TB 数据 → 不可能

方案 2: 分片保存（现代方式）
  每个 GPU 只保存自己持有的那部分状态
  
  ┌─────────────────────────────────────────────────────────┐
  │  checkpoint_dir/                                        │
  │  ├── rank_0/                                            │
  │  │   ├── model_shard_0.pt     (GPU 0 的参数分片)        │
  │  │   └── optim_shard_0.pt     (GPU 0 的优化器分片)      │
  │  ├── rank_1/                                            │
  │  │   ├── model_shard_1.pt                               │
  │  │   └── optim_shard_1.pt                               │
  │  ├── ...                                                │
  │  └── metadata.json            (全局信息: 分片映射)      │
  └─────────────────────────────────────────────────────────┘
  
  优势：
  1. 并行写入：N 个 GPU 同时写，I/O 速度 ×N
  2. 无需额外内存：每个 GPU 只写自己的部分
  3. LLaMA-70B, 64 GPU: 每 GPU 写 ~16GB，64 路并行 → 几秒完成
```

### FSDP 分片保存

```python
from torch.distributed.checkpoint import (
    save,
    load,
    FileSystemWriter,
    FileSystemReader,
)
from torch.distributed.checkpoint.state_dict import (
    get_state_dict,
    set_state_dict,
    StateDictOptions,
)

# === 分片保存（每 GPU 并行写入自己的分片）===
model_state, optim_state = get_state_dict(model, optimizer)
state_dict = {
    "model": model_state,
    "optimizer": optim_state,
}
save(
    state_dict=state_dict,
    storage_writer=FileSystemWriter("checkpoint_dir/step_1000"),
)
# 所有 GPU 同时写入，速度 = 单 GPU 写入速度 × N

# === 分片加载 ===
state_dict = {
    "model": model_state,
    "optimizer": optim_state,
}
load(
    state_dict=state_dict,
    storage_reader=FileSystemReader("checkpoint_dir/step_1000"),
)
set_state_dict(model, optimizer, model_state, optim_state)
```

### DeepSpeed Checkpoint

```python
# 保存 —— DeepSpeed 自动处理分片
model_engine.save_checkpoint(
    save_dir="checkpoints",
    tag=f"step_{step}",
    # 可选：排除优化器状态（只保存模型，节省空间）
    # exclude_frozen_parameters=True,
)

# 加载 —— 自动匹配分片
model_engine.load_checkpoint(
    load_dir="checkpoints",
    tag="step_1000"
)
```

### Checkpoint 转换：分片 ↔ 聚合

```
场景：用 64 GPU 训练保存的分片 Checkpoint，想在 8 GPU 上继续训练

问题：分片方式与 GPU 数量绑定！
  64 GPU → 64 个分片
  8 GPU 加载 64 个分片 → 需要重新分配

解决方案：
  1. 合并为完整 Checkpoint → 再按新拓扑重新分片
  2. 使用 PyTorch DCP (Distributed Checkpoint) 的 reshape 功能
  3. DeepSpeed 的 zero_to_fp32.py 工具

# DeepSpeed: 合并分片为单一 FP32 模型
python zero_to_fp32.py checkpoints/step_1000 output/model.pt

# PyTorch DCP: 自动处理拓扑变化
# 内部实现：读取 metadata.json 中的分片映射
# → 计算新旧拓扑的对应关系
# → 每个 GPU 只读取自己需要的分片
```

---

## 容错训练

### 故障类型与应对

```
┌──────────────────────────────────────────────────────────────┐
│  故障类型           │ 频率        │ 应对策略                  │
├──────────────────────────────────────────────────────────────┤
│  GPU 硬件故障       │ 高          │ 从 Checkpoint 恢复       │
│  （显存 ECC 错误）  │             │ 替换故障节点后重启       │
│                     │             │                           │
│  网络中断           │ 中          │ NCCL 超时检测            │
│  （IB 链路抖动）    │             │ 自动重连或重启           │
│                     │             │                           │
│  训练不稳定（NaN）  │ 中          │ 回退到更早的 Checkpoint  │
│  （loss spike）     │             │ 跳过有问题的数据         │
│                     │             │                           │
│  节点抢占           │ 低-高       │ 弹性训练（调整 GPU 数）  │
│  （云上竞价实例）   │ (取决于平台) │                          │
│                     │             │                           │
│  慢节点（Straggler）│ 常见        │ 异步通信或剔除慢节点     │
│  （某个 GPU 特别慢）│             │                           │
└──────────────────────────────────────────────────────────────┘
```

### 自动恢复训练流程

```python
import logging
logger = logging.getLogger(__name__)

def resilient_training(model_engine, dataloader, checkpoint_dir, 
                       save_interval=500, max_retries=3):
    """带容错的训练循环"""
    
    # 1. 尝试从最新 Checkpoint 恢复
    start_step = 0
    try:
        _, info = model_engine.load_checkpoint(checkpoint_dir)
        if info is not None:
            start_step = info.get('step', 0)
            logger.info(f"Resumed from step {start_step}")
    except Exception:
        logger.info("No checkpoint found, starting fresh")
    
    # 2. 训练循环（带重试机制）
    step = start_step
    retry_count = 0
    
    for batch in dataloader:
        if step < start_step:
            step += 1
            continue  # 跳过已训练的步数
        
        try:
            loss = model_engine(batch).loss
            
            # Loss 异常检测
            if torch.isnan(loss) or torch.isinf(loss):
                logger.warning(f"Step {step}: NaN/Inf loss detected!")
                if retry_count < max_retries:
                    retry_count += 1
                    logger.info(f"Skipping bad batch (retry {retry_count}/{max_retries})")
                    continue
                else:
                    # 回退到上一个 Checkpoint
                    logger.error("Too many NaN losses, rolling back")
                    model_engine.load_checkpoint(checkpoint_dir)
                    retry_count = 0
                    continue
            
            model_engine.backward(loss)
            model_engine.step()
            retry_count = 0  # 成功训练，重置重试计数
            
        except RuntimeError as e:
            if "out of memory" in str(e):
                logger.error(f"OOM at step {step}, saving and exiting")
                torch.cuda.empty_cache()
                model_engine.save_checkpoint(checkpoint_dir, tag=f"emergency_{step}")
                raise
            else:
                logger.error(f"Runtime error at step {step}: {e}")
                raise
        
        # 3. 定期保存
        if step % save_interval == 0:
            model_engine.save_checkpoint(checkpoint_dir, tag=f"step_{step}")
            logger.info(f"Saved checkpoint at step {step}")
        
        step += 1
```

### Loss Spike 处理策略

```
Loss Spike（训练不稳定）是大模型训练的常见问题：

正常训练:
  loss: 2.5 → 2.4 → 2.3 → 2.2 → 2.1 → ...  ← 平稳下降

Loss Spike:
  loss: 2.5 → 2.4 → 2.3 → 15.7 → 892.3 → NaN  ← 突然爆炸！

原因分析：
  1. 数据问题：某个 batch 包含异常样本（极长文本、特殊编码）
  2. 学习率过大：在 loss landscape 的陡峭区域
  3. 数值溢出：梯度值超出 FP16 表示范围
  4. 随机因素：数据并行中某个 GPU 的梯度异常大

应对策略（Meta LLaMA-3 训练报告中使用的方法）：

┌─────────────────────────────────────────────────────────┐
│  策略 1: 回退重训                                        │
│  检测到 loss spike → 回退 100 步的 Checkpoint            │
│  跳过导致 spike 的数据 → 继续训练                       │
│                                                          │
│  策略 2: 降低学习率                                      │
│  检测到 loss spike → 暂时将 lr 降低 50%                 │
│  待 loss 恢复正常后 → 逐渐恢复原 lr                    │
│                                                          │
│  策略 3: 梯度裁剪 (Gradient Clipping)                   │
│  每步检查梯度范数，超过阈值则等比缩放                   │
│  torch.nn.utils.clip_grad_norm_(params, max_norm=1.0)   │
│                                                          │
│  策略 4: 数据过滤                                        │
│  记录导致 spike 的 batch 索引                            │
│  下次训练时跳过这些数据                                  │
└─────────────────────────────────────────────────────────┘
```

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

```
弹性训练的应用场景：

场景 1: 云上竞价实例
  开始: 128 GPU (便宜) → 部分实例被抢占 → 剩 96 GPU → 继续训练
  自动调整 batch size 和数据并行度

场景 2: 故障后部分恢复  
  128 GPU → 2 张 GPU 故障 → 126 GPU
  传统方式：等替换 GPU 后全部重启（可能等数小时）
  弹性训练：立即用 126 GPU 继续（仅调整 batch 配置）

场景 3: 资源共享集群
  夜间集群空闲：扩展到 128 GPU
  白天用户增多：缩减到 64 GPU
  训练全程不中断
```

---

## 最佳实践

### 异步 Checkpoint（不阻塞训练）

```
同步保存的问题：
  训练 → 暂停 → 写 100GB 到磁盘 (50 秒) → 继续训练
  50 秒 × 每小时保存 2 次 = 每小时浪费 100 秒

异步保存：
  训练 → 后台线程写磁盘 → 训练继续不停
  
  ┌─────────────────────────────────────────────────────┐
  │  主线程:  [训练] [训练] [训练] [训练] [训练] ...    │
  │                  ↓ 快照                              │
  │  后台线程:       [──── 写磁盘 ────]                 │
  │                  (不影响训练速度)                     │
  └─────────────────────────────────────────────────────┘
  
  实现要点：
  1. 快照状态到 CPU 内存（~1 秒，需要额外 CPU 内存）
  2. 后台线程从 CPU 内存写入磁盘
  3. 写入完成前不能开始下一次保存

PyTorch 2.0+ 的 torch.distributed.checkpoint 已支持异步保存
DeepSpeed 也支持 async checkpoint
```

### 存储架构选择

```
┌──────────────────────────────────────────────────────────────┐
│  存储层次与适用场景                                           │
├──────────────────────────────────────────────────────────────┤
│                                                               │
│  1. 本地 NVMe SSD（最快）                                     │
│     速度: ~3-6 GB/s                                          │
│     容量: 通常 1-4 TB/节点                                   │
│     用途: 临时 Checkpoint（滚动保存）                        │
│     风险: 节点挂了 SSD 上的数据也没了                        │
│                                                               │
│  2. 分布式文件系统（推荐）                                    │
│     Lustre/GPFS: ~50-200 GB/s (聚合)                         │
│     速度快 + 高可用 + 跨节点访问                              │
│     用途: 主要 Checkpoint 存储                               │
│                                                               │
│  3. 对象存储（最安全）                                        │
│     S3/GCS/COS: ~几 GB/s                                     │
│     三副本 + 跨区域备份，几乎不会丢                          │
│     用途: 里程碑 Checkpoint 长期保存                         │
│                                                               │
│  推荐组合:                                                    │
│  本地 SSD (滚动保存最近 3 个)                                │
│     ↓ 每 N 次同步到                                          │
│  分布式文件系统 (保留最近 10 个)                              │
│     ↓ 重要里程碑 (每 10% 进度)                               │
│  对象存储 (永久保留)                                          │
└──────────────────────────────────────────────────────────────┘
```

### Checkpoint 完整性验证

```python
import hashlib

def save_checkpoint_with_verification(state, path):
    """保存 Checkpoint 并记录校验和"""
    torch.save(state, path)
    
    # 计算 SHA256 校验和
    sha256 = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(8192), b''):
            sha256.update(chunk)
    
    checksum = sha256.hexdigest()
    with open(path + '.sha256', 'w') as f:
        f.write(checksum)
    
    return checksum

def validate_checkpoint(path):
    """验证 Checkpoint 完整性"""
    # 校验和验证
    if os.path.exists(path + '.sha256'):
        with open(path + '.sha256', 'r') as f:
            expected = f.read().strip()
        sha256 = hashlib.sha256()
        with open(path, 'rb') as f:
            for chunk in iter(lambda: f.read(8192), b''):
                sha256.update(chunk)
        actual = sha256.hexdigest()
        assert actual == expected, f"Checksum mismatch: {actual} != {expected}"
    
    # 内容验证
    ckpt = torch.load(path, map_location='cpu', weights_only=False)
    required_keys = ['model_state_dict', 'optimizer_state_dict']
    for key in required_keys:
        assert key in ckpt, f"Missing key: {key}"
    
    # 检查参数是否包含 NaN
    for name, param in ckpt['model_state_dict'].items():
        assert not torch.isnan(param).any(), f"NaN found in {name}"
    
    print(f"Checkpoint validated: {path}")
    print(f"Keys: {list(ckpt.keys())}")
    return True
```

### Checkpoint 策略总览

| 策略 | 频率 | 适用场景 | 存储位置 |
|------|------|----------|---------|
| 滚动保存 | 每 N 步 | 长时间训练，防故障 | 本地 SSD |
| 按时间 | 每 15-30 分钟 | 不稳定环境 | 分布式 FS |
| 里程碑 | 每 10% 进度 | 长期保留 | 对象存储 |
| 最优模型 | 验证集最优时 | 微调任务 | 分布式 FS |
| 紧急保存 | 故障检测时 | 抢救进度 | 本地 SSD |

---

## 小结

```
大模型 Checkpoint 的核心要点：

1. 不是可选项：千卡训练平均不到 2 天故障一次，不保存 = 烧钱
2. 完整保存：模型 + 优化器 + 调度器 + RNG + 数据位置
3. 分片保存：大模型必须并行写入，单点汇总不可行
4. 异步保存：不阻塞训练，用 CPU 内存做缓冲
5. 分层存储：本地 SSD（快但不安全）+ 分布式 FS + 对象存储（慢但安全）
6. 容错训练：自动恢复 + Loss spike 处理 + 弹性 GPU 数量
```

---

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **Maeng, K., et al. (2021).** *Understanding and Improving Failure Tolerant Training for Deep Learning Recommendation with Partial Recovery.*  
   https://arxiv.org/abs/2011.02999

2. **Mohan, J., et al. (2021).** *CheckFreq: Frequent, Fine-Grained DNN Checkpointing.* FAST 2021.  
   https://www.usenix.org/conference/fast21/presentation/mohan

3. **PyTorch Documentation.** *Distributed Checkpoint (DCP).*  
   https://pytorch.org/docs/stable/distributed.checkpoint.html

4. **DeepSpeed Documentation.** *Checkpoint Configuration.*  
   https://www.deepspeed.ai/docs/config-json/#checkpoint-options
