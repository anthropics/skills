# 数据并行详解

> 掌握 DDP、ZeRO、FSDP 的原理和使用。

## 目录

- [数据并行原理](#数据并行原理)
- [PyTorch DDP](#pytorch-ddp)
- [ZeRO 优化器](#zero-优化器)
- [PyTorch FSDP](#pytorch-fsdp)
- [选择建议](#选择建议)

---

## 数据并行原理

### 生活类比：连锁餐厅的标准化运营

想象你开了一家连锁餐厅，每个分店都有**完全相同的菜谱**（模型副本），但处理**不同地区的订单**（不同数据分片）：

```
┌─────────────────────────────────────────────────────────────────────────┐
│                  数据并行 = 连锁餐厅模式                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│                    总菜谱 (完整模型)                                     │
│                   ┌───────────┐                                         │
│                   │ 一模一样  │                                          │
│              ┌────┴────┬──────┴───┬──────────┐                          │
│              ▼         ▼          ▼          ▼                          │
│          分店 A    分店 B     分店 C     分店 D                         │
│          (GPU 0)   (GPU 1)    (GPU 2)    (GPU 3)                       │
│          处理      处理       处理       处理                           │
│          海淀区    朝阳区     丰台区     通州区                         │
│          的订单    的订单     的订单     的订单                         │
│                                                                         │
│    每天结束，各分店交流经验（AllReduce 梯度），统一更新菜谱             │
│                                                                         │
│    关键点：                                                              │
│    1. 菜谱完全相同 → 每个 GPU 持有完整模型副本                         │
│    2. 订单不同 → 每个 GPU 处理不同数据分片                             │
│    3. 交流经验 → AllReduce 同步梯度（求平均）                          │
│    4. 统一更新 → 各 GPU 用相同平均梯度更新参数                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 工作流程详解

数据并行的五步循环：

```
Step 1: 复制模型              Step 2: 切分数据
┌──────────────┐             全部数据: [D0, D1, D2, D3, ...]
│  完整模型 M  │                    │
│  (参数 θ)    │            ┌───────┼───────┬───────┐
└──────┬───────┘            ▼       ▼       ▼       ▼
       │ 广播              GPU0:D0  GPU1:D1  GPU2:D2  GPU3:D3
  ┌────┼────┬────┐
  ▼    ▼    ▼    ▼
 M₀   M₁   M₂   M₃         (每个 GPU 只看到 1/N 的数据)
(完全相同的 4 份副本)

Step 3: 独立计算              Step 4: AllReduce 同步
GPU 0: loss₀ = L(M₀(D0))    GPU 0: g₀ ──┐
GPU 1: loss₁ = L(M₁(D1))    GPU 1: g₁ ──┼── AllReduce ── ḡ = (g₀+g₁+g₂+g₃)/4
GPU 2: loss₂ = L(M₂(D2))    GPU 2: g₂ ──┤   (Ring 算法)
GPU 3: loss₃ = L(M₃(D3))    GPU 3: g₃ ──┘

Step 5: 同步更新              数学保证：等价于大 batch 训练
GPU 0: θ₀ = θ₀ - lr·ḡ       全局 batch_size = per_gpu_batch × N
GPU 1: θ₁ = θ₁ - lr·ḡ       等价于单卡用 4 倍 batch 训练
GPU 2: θ₂ = θ₂ - lr·ḡ       （梯度求平均 = 对所有样本梯度求平均）
GPU 3: θ₃ = θ₃ - lr·ḡ
```

### 通信原理：Ring AllReduce

为什么不用"一对多"广播，而用 Ring？

```
朴素方法：所有 GPU 发给 GPU 0 汇总，再广播回来
  问题：GPU 0 成为通信瓶颈，带宽 = B（单链路）

Ring AllReduce：N 个 GPU 组成环，分 2(N-1) 步完成
  优势：每条链路并行传输，有效带宽 = B·(N-1)/N ≈ B

┌──────┐     ┌──────┐
│GPU 0 │ ──→ │GPU 1 │
│      │ ←── │      │
└──┬───┘     └───┬──┘
   │  ↑          │  ↑
   ▼  │          ▼  │
┌──┴───┐     ┌───┴──┐
│GPU 3 │ ←── │GPU 2 │
│      │ ──→ │      │
└──────┘     └──────┘

过程：
1. Reduce-Scatter 阶段（N-1 步）：每步传 1/N 数据，最终每 GPU 持有 1/N 的完整归约结果
2. All-Gather 阶段（N-1 步）：每步传 1/N 数据，最终每 GPU 拥有完整结果

总通信量：2·(N-1)/N · DataSize ≈ 2·DataSize
关键：与 GPU 数量 N 几乎无关！这就是数据并行能扩展到数百 GPU 的原因
```

### 数学等价性：为什么数据并行结果与单卡相同？

```
单卡训练（batch_size = 4B）:
  g = (1/4B) Σᵢ ∇L(xᵢ)

4 卡数据并行（每卡 batch_size = B）:
  g₀ = (1/B) Σ ∇L(x₀ᵢ)   # GPU 0 的局部梯度
  g₁ = (1/B) Σ ∇L(x₁ᵢ)   # GPU 1 的局部梯度
  g₂ = (1/B) Σ ∇L(x₂ᵢ)   # GPU 2 的局部梯度
  g₃ = (1/B) Σ ∇L(x₃ᵢ)   # GPU 3 的局部梯度
  
  ḡ = (g₀+g₁+g₂+g₃)/4 = (1/4B) Σᵢ ∇L(xᵢ) = g  ✓ 完全相同！

结论：数据并行在数学上严格等价于用更大 batch 在单卡上训练
```

---

## PyTorch DDP

### DDP 的核心优化：梯度桶化（Gradient Bucketing）

朴素数据并行：等所有梯度算完 → AllReduce → 通信和计算完全串行。

DDP 的巧妙之处：**把通信藏在计算里**。

```
朴素方式（通信与计算串行）：
┌──────────── 反向传播 ──────────────┐┌──── AllReduce ────┐
│ 计算 layer N → ... → layer 1 梯度  ││ 同步所有梯度       │
└────────────────────────────────────┘└────────────────────┘
 总时间 = T_compute + T_comm （加法）

DDP 桶化（通信与计算重叠）：
                反向传播
├─ layer N,N-1 ─┤─ layer N-2,N-3 ─┤─ layer N-4,N-5 ─┤
                │                   │                   │
                ├ AllReduce 桶 1 ──┤ AllReduce 桶 2 ──┤ AllReduce 桶 3
                │                   │                   │
 总时间 ≈ max(T_compute, T_comm)   （重叠，不是加法！）
```

**类比**：你在考试时，写完第一页就让助手去复印（通信），你继续写第二页。写完第二页时，第一页已经复印好了。这就是**计算-通信重叠**。

**关键实现细节**：
- 梯度从模型**最后一层往前**计算（反向传播顺序）
- DDP 把参数按反向顺序分组为"桶"（默认 25MB 一桶）
- 一个桶的梯度算完，立刻启动该桶的 AllReduce
- 下一个桶的梯度计算与上一个桶的通信并行

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
    
    # 使用 DistributedSampler —— 确保每个 GPU 看到不同的数据
    sampler = torch.utils.data.distributed.DistributedSampler(
        dataset, num_replicas=world_size, rank=rank
    )
    dataloader = DataLoader(dataset, sampler=sampler, batch_size=32)
    
    optimizer = torch.optim.AdamW(model.parameters())
    
    for epoch in range(epochs):
        sampler.set_epoch(epoch)  # 确保每 epoch 数据打乱方式不同
        for batch in dataloader:
            loss = model(batch).loss
            loss.backward()  # DDP 自动在反向传播中插入 AllReduce
            optimizer.step()
            optimizer.zero_grad()
    
    dist.destroy_process_group()

# 启动: torchrun --nproc_per_node=4 train.py
```

### DDP 关键参数详解

```python
model = DDP(
    model,
    device_ids=[rank],
    output_device=rank,
    find_unused_parameters=False,  # 有未使用参数时设为 True（但会降低性能）
    bucket_cap_mb=25,              # 梯度桶大小，影响通信重叠效果
    # 桶太小：通信次数多，启动开销大
    # 桶太大：等待时间长，重叠效果差
    # 经验值：25MB 适合大多数场景，大模型可调至 40-50MB
)
```

### DDP 的局限性

```
问题：每个 GPU 必须存储完整模型！

以 LLaMA-7B + Adam 优化器为例：
  FP16 参数:      7B × 2 bytes  =  14 GB
  FP16 梯度:      7B × 2 bytes  =  14 GB
  FP32 优化器状态: 7B × 12 bytes =  84 GB  （FP32副本 + m + v）
  ─────────────────────────────────────────
  合计每 GPU:                      112 GB

  单张 A100 80GB → 放不下！

这就是为什么需要 ZeRO / FSDP：不复制完整状态，而是切分它们。
```

---

## ZeRO 优化器

### 核心思想：从"每人一份"到"合租共享"

**类比**：四个室友合租一套房子。

```
DDP 模式（每人一份）= 每个室友各买一套完整家具：
  室友 A: 冰箱+洗衣机+微波炉+沙发  （全部 16Ψ）
  室友 B: 冰箱+洗衣机+微波炉+沙发
  室友 C: 冰箱+洗衣机+微波炉+沙发
  室友 D: 冰箱+洗衣机+微波炉+沙发
  浪费！总共买了 4 套一模一样的家具

ZeRO 模式（合租共享）= 每人负责一部分家具：
  Stage 1: 合买贵的（优化器），便宜的各买
    A: 冰箱+自己的碗筷+自己的衣服
    B: 洗衣机+自己的碗筷+自己的衣服
    C: 微波炉+自己的碗筷+自己的衣服
    D: 沙发+自己的碗筷+自己的衣服

  Stage 2: 连碗筷也合买（+梯度）
  Stage 3: 连衣服也合买（+参数）→ 需要时找室友借
```

### 三阶段原理与详细计算

```
假设 N 个 GPU，模型参数量 Ψ

FP16 模型训练，每个参数需要存储：
  FP16 参数:   2 bytes × Ψ  =  2Ψ
  FP16 梯度:   2 bytes × Ψ  =  2Ψ
  FP32 优化器状态（以 Adam 为例）:
    - FP32 参数副本:  4 bytes × Ψ  =  4Ψ
    - FP32 一阶动量 m: 4 bytes × Ψ  =  4Ψ
    - FP32 二阶动量 v: 4 bytes × Ψ  =  4Ψ
    - 小计:                           12Ψ
  ────────────────────────────────────
  总计每 GPU（DDP）:                  16Ψ

┌──────────────────────────────────────────────────────────────────┐
│  Stage 1: 切分优化器状态                                          │
│                                                                    │
│  每 GPU 只负责 1/N 参数的优化器状态（但仍存完整参数和梯度）       │
│  每 GPU: 2Ψ + 2Ψ + 12Ψ/N = (4 + 12/N)Ψ                        │
│                                                                    │
│  LLaMA-7B，N=8:  (4 + 12/8) × 14GB = 4 + 1.5 = 5.5 × 14 =     │
│                   每 GPU 约 77 GB → 节省 31%                     │
│                                                                    │
│  通信代价：反向传播后需要 Reduce-Scatter 梯度给负责的 GPU       │
│           优化器更新后需要 All-Gather 收集更新的参数               │
├──────────────────────────────────────────────────────────────────┤
│  Stage 2: + 切分梯度                                              │
│                                                                    │
│  每 GPU 只保留自己负责那 1/N 参数的梯度                          │
│  每 GPU: 2Ψ + 2Ψ/N + 12Ψ/N = (2 + 14/N)Ψ                      │
│                                                                    │
│  LLaMA-7B，N=8:  (2 + 14/8) × 14GB = 3.75 × 14 =              │
│                   每 GPU 约 52.5 GB → 节省 53%                   │
│                                                                    │
│  通信代价：与 Stage 1 相同（梯度计算完即可丢弃非负责部分）       │
├──────────────────────────────────────────────────────────────────┤
│  Stage 3: + 切分模型参数                                          │
│                                                                    │
│  参数、梯度、优化器全部切分！                                      │
│  每 GPU: 2Ψ/N + 2Ψ/N + 12Ψ/N = 16Ψ/N                          │
│                                                                    │
│  LLaMA-7B，N=8:  16/8 × 14GB =                                  │
│                   每 GPU 仅 28 GB → 节省 75%                     │
│  LLaMA-7B，N=64: 每 GPU 仅 3.5 GB → 节省 96.9%                 │
│                                                                    │
│  通信代价：前向和反向都需要 All-Gather 收集完整参数               │
│           每一层计算前临时收集，计算后丢弃                          │
└──────────────────────────────────────────────────────────────────┘
```

### Stage 3 前向传播的通信过程

```
假设模型有 L 层，4 个 GPU

前向传播 Layer i 时：
  1. All-Gather: 从 4 个 GPU 收集 Layer i 的完整参数
     GPU 0 持有 Wᵢ[0:25%], GPU 1 持有 Wᵢ[25:50%], ...
     → 每个 GPU 临时拥有完整 Wᵢ

  2. 计算: output = LayerI(input, Wᵢ)

  3. 丢弃: 释放其他 GPU 的参数分片（只保留自己的 1/N）

  4. 继续下一层...

反向传播类似，只是方向相反，且需要额外 Reduce-Scatter 梯度

┌─────────────────────────────────────────────────────────────┐
│  时间线（前向）:                                             │
│                                                              │
│  Layer 0     Layer 1     Layer 2     Layer L                │
│  ┌─┬──┬─┐  ┌─┬──┬─┐  ┌─┬──┬─┐         ┌─┬──┬─┐          │
│  │G│计│丢│  │G│计│丢│  │G│计│丢│  ...   │G│计│丢│          │
│  │a│算│弃│  │a│算│弃│  │a│算│弃│         │a│算│弃│          │
│  │t│  │  │  │t│  │  │  │t│  │  │         │t│  │  │          │
│  │h│  │  │  │h│  │  │  │h│  │  │         │h│  │  │          │
│  └─┴──┴─┘  └─┴──┴─┘  └─┴──┴─┘         └─┴──┴─┘          │
│   ↑                                                         │
│   All-Gather 收集完整参数                                    │
│                                                              │
│  通信量分析：                                                │
│  前向 L 层: L × Ψ_layer × (N-1)/N ≈ Ψ_total               │
│  反向 L 层: L × Ψ_layer × (N-1)/N + Reduce-Scatter        │
│  总通信 ≈ 3Ψ_total（是 DDP 的 1.5 倍）                     │
│                                                              │
│  结论：Stage 3 用 1.5 倍通信换取 N 倍显存节省               │
└─────────────────────────────────────────────────────────────┘
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

**关键参数解读**：
- `overlap_comm`: 通信与计算重叠，类似 DDP 的桶化思想
- `reduce_bucket_size`: 通信桶大小，5e8 ≈ 500M 参数 ≈ 1GB FP16
- `stage3_prefetch_bucket_size`: 预取下一层参数，隐藏通信延迟
- `stage3_param_persistence_threshold`: 小于此大小的参数常驻内存不切分（如 LayerNorm）
- `offload_optimizer/param`: 将优化器状态/参数卸载到 CPU，用 PCIe 带宽换 GPU 显存

### DeepSpeed ZeRO-Offload 与 ZeRO-Infinity

```
ZeRO-Offload（Stage 2 + CPU）:
┌──────────┐     PCIe      ┌──────────┐
│   GPU    │ ←──────────→  │   CPU    │
│  参数    │   带宽 ~32GB/s │  优化器  │
│  梯度    │               │  状态    │
│  前/反向 │               │  参数更新│
└──────────┘               └──────────┘
  计算在 GPU                  Adam 更新在 CPU

ZeRO-Infinity（Stage 3 + CPU + NVMe）:
┌──────┐   PCIe   ┌──────┐   NVMe   ┌──────┐
│ GPU  │ ←──────→ │ CPU  │ ←──────→ │ SSD  │
│ 计算 │  32GB/s  │ 缓冲 │  ~5GB/s  │ 存储 │
│ 层   │          │ 层   │          │ 层   │
└──────┘          └──────┘          └──────┘

理论上：单机 8 卡 A100 + 1TB CPU 内存 + NVMe
可以训练万亿参数模型！代价是训练速度显著降低
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

### FSDP 的本质：PyTorch 原生的 ZeRO-3

FSDP (Fully Sharded Data Parallel) 是 PyTorch 对 ZeRO-3 的原生实现。

**类比**：ZeRO 是第三方改装店的方案，FSDP 是官方原厂方案——功能类似，但与 PyTorch 生态（AMP、编译器、Profiler）集成更紧密。

### FSDP 的分片单元：Flat Parameter

```
FSDP 不是按"一个参数张量"切分，而是：
1. 将一组参数（如一个 Transformer 层的所有参数）展平为一维张量
2. 均匀切分到 N 个 GPU

TransformerBlock 的参数:
  Q_weight [4096×4096]  ─┐
  K_weight [4096×4096]   │  展平
  V_weight [4096×4096]   ├─────→  [flat_param: 共 ~67M 个数] 
  O_weight [4096×4096]   │           │
  MLP_up   [4096×11008]  │     ┌─────┼─────┬─────┐
  MLP_down [11008×4096] ─┘     ▼     ▼     ▼     ▼
                             GPU0   GPU1   GPU2   GPU3
                             ~17M   ~17M   ~17M   ~17M

好处：
- 参数对齐，没有碎片化
- 通信粒度更大，效率更高
- 内存管理更简单（一个连续块 vs 多个小张量）
```

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

# 训练循环与 DDP 完全相同
for batch in dataloader:
    loss = model(batch).loss
    loss.backward()
    optimizer.step()
    optimizer.zero_grad()
```

### FSDP 分片策略对照表

| 策略 | 等价 ZeRO | 显存节省 | 通信量 | 适用场景 |
|------|-----------|----------|--------|----------|
| `NO_SHARD` | DDP | 无 | 2Ψ | 小模型基线 |
| `SHARD_GRAD_OP` | Stage 2 | 中等 | 2Ψ | 显存紧张但需要高性能 |
| `FULL_SHARD` | Stage 3 | 最大 | 3Ψ | 大模型必选 |
| `HYBRID_SHARD` | 机内 S3 + 机间 S1 | 平衡 | 介于两者 | 多机训练的最佳平衡 |

**HYBRID_SHARD 详解**：

```
8 机 × 8 卡 = 64 GPU

FULL_SHARD: 64 GPU 间全切分
  通信：需要跨机 All-Gather，受限于机间带宽（通常 100-400 Gbps）

HYBRID_SHARD: 
  机内 8 卡: FULL_SHARD（NVLink 900 GB/s，快！）
  机间 8 机: NO_SHARD（只做 DDP 梯度同步）
  
  ┌─── 机器 0 ───┐  ┌─── 机器 1 ───┐
  │ GPU0 GPU1 ...│  │ GPU0 GPU1 ...│
  │  FULL_SHARD  │──│  FULL_SHARD  │  机间: DDP AllReduce
  │  (机内切分)   │  │  (机内切分)   │  (只传梯度，不传参数)
  └──────────────┘  └──────────────┘

  显存节省 8 倍（不是 64 倍），但通信效率高得多
```

### FSDP vs ZeRO 详细对比

| 特性 | ZeRO (DeepSpeed) | FSDP (PyTorch) |
|------|------------------|----------------|
| 实现方式 | 独立库 | PyTorch 原生 |
| Stage 1/2/3 | ✅ | ✅ |
| CPU Offload | ✅ (+ NVMe) | ✅ (仅 CPU) |
| 混合精度 | 自己管理 | 无缝对接 torch.amp |
| torch.compile | 不支持 | ✅ 支持 |
| Profiler 集成 | 有限 | 完整 |
| 社区支持 | 微软 DeepSpeed 团队 | PyTorch 核心团队 |
| 成熟度 | 更成熟，坑已踩过 | 较新，快速迭代中 |
| 配置方式 | JSON 配置文件 | Python API |

---

## 选择建议

### 决策树

```
你的模型有多大？
│
├── < 10B 参数（单卡能放下）
│   └── 用 DDP
│       理由：最简单，性能最好（无额外通信开销）
│
├── 10B ~ 100B 参数
│   ├── 追求 PyTorch 原生体验？
│   │   └── 用 FSDP (FULL_SHARD)
│   │       搭配 HYBRID_SHARD 做多机训练
│   │
│   └── 需要 NVMe Offload 或更多调优选项？
│       └── 用 DeepSpeed ZeRO Stage 3
│
├── > 100B 参数
│   └── 纯数据并行不够，需要结合模型并行
│       参考 3D 并行方案
│
└── GPU 显存极度不足？
    └── ZeRO-Infinity (Stage 3 + CPU + NVMe Offload)
        代价：训练速度下降 2-5 倍
```

### 性能参考（LLaMA-7B，8×A100-80GB）

| 方案 | 每 GPU 显存 | 训练吞吐 (tokens/s) | 备注 |
|------|-------------|---------------------|------|
| DDP | ~112 GB (OOM) | — | 放不下 |
| ZeRO Stage 1 | ~77 GB | ~3200 | 刚好放下 |
| ZeRO Stage 2 | ~52 GB | ~3000 | 余量充足 |
| ZeRO Stage 3 | ~28 GB | ~2500 | 可开大 batch |
| FSDP FULL_SHARD | ~28 GB | ~2600 | 与 Stage 3 相当 |
| ZeRO-Offload | ~20 GB | ~1500 | CPU 参与计算 |

> 注：吞吐数据为估算参考值，实际取决于硬件配置、batch size、序列长度等。

---

## 小结

- **数据并行**是分布式训练最基础的策略，数学上等价于大 batch 训练
- **DDP** 通过梯度桶化实现计算-通信重叠，是小模型的最佳选择
- **ZeRO** 三阶段递进式切分，用通信换显存，突破单卡容量限制
- **FSDP** 是 PyTorch 原生的 ZeRO-3，与生态集成更好
- **关键取舍**：Stage 越高 → 显存越省 → 通信越多 → 吞吐略降

---

*下一篇：[04-model-parallelism.md](04-model-parallelism.md) - 模型并行详解*

---

## 参考资料与引用

1. **Li, S., et al. (2020).** *PyTorch Distributed: Experiences on Accelerating Data Parallel Training.* VLDB 2020.  
   https://arxiv.org/abs/2006.15704

2. **Rajbhandari, S., et al. (2020).** *ZeRO: Memory Optimizations Toward Training Trillion Parameter Models.* — ZeRO-DP  
   https://arxiv.org/abs/1910.02054

3. **Goyal, P., et al. (2017).** *Accurate, Large Minibatch SGD: Training ImageNet in 1 Hour.* — 大 batch 数据并行训练  
   https://arxiv.org/abs/1706.02677

4. **PyTorch Documentation.** *DistributedDataParallel.*  
   https://pytorch.org/docs/stable/generated/torch.nn.parallel.DistributedDataParallel.html

5. **DeepSpeed Documentation.** *ZeRO Optimization Stages.*  
   https://www.deepspeed.ai/tutorials/zero/
