# 分布式训练详解

> 大模型无法在单卡上训练，分布式训练是唯一出路。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [02-distributed-training/](./02-distributed-training/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | 为什么需要分布式训练 | [01-why-distributed.md](./02-distributed-training/01-why-distributed.md) |
> | 并行策略总览 | [02-parallelism-overview.md](./02-distributed-training/02-parallelism-overview.md) |
> | 数据并行详解 | [03-data-parallelism.md](./02-distributed-training/03-data-parallelism.md) |
> | 模型并行详解 | [04-model-parallelism.md](./02-distributed-training/04-model-parallelism.md) |
> | 流水线并行详解 | [05-pipeline-parallelism.md](./02-distributed-training/05-pipeline-parallelism.md) |
> | 3D 并行实践 | [06-3d-parallelism.md](./02-distributed-training/06-3d-parallelism.md) |
> | 训练框架对比 | [07-training-frameworks.md](./02-distributed-training/07-training-frameworks.md) |
> | 通信优化 | [08-communication-optimization.md](./02-distributed-training/08-communication-optimization.md) |
> | Checkpoint 与容错 | [09-checkpoint-fault-tolerance.md](./02-distributed-training/09-checkpoint-fault-tolerance.md) |
> | 序列并行详解 | [10-sequence-parallelism.md](./02-distributed-training/10-sequence-parallelism.md) |
> | 专家并行与 MoE | [11-expert-parallelism-moe.md](./02-distributed-training/11-expert-parallelism-moe.md) |
> | 混合精度训练 | [12-mixed-precision-training.md](./02-distributed-training/12-mixed-precision-training.md) |

---

## 目录

- [为什么需要分布式训练](#为什么需要分布式训练)
- [并行策略总览](#并行策略总览)
- [数据并行](#数据并行)
- [模型并行](#模型并行)
- [3D 并行](#3d-并行)
- [训练框架对比](#训练框架对比)
- [通信优化](#通信优化)
- [Checkpoint 与容错](#checkpoint-与容错)
- [实战练习](#实战练习)

---

## 为什么需要分布式训练

### 单卡训练的瓶颈

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    大模型训练的三大瓶颈                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. 显存瓶颈 (Memory)                                                   │
│     ├── 模型参数: 7B FP16 = 14GB                                        │
│     ├── 梯度: 14GB                                                      │
│     ├── 优化器状态 (AdamW): 56GB                                        │
│     ├── 激活值: 取决于 batch size                                       │
│     └── 总计: 7B 模型训练需要 ~100GB+                                   │
│         (单卡 A100 80GB 装不下！)                                       │
│                                                                         │
│  2. 计算瓶颈 (Compute)                                                  │
│     ├── GPT-3 175B 训练: ~3.14×10²³ FLOPs                              │
│     ├── 单 A100 (312 TFLOPS FP16): 需要 1,000+ 年                       │
│     └── 1024 GPU 并行: ~1个月                                           │
│                                                                         │
│  3. 数据瓶颈 (Data)                                                     │
│     ├── 大规模数据集读取                                                 │
│     └── 预处理速度跟不上 GPU 消费                                        │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 解决方案：分而治之

```
                    ┌─────────────────────┐
                    │   分布式训练策略     │
                    └──────────┬──────────┘
                               │
         ┌─────────────────────┼─────────────────────┐
         │                     │                     │
         ▼                     ▼                     ▼
    ┌─────────┐          ┌─────────┐          ┌─────────┐
    │数据并行  │          │模型并行  │          │流水线并行│
    │  (DP)   │          │  (MP)   │          │  (PP)   │
    └────┬────┘          └────┬────┘          └────┬────┘
         │                     │                     │
         ▼                     ▼                     ▼
    复制模型              切分模型               切分层
    切分数据              每卡存部分             按阶段执行
```

---

## 并行策略总览

### 四种主要并行方式

| 并行方式 | 切分维度 | 解决问题 | 通信开销 |
|----------|----------|----------|----------|
| **数据并行 (DP)** | Batch 维度 | 加速计算 | AllReduce 梯度 |
| **张量并行 (TP)** | 隐藏层维度 | 显存不足 | 每层 AllReduce |
| **流水线并行 (PP)** | 层维度 | 显存不足 | 相邻阶段传输 |
| **序列并行 (SP)** | 序列维度 | 长序列显存 | AllGather/ReduceScatter |

### 组合策略（3D/4D 并行）

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        3D 并行示意图                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   假设 64 GPU，配置: DP=8, TP=4, PP=2                                   │
│                                                                         │
│   数据并行 (DP=8): 8 个数据并行组，每组处理不同数据                        │
│   ┌──────────────────────────────────────────────────────────────┐     │
│   │ Group 0 │ Group 1 │ Group 2 │ ... │ Group 7 │                │     │
│   └────┬────┴────┬────┴────┬────┴─────┴────┬────┘                │     │
│        │         │         │              │                       │     │
│        ▼         ▼         ▼              ▼                       │     │
│   流水线并行 (PP=2): 每个 DP 组内分 2 个流水线阶段                        │
│   ┌────────────────────────────────────────────┐                       │
│   │    Stage 0    │    Stage 1    │                                    │
│   │  (Layers 0-N) │  (Layers N-M) │                                    │
│   └───────┬───────┴───────┬───────┘                                    │
│           │               │                                            │
│           ▼               ▼                                            │
│   张量并行 (TP=4): 每个 Stage 内 4 GPU 切分每层                          │
│   ┌─────────────────────────────────┐                                  │
│   │ GPU0 │ GPU1 │ GPU2 │ GPU3 │                                        │
│   │(1/4) │(1/4) │(1/4) │(1/4) │                                        │
│   └─────────────────────────────────┘                                  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 数据并行

### 基本原理

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        数据并行 (Data Parallel)                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   数据被切分，模型被复制                                                  │
│                                                                         │
│   ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐         │
│   │  GPU 0  │     │  GPU 1  │     │  GPU 2  │     │  GPU 3  │         │
│   │ Model   │     │ Model   │     │ Model   │     │ Model   │         │
│   │ (copy)  │     │ (copy)  │     │ (copy)  │     │ (copy)  │         │
│   └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘         │
│        │               │               │               │               │
│   ┌────▼────┐     ┌────▼────┐     ┌────▼────┐     ┌────▼────┐         │
│   │ Batch 0 │     │ Batch 1 │     │ Batch 2 │     │ Batch 3 │         │
│   └────┬────┘     └────┬────┘     └────┬────┘     └────┬────┘         │
│        │               │               │               │               │
│        └───────────────┴───────────────┴───────────────┘               │
│                               │                                         │
│                         AllReduce                                       │
│                      (平均梯度同步)                                      │
│                               │                                         │
│                               ▼                                         │
│                    所有 GPU 更新相同参数                                  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### PyTorch DDP（DistributedDataParallel）

```python
import torch
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP

def setup(rank, world_size):
    dist.init_process_group("nccl", rank=rank, world_size=world_size)
    torch.cuda.set_device(rank)

def train(rank, world_size):
    setup(rank, world_size)
    
    # 创建模型并包装为 DDP
    model = MyModel().to(rank)
    model = DDP(model, device_ids=[rank])
    
    # 使用 DistributedSampler 确保数据不重叠
    train_sampler = torch.utils.data.distributed.DistributedSampler(
        dataset, num_replicas=world_size, rank=rank
    )
    dataloader = DataLoader(dataset, sampler=train_sampler, batch_size=32)
    
    optimizer = torch.optim.AdamW(model.parameters(), lr=1e-4)
    
    for epoch in range(epochs):
        train_sampler.set_epoch(epoch)  # 确保每个 epoch 数据顺序不同
        for batch in dataloader:
            optimizer.zero_grad()
            loss = model(batch).loss
            loss.backward()  # DDP 自动同步梯度
            optimizer.step()
    
    dist.destroy_process_group()

# 启动: torchrun --nproc_per_node=4 train.py
```

### ZeRO 优化器（DeepSpeed）

ZeRO（Zero Redundancy Optimizer）通过切分优化器状态来节省显存：

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          ZeRO 三阶段                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   假设 4 GPU，模型参数 M，优化器状态 O (AdamW: M×8)，梯度 G (M×2)         │
│                                                                         │
│   标准 DDP:                                                             │
│   每 GPU 存储: M + G + O = M×12                                         │
│   总存储: 4 × M×12 = M×48 (冗余!)                                       │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │              ZeRO Stage 1: 切分优化器状态                        │   │
│   │                                                                 │   │
│   │   GPU 0      GPU 1      GPU 2      GPU 3                       │   │
│   │   ┌───┐      ┌───┐      ┌───┐      ┌───┐                       │   │
│   │   │ M │      │ M │      │ M │      │ M │  ← 模型完整复制        │   │
│   │   │ G │      │ G │      │ G │      │ G │  ← 梯度完整复制        │   │
│   │   │O/4│      │O/4│      │O/4│      │O/4│  ← 优化器 1/4         │   │
│   │   └───┘      └───┘      └───┘      └───┘                       │   │
│   │   每 GPU: M + G + O/4 = M×4.5 (vs M×12)                        │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │              ZeRO Stage 2: + 切分梯度                            │   │
│   │                                                                 │   │
│   │   GPU 0      GPU 1      GPU 2      GPU 3                       │   │
│   │   ┌───┐      ┌───┐      ┌───┐      ┌───┐                       │   │
│   │   │ M │      │ M │      │ M │      │ M │  ← 模型完整复制        │   │
│   │   │G/4│      │G/4│      │G/4│      │G/4│  ← 梯度 1/4           │   │
│   │   │O/4│      │O/4│      │O/4│      │O/4│  ← 优化器 1/4         │   │
│   │   └───┘      └───┘      └───┘      └───┘                       │   │
│   │   每 GPU: M + G/4 + O/4 = M×3 (vs M×12)                        │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │              ZeRO Stage 3: + 切分模型参数                        │   │
│   │                                                                 │   │
│   │   GPU 0      GPU 1      GPU 2      GPU 3                       │   │
│   │   ┌───┐      ┌───┐      ┌───┐      ┌───┐                       │   │
│   │   │M/4│      │M/4│      │M/4│      │M/4│  ← 模型 1/4           │   │
│   │   │G/4│      │G/4│      │G/4│      │G/4│  ← 梯度 1/4           │   │
│   │   │O/4│      │O/4│      │O/4│      │O/4│  ← 优化器 1/4         │   │
│   │   └───┘      └───┘      └───┘      └───┘                       │   │
│   │   每 GPU: M/4 + G/4 + O/4 = M×3/4 (vs M×12) 🎉                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   代价: 前向/反向时需要 AllGather 收集完整参数                            │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### FSDP（Fully Sharded Data Parallel）

PyTorch 原生的 ZeRO-3 实现：

```python
from torch.distributed.fsdp import FullyShardedDataParallel as FSDP
from torch.distributed.fsdp import ShardingStrategy

model = MyModel()

# 配置 FSDP
fsdp_model = FSDP(
    model,
    sharding_strategy=ShardingStrategy.FULL_SHARD,  # 等价 ZeRO-3
    # ShardingStrategy.SHARD_GRAD_OP,  # 等价 ZeRO-2
    # ShardingStrategy.NO_SHARD,  # 等价 DDP
    auto_wrap_policy=transformer_auto_wrap_policy,
    mixed_precision=MixedPrecision(
        param_dtype=torch.bfloat16,
        reduce_dtype=torch.bfloat16,
        buffer_dtype=torch.bfloat16,
    ),
)

# 训练循环与 DDP 相同
for batch in dataloader:
    loss = fsdp_model(batch).loss
    loss.backward()
    optimizer.step()
```

---

## 模型并行

### 张量并行（Tensor Parallelism）

切分每一层的计算，适合 Transformer 的大型矩阵运算：

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    张量并行：切分 Linear 层                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   原始 Linear: Y = XW + b                                               │
│   X: [batch, seq, hidden]                                               │
│       batch  = 一次喂入多少条样本 (如 4 条句子)                          │
│       seq    = 每条样本的 token 数 (如 2048 个 token)                    │
│                由模型最大上下文长度决定 (如 LLaMA-2=4096, GPT-4=128K)   │
│                seq 越长 → 注意力显存 ∝ seq² (翻倍则显存×4)             │
│                这也是长上下文训练的核心难点                               │
│       hidden = 每个 token 的特征维度 (如 LLaMA-7B 是 4096)              │
│   W: [hidden, output]                                                   │
│                                                                         │
│   列切分 (Column Parallel):                                             │
│   ┌─────────────────────────────────────────────────────────────┐       │
│   │                                                             │       │
│   │      W                    W₀      W₁      W₂      W₃       │       │
│   │   ┌─────┐              ┌────┐  ┌────┐  ┌────┐  ┌────┐      │       │
│   │   │     │   切分为     │    │  │    │  │    │  │    │      │       │
│   │   │     │   ─────→    │    │  │    │  │    │  │    │      │       │
│   │   │     │              │    │  │    │  │    │  │    │      │       │
│   │   └─────┘              └────┘  └────┘  └────┘  └────┘      │       │
│   │                        GPU 0   GPU 1   GPU 2   GPU 3       │       │
│   │                                                             │       │
│   │   计算: Y_i = X @ W_i  (每 GPU 独立计算)                     │       │
│   │   结果: [Y₀, Y₁, Y₂, Y₃] 拼接得到完整 Y                      │       │
│   │                                                             │       │
│   └─────────────────────────────────────────────────────────────┘       │
│                                                                         │
│   行切分 (Row Parallel):                                                │
│   ┌─────────────────────────────────────────────────────────────┐       │
│   │                                                             │       │
│   │      W                   W₀       W₁       W₂       W₃     │       │
│   │   ┌─────┐              ┌────┐   ┌────┐   ┌────┐   ┌────┐   │       │
│   │   │     │   切分为     │    │   │    │   │    │   │    │   │       │
│   │   │     │   ─────→    ├────┤   ├────┤   ├────┤   ├────┤   │       │
│   │   │     │              │    │   │    │   │    │   │    │   │       │
│   │   └─────┘              └────┘   └────┘   └────┘   └────┘   │       │
│   │                        GPU 0    GPU 1    GPU 2    GPU 3    │       │
│   │                                                             │       │
│   │   需要切分输入 X: X_i @ W_i                                  │       │
│   │   结果: AllReduce(Y₀ + Y₁ + Y₂ + Y₃) 得到完整 Y              │       │
│   │                                                             │       │
│   └─────────────────────────────────────────────────────────────┘       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Transformer 中的张量并行

```
┌─────────────────────────────────────────────────────────────────────────┐
│                  Transformer 层的张量并行                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   MLP Block (2 个 Linear):                                              │
│                                                                         │
│       Input X                                                           │
│          │                                                              │
│          ▼                                                              │
│   ┌──────────────┐                                                      │
│   │  Linear 1    │  ← Column Parallel: 切分 output 维度                 │
│   │ (hidden→4h)  │     无需通信，每 GPU 计算部分输出                      │
│   └──────┬───────┘                                                      │
│          │                                                              │
│          ▼                                                              │
│   ┌──────────────┐                                                      │
│   │    GeLU      │  ← 每 GPU 独立计算                                   │
│   └──────┬───────┘                                                      │
│          │                                                              │
│          ▼                                                              │
│   ┌──────────────┐                                                      │
│   │  Linear 2    │  ← Row Parallel: 切分 input 维度                     │
│   │ (4h→hidden)  │     需要 AllReduce 合并结果                          │
│   └──────┬───────┘                                                      │
│          │                                                              │
│          ▼                                                              │
│       Output                                                            │
│                                                                         │
│   Self-Attention:                                                       │
│   - Q, K, V projection: Column Parallel (切分 head 维度)                │
│   - Attention 计算: 每 GPU 计算部分 head                                 │
│   - Output projection: Row Parallel + AllReduce                         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

#### MLP Block 为什么这样切？用 LLaMA-7B 的数字走一遍

```
以 LLaMA-7B 为例: hidden=4096, 4h=16384, 4 块 GPU

═══════════════════════════════════════════════════════════════════════════
  MLP 原始结构 (单卡):
═══════════════════════════════════════════════════════════════════════════

    Input X: [batch, seq, 4096]
        │
        ▼
    Linear 1: W₁ [4096 × 16384]   ← "升维"，把 4096 维映射到 16384 维
        │      参数量: 4096 × 16384 = 6700万
        ▼
    GeLU 激活函数                   ← 逐元素操作，不涉及参数
        │
        ▼
    Linear 2: W₂ [16384 × 4096]   ← "降维"，把 16384 维映射回 4096 维
        │      参数量: 16384 × 4096 = 6700万
        ▼
    Output: [batch, seq, 4096]

    MLP 总参数: 1.34 亿 (× 32 层 = 整个模型 MLP 部分约 43 亿参数)

═══════════════════════════════════════════════════════════════════════════
  张量并行后 (4 GPU):
═══════════════════════════════════════════════════════════════════════════

  ────── Linear 1: Column Parallel (按列切) ──────

    W₁ [4096 × 16384] 按列切成 4 份:
    GPU 0: W₁₀ [4096 × 4096]    (负责输出维度的 1/4)
    GPU 1: W₁₁ [4096 × 4096]
    GPU 2: W₁₂ [4096 × 4096]
    GPU 3: W₁₃ [4096 × 4096]

    每块 GPU 的计算:
    GPU 0: Y₀ = X @ W₁₀  →  [batch, seq, 4096]  (输出是完整的 1/4)
    GPU 1: Y₁ = X @ W₁₁  →  [batch, seq, 4096]
    ...

    关键: 每块 GPU 都拿到完整的 X，乘以自己那一份 W
          输出的 4096 维是完整 16384 维的 1/4
          → 不需要任何通信!

  ────── GeLU: 独立计算 ──────

    GeLU = Gaussian Error Linear Unit (高斯误差线性单元)
    公式: GeLU(x) = x · Φ(x)，其中 Φ(x) 是标准正态分布的累积分布函数
    直觉: "平滑版 ReLU" — 小值被柔和抑制，大值近似保留

    模型层面的作用:
    GeLU 位于两个 Linear 层之间，引入非线性。
    没有它，两个线性层堆叠等价于一个线性层 (矩阵 × 矩阵 = 矩阵)，
    模型就无法学习复杂模式。

    张量并行层面的作用:
    每块 GPU 对自己的 Y_i 做 GeLU，互不干扰
    GeLU(Y₀), GeLU(Y₁), GeLU(Y₂), GeLU(Y₃)

    为什么 Column Parallel 后可以直接做 GeLU？
    因为 GeLU 是逐元素 (element-wise) 操作: GeLU([a, b]) = [GeLU(a), GeLU(b)]
    → 拆开算和拼起来算结果一样!
    → 这是 Column Parallel 放在第一个 Linear 的重要原因
    → 零通信开销，是 Megatron-LM 张量并行高效工作的关键设计点

  ────── Linear 2: Row Parallel (按行切) ──────

    W₂ [16384 × 4096] 按行切成 4 份:
    GPU 0: W₂₀ [4096 × 4096]    (负责输入维度的 1/4)
    GPU 1: W₂₁ [4096 × 4096]
    GPU 2: W₂₂ [4096 × 4096]
    GPU 3: W₂₃ [4096 × 4096]

    每块 GPU 的计算:
    GPU 0: Z₀ = GeLU(Y₀) @ W₂₀  →  [batch, seq, 4096]
    GPU 1: Z₁ = GeLU(Y₁) @ W₂₁  →  [batch, seq, 4096]
    ...

    数学原理: 原始计算是 Z = [GeLU(Y₀)|GeLU(Y₁)|GeLU(Y₂)|GeLU(Y₃)] @ W₂
    按行切分后: Z = GeLU(Y₀)@W₂₀ + GeLU(Y₁)@W₂₁ + GeLU(Y₂)@W₂₂ + GeLU(Y₃)@W₂₃
    即: Z = Z₀ + Z₁ + Z₂ + Z₃
    → 需要 AllReduce(SUM) 把 4 块 GPU 的结果加起来!

  ────── 通信分析 ──────

    整个 MLP Block 只需要 1 次 AllReduce:
    通信数据量 = [batch × seq × 4096] × 2 bytes (FP16)
    比如 batch=4, seq=2048: 4 × 2048 × 4096 × 2 = 64 MB
    → 相比计算量来说，通信量很小!
```

#### Self-Attention 的张量并行

```
═══════════════════════════════════════════════════════════════════════════
  LLaMA-7B: hidden=4096, 32 个注意力头, 每个头 128 维
  4 块 GPU → 每块 GPU 负责 8 个头
═══════════════════════════════════════════════════════════════════════════

    Input X: [batch, seq, 4096]
        │
        │  Q/K/V Projection (Column Parallel — 按 head 维度切)
        │  ──────────────────────────────────────────────────
        ▼
    原始 W_Q: [4096 × 4096]  (32个头 × 128维/头)
    切分后:
    GPU 0: W_Q₀ [4096 × 1024]  → 算 8 个头的 Q     (头 0-7)
    GPU 1: W_Q₁ [4096 × 1024]  → 算 8 个头的 Q     (头 8-15)
    GPU 2: W_Q₂ [4096 × 1024]  → 算 8 个头的 Q     (头 16-23)
    GPU 3: W_Q₃ [4096 × 1024]  → 算 8 个头的 Q     (头 24-31)
    K, V 同理切分

        │
        │  Attention 计算 (每 GPU 独立)
        │  ────────────────────────────
        ▼
    GPU 0: 用自己的 8 个头的 Q₀, K₀, V₀ 做注意力
           Attention(Q₀, K₀, V₀) → [batch, seq, 1024]
    GPU 1-3: 同理

    为什么可以按 head 切？
    → 多头注意力本身就是各 head 独立计算，最后拼接
    → 天然适合并行! 每个 GPU 算几个 head，完全不影响结果

        │
        │  Output Projection (Row Parallel + AllReduce)
        │  ──────────────────────────────────────────────
        ▼
    W_O: [4096 × 4096] 按行切成 4 份
    GPU 0: Attn₀ @ W_O₀ → Z₀ [batch, seq, 4096]
    GPU 1: Attn₁ @ W_O₁ → Z₁
    ...
    AllReduce(Z₀ + Z₁ + Z₂ + Z₃) → 完整输出

═══════════════════════════════════════════════════════════════════════════
  整个 Attention Block 也只需要 1 次 AllReduce!
═══════════════════════════════════════════════════════════════════════════

  总结: 一个 Transformer 层 = MLP (1次AllReduce) + Attention (1次AllReduce)
  → 每层只需 2 次 AllReduce，通信开销很小
  → 这就是 Megatron-LM 张量并行的核心设计
```

### 流水线并行（Pipeline Parallelism）

按层切分模型，不同阶段处理不同的 micro-batch：

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       流水线并行原理                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   模型 24 层，4 GPU，每 GPU 6 层                                         │
│                                                                         │
│   GPU 0: Layers 0-5   (Stage 0)                                        │
│   GPU 1: Layers 6-11  (Stage 1)                                        │
│   GPU 2: Layers 12-17 (Stage 2)                                        │
│   GPU 3: Layers 18-23 (Stage 3)                                        │
│                                                                         │
│   朴素流水线 (大量气泡):                                                 │
│                                                                         │
│   Time →                                                                │
│   GPU 0: │ F0 │ F1 │ F2 │ F3 │    │    │    │    │ B3 │ B2 │ B1 │ B0 │ │
│   GPU 1: │    │ F0 │ F1 │ F2 │ F3 │    │    │ B3 │ B2 │ B1 │ B0 │    │ │
│   GPU 2: │    │    │ F0 │ F1 │ F2 │ F3 │ B3 │ B2 │ B1 │ B0 │    │    │ │
│   GPU 3: │    │    │    │ F0 │ F1 │ F2 │ F3 │ B2 │ B1 │ B0 │    │    │ │
│          └─────────────────────────────────────────────────────────────┘│
│                        ↑ 气泡（空闲） ↑                                   │
│                                                                         │
│   GPipe (micro-batch):                                                  │
│   将一个 batch 切分为多个 micro-batch，流水执行                           │
│                                                                         │
│   1F1B (Interleaved):                                                   │
│   前向和反向交替执行，最小化气泡                                          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 3D 并行

### Megatron-LM 的 3D 并行

```python
# Megatron-LM 配置示例
# 假设 64 GPU 训练 GPT-3 175B

# 并行配置
tensor_model_parallel_size = 8    # TP: 每层切分到 8 GPU
pipeline_model_parallel_size = 8  # PP: 模型分 8 个阶段
data_parallel_size = 1            # DP: 64 / 8 / 8 = 1

# 启动命令
"""
python -m torch.distributed.launch \
    --nproc_per_node 8 \
    --nnodes 8 \
    pretrain_gpt.py \
    --tensor-model-parallel-size 8 \
    --pipeline-model-parallel-size 8 \
    --num-layers 96 \
    --hidden-size 12288 \
    --num-attention-heads 96 \
    --micro-batch-size 1 \
    --global-batch-size 1536 \
    ...
"""
```

### DeepSpeed 3D 并行配置

```json
{
    "train_batch_size": 1024,
    "train_micro_batch_size_per_gpu": 4,
    "gradient_accumulation_steps": 64,
    
    "zero_optimization": {
        "stage": 3,
        "offload_optimizer": {
            "device": "cpu"
        },
        "offload_param": {
            "device": "cpu"
        }
    },
    
    "fp16": {
        "enabled": true,
        "loss_scale_window": 100
    },
    
    "pipeline": {
        "stages": 4,
        "partition_method": "uniform"
    },
    
    "tensor_parallel": {
        "tp_size": 4
    }
}
```

---

## 训练框架对比

### 主流框架对比

| 特性 | PyTorch DDP/FSDP | DeepSpeed | Megatron-LM | ColossalAI |
|------|------------------|-----------|-------------|------------|
| **开发者** | Meta | Microsoft | NVIDIA | HPC-AI Tech |
| **数据并行** | ✅ | ✅ ZeRO-1/2/3 | ✅ | ✅ |
| **张量并行** | ❌ | ✅ (有限) | ✅ (最成熟) | ✅ |
| **流水线并行** | ❌ | ✅ | ✅ | ✅ |
| **序列并行** | ❌ | ✅ Ulysses | ✅ | ✅ |
| **CPU Offload** | ✅ | ✅ ZeRO-Infinity | ❌ | ✅ |
| **易用性** | 高 | 中 | 低 | 中 |
| **适用场景** | 中小模型 | 大模型训练 | 超大模型 | 通用 |

### 选择建议

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       框架选择决策树                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│                     你的模型规模？                                        │
│                          │                                               │
│         ┌────────────────┼────────────────┐                             │
│         │                │                │                             │
│         ▼                ▼                ▼                             │
│      < 10B           10B-100B          > 100B                           │
│         │                │                │                             │
│         ▼                ▼                ▼                             │
│   PyTorch DDP/FSDP   DeepSpeed      Megatron-LM                         │
│                       ZeRO-3        + DeepSpeed                         │
│                                                                         │
│   具体推荐:                                                              │
│   - 7B 以下，单机多卡: FSDP 或 DDP + 梯度累积                            │
│   - 7B-70B，多机多卡: DeepSpeed ZeRO-3                                  │
│   - 70B+，超大规模: Megatron-LM 3D 并行                                  │
│   - 快速实验: ColossalAI (封装较好)                                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### DeepSpeed 快速上手

```python
import deepspeed
import torch

# 1. 定义模型
model = MyTransformer()

# 2. DeepSpeed 配置
ds_config = {
    "train_batch_size": 64,
    "gradient_accumulation_steps": 4,
    "fp16": {"enabled": True},
    "zero_optimization": {
        "stage": 2,
        "offload_optimizer": {"device": "cpu"},
        "contiguous_gradients": True,
        "overlap_comm": True
    }
}

# 3. 初始化 DeepSpeed
model_engine, optimizer, _, _ = deepspeed.initialize(
    model=model,
    model_parameters=model.parameters(),
    config=ds_config
)

# 4. 训练循环
for batch in dataloader:
    loss = model_engine(batch).loss
    model_engine.backward(loss)
    model_engine.step()

# 启动: deepspeed --num_gpus=8 train.py
```

---

## 通信优化

### 集合通信原语

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       常用集合通信操作                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   AllReduce: 所有节点数据求和后广播给所有节点                             │
│   ┌───┐ ┌───┐ ┌───┐ ┌───┐        ┌───┐ ┌───┐ ┌───┐ ┌───┐             │
│   │ A │ │ B │ │ C │ │ D │   →    │Sum│ │Sum│ │Sum│ │Sum│             │
│   └───┘ └───┘ └───┘ └───┘        └───┘ └───┘ └───┘ └───┘             │
│   用途: DDP 梯度同步                                                    │
│                                                                         │
│   AllGather: 收集所有节点数据，每个节点得到完整数据                        │
│   ┌───┐ ┌───┐ ┌───┐ ┌───┐        ┌────────────────┐ (×4)              │
│   │ A │ │ B │ │ C │ │ D │   →    │ A │ B │ C │ D │                    │
│   └───┘ └───┘ └───┘ └───┘        └────────────────┘                    │
│   用途: ZeRO-3 收集模型参数                                              │
│                                                                         │
│   ReduceScatter: 规约后分散结果到各节点                                   │
│   ┌────────────────┐ (×4)        ┌───┐ ┌───┐ ┌───┐ ┌───┐             │
│   │ A │ B │ C │ D │        →    │ΣA │ │ΣB │ │ΣC │ │ΣD │             │
│   └────────────────┘              └───┘ └───┘ └───┘ └───┘             │
│   用途: ZeRO 梯度切分                                                    │
│                                                                         │
│   Broadcast: 一个节点数据广播给所有节点                                   │
│   用途: 模型初始化同步                                                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### NCCL 优化技巧

```python
# 1. 使用 NCCL 后端（GPU 通信最优）
dist.init_process_group(backend='nccl')

# 2. 启用通信计算重叠
os.environ['NCCL_ASYNC_ERROR_HANDLING'] = '1'

# 3. 调整 NCCL 缓冲区大小
os.environ['NCCL_BUFFSIZE'] = '16777216'  # 16MB

# 4. 使用 bucket 梯度聚合
model = DDP(model, bucket_cap_mb=25)  # 默认 25MB

# 5. 梯度压缩（DeepSpeed）
ds_config = {
    "gradient_compression": {
        "enabled": True,
        "compression_type": "1bit"  # 1-bit Adam
    }
}
```

### 通信与计算重叠

```python
# DeepSpeed 的通信计算重叠
ds_config = {
    "zero_optimization": {
        "stage": 2,
        "overlap_comm": True,  # 关键配置
        "contiguous_gradients": True,
        "reduce_bucket_size": 5e8
    }
}

# FSDP 的重叠配置
from torch.distributed.fsdp import BackwardPrefetch

fsdp_model = FSDP(
    model,
    backward_prefetch=BackwardPrefetch.BACKWARD_PRE,  # 预取参数
    forward_prefetch=True,  # 前向预取
)
```

---

## Checkpoint 与容错

### Checkpoint 策略

```python
# 基本 checkpoint
def save_checkpoint(model, optimizer, epoch, path):
    torch.save({
        'epoch': epoch,
        'model_state_dict': model.state_dict(),
        'optimizer_state_dict': optimizer.state_dict(),
    }, path)

# 大模型分片 checkpoint (FSDP)
from torch.distributed.checkpoint import (
    save_state_dict,
    load_state_dict,
    FileSystemWriter,
    FileSystemReader
)

# 分片保存
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

### 容错训练

```python
# DeepSpeed 弹性训练
ds_config = {
    "elasticity": {
        "enabled": True,
        "max_train_batch_size": 2048,
        "micro_batch_sizes": [4, 8, 16],
        "min_gpus": 32,
        "max_gpus": 128,
        "prefer_larger_batch_size": True
    }
}

# 故障恢复
try:
    model_engine.load_checkpoint(checkpoint_dir)
    print(f"Resumed from {checkpoint_dir}")
except:
    print("Starting fresh training")

# 定期保存
for step, batch in enumerate(dataloader):
    loss = train_step(batch)
    
    if step % save_interval == 0:
        model_engine.save_checkpoint(checkpoint_dir)
```

---

## 实战练习

### 练习 1：单机多卡 DDP 训练

```python
# ddp_training.py
import torch
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP
from torch.utils.data import DataLoader, DistributedSampler
from transformers import AutoModelForCausalLM, AutoTokenizer

def setup():
    dist.init_process_group("nccl")
    rank = dist.get_rank()
    torch.cuda.set_device(rank)
    return rank

def train():
    rank = setup()
    
    # 加载模型
    model = AutoModelForCausalLM.from_pretrained("gpt2")
    model = model.to(rank)
    model = DDP(model, device_ids=[rank])
    
    # 数据加载
    # ... 准备 dataset
    sampler = DistributedSampler(dataset)
    dataloader = DataLoader(dataset, sampler=sampler, batch_size=8)
    
    optimizer = torch.optim.AdamW(model.parameters(), lr=1e-5)
    
    for epoch in range(3):
        sampler.set_epoch(epoch)
        for batch in dataloader:
            batch = {k: v.to(rank) for k, v in batch.items()}
            outputs = model(**batch)
            loss = outputs.loss
            
            optimizer.zero_grad()
            loss.backward()
            optimizer.step()
            
            if rank == 0:
                print(f"Loss: {loss.item():.4f}")
    
    dist.destroy_process_group()

if __name__ == "__main__":
    train()

# 运行: torchrun --nproc_per_node=4 ddp_training.py
```

### 练习 2：DeepSpeed ZeRO-3 训练

```python
# deepspeed_training.py
import deepspeed
from transformers import AutoModelForCausalLM

# ds_config.json
"""
{
    "train_batch_size": 32,
    "train_micro_batch_size_per_gpu": 4,
    "gradient_accumulation_steps": 2,
    "fp16": {"enabled": true},
    "zero_optimization": {
        "stage": 3,
        "offload_optimizer": {"device": "cpu"},
        "offload_param": {"device": "cpu"}
    }
}
"""

model = AutoModelForCausalLM.from_pretrained("meta-llama/Llama-2-7b-hf")

model_engine, optimizer, _, _ = deepspeed.initialize(
    model=model,
    model_parameters=model.parameters(),
    config="ds_config.json"
)

for batch in dataloader:
    outputs = model_engine(batch)
    loss = outputs.loss
    
    model_engine.backward(loss)
    model_engine.step()

# 运行: deepspeed --num_gpus=8 deepspeed_training.py
```

### 练习 3：混合精度训练

```python
from torch.cuda.amp import autocast, GradScaler

scaler = GradScaler()

for batch in dataloader:
    optimizer.zero_grad()
    
    with autocast():  # 自动使用 FP16
        outputs = model(batch)
        loss = outputs.loss
    
    # 缩放 loss 防止 FP16 下溢
    scaler.scale(loss).backward()
    scaler.step(optimizer)
    scaler.update()
```

---

## 延伸阅读

### 必读论文

- [Megatron-LM](https://arxiv.org/abs/1909.08053) - 模型并行经典
- [ZeRO](https://arxiv.org/abs/1910.02054) - 内存优化革命
- [GPipe](https://arxiv.org/abs/1811.06965) - 流水线并行
- [1-bit Adam](https://arxiv.org/abs/2102.02888) - 通信压缩

### 官方文档

- [PyTorch Distributed](https://pytorch.org/docs/stable/distributed.html)
- [DeepSpeed Documentation](https://www.deepspeed.ai/)
- [Megatron-LM GitHub](https://github.com/NVIDIA/Megatron-LM)
- [ColossalAI Documentation](https://colossalai.org/)

### 推荐博客

- [Hugging Face: Model Parallelism](https://huggingface.co/docs/transformers/parallelism)
- [NVIDIA: Large Language Model Training](https://developer.nvidia.com/blog/scaling-language-model-training/)

---

*下一篇：[03-inference-serving.md](03-inference-serving.md) - 模型推理部署详解*
