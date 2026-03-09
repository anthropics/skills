# 训练框架对比

> 选择适合你的分布式训练框架 — 每个框架的设计哲学和核心原理。

## 目录

- [为什么需要训练框架](#为什么需要训练框架)
- [PyTorch DDP / FSDP](#pytorch-ddp--fsdp)
- [DeepSpeed](#deepspeed)
- [Megatron-LM](#megatron-lm)
- [ColossalAI](#colossalai)
- [框架对比总表](#框架对比总表)
- [选择建议](#选择建议)

---

## 为什么需要训练框架

```
  类比: 自己盖房子 vs 用建筑框架

  "裸写"分布式训练:
    自己管通信 (NCCL AllReduce)
    自己管显存 (梯度分片)
    自己管调度 (流水线 micro-batch)
    → 像自己和水泥、砌砖、接水电 — 能盖但极其痛苦

  训练框架 = 建筑公司:
    PyTorch DDP = 简易工具箱 (适合小装修)
    DeepSpeed  = 专业建筑队 (能盖大楼)
    Megatron-LM = 摩天大楼施工队 (超大工程)
    ColossalAI = 精装修公司 (省心但可能不如自建灵活)
```

---

## PyTorch DDP / FSDP

### DDP — 最简单的多卡训练

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  DDP (DistributedDataParallel) 原理:                              │
  │                                                                  │
  │  核心: 每张 GPU 有完整的模型副本，只切分数据                     │
  │                                                                  │
  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐           │
  │  │  GPU 0  │  │  GPU 1  │  │  GPU 2  │  │  GPU 3  │           │
  │  │ 完整模型 │  │ 完整模型 │  │ 完整模型 │  │ 完整模型 │           │
  │  │ Batch 0  │  │ Batch 1  │  │ Batch 2  │  │ Batch 3  │           │
  │  └────┬────┘  └────┬────┘  └────┬────┘  └────┬────┘           │
  │       │  前向+反向  │            │            │                  │
  │       ▼            ▼            ▼            ▼                  │
  │   梯度₀        梯度₁        梯度₂        梯度₃                  │
  │       └────────────┴──────┬─────┴────────────┘                  │
  │                     AllReduce (梯度求平均)                        │
  │       ┌────────────┬──────┴─────┬────────────┐                  │
  │       ▼            ▼            ▼            ▼                  │
  │   更新权重     更新权重     更新权重     更新权重                 │
  │  (相同梯度→相同权重→模型始终一致)                                │
  └──────────────────────────────────────────────────────────────────┘

  DDP 的精妙之处 — 梯度桶 (Gradient Bucketing):
    不是等所有梯度算完再通信，而是分成多个"桶"
    后面层的梯度先算完 → 先通信
    → 计算和通信重叠 (Overlap)，几乎零通信开销!

  局限: 每张 GPU 要放完整模型 → 7B 模型需要 14GB+ → 小卡放不下
```

### FSDP — 让小卡也能训大模型

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  FSDP (Fully Sharded Data Parallel) 原理:                        │
  │                                                                  │
  │  核心: 把模型参数、梯度、优化器状态都切分到多卡                  │
  │  本质: PyTorch 原生实现的 ZeRO-3                                  │
  │                                                                  │
  │  类比: 合租房                                                    │
  │    DDP = 每人有独立公寓 (完整模型副本) — 贵!                     │
  │    FSDP = 4人合租，家具拆开分别放各自房间                        │
  │           需要某个家具时，大家把各自的零件拼起来用                │
  │           用完再拆开各自收好                                      │
  │                                                                  │
  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐           │
  │  │  GPU 0  │  │  GPU 1  │  │  GPU 2  │  │  GPU 3  │           │
  │  │ 参数 1/4│  │ 参数 2/4│  │ 参数 3/4│  │ 参数 4/4│           │
  │  │ 梯度 1/4│  │ 梯度 2/4│  │ 梯度 3/4│  │ 梯度 4/4│           │
  │  │ 优化 1/4│  │ 优化 2/4│  │ 优化 3/4│  │ 优化 4/4│           │
  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘           │
  │                                                                  │
  │  计算时:                                                         │
  │    要算 Layer 3 → AllGather: 4卡把 Layer 3 的参数拼到一起       │
  │    前向/反向计算                                                  │
  │    计算完 → 各卡只保留自己那 1/4 的梯度 (ReduceScatter)          │
  │    → 释放不属于自己的参数                                        │
  │                                                                  │
  │  显存节省:                                                       │
  │    DDP (7B): 每卡 ~112 GB (参数14+梯度14+优化器84)               │
  │    FSDP (7B, 4卡): 每卡 ~28 GB  → 4 倍节省!                     │
  └──────────────────────────────────────────────────────────────────┘
```

### 代码示例

```python
# DDP — 3 行改造
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP

dist.init_process_group("nccl")
model = DDP(model.cuda(), device_ids=[local_rank])
# 启动: torchrun --nproc_per_node=4 train.py

# FSDP — 同样简洁
from torch.distributed.fsdp import FullyShardedDataParallel as FSDP
from torch.distributed.fsdp import ShardingStrategy

model = FSDP(
    model,
    sharding_strategy=ShardingStrategy.FULL_SHARD,  # ZeRO-3 等价
    # SHARD_GRAD_OP = ZeRO-2, NO_SHARD = DDP
    mixed_precision=MixedPrecision(
        param_dtype=torch.bfloat16,
        reduce_dtype=torch.float32,
    ),
)
# 启动: torchrun --nproc_per_node=4 train.py
```

---

## DeepSpeed

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  DeepSpeed = 微软的"显存魔术师"                                   │
  │                                                                  │
  │  核心武器: ZeRO (Zero Redundancy Optimizer)                       │
  │                                                                  │
  │  类比: 图书馆管理                                                │
  │    传统 (DDP): 每个分馆都买全套书 (4个分馆 = 4 套) — 浪费!      │
  │    ZeRO: 4 个分馆分工，每馆只买 1/4 的书                         │
  │          有人要借? 馆际互借 (AllGather)                           │
  │                                                                  │
  │  ZeRO 三阶段 (渐进式节省显存):                                   │
  │                                                                  │
  │  以 LLaMA-7B + 4 GPU 为例:                                      │
  │  (FP16 参数14GB + FP16 梯度14GB + FP32 优化器84GB = 112GB/卡)   │
  │                                                                  │
  │  Stage 1: 切分优化器状态                                         │
  │    每卡: 14 + 14 + 84/4 = 49 GB  (节省 56%)                     │
  │                                                                  │
  │  Stage 2: + 切分梯度                                             │
  │    每卡: 14 + 14/4 + 84/4 = 38.5 GB  (节省 66%)                 │
  │                                                                  │
  │  Stage 3: + 切分参数 (= FSDP)                                    │
  │    每卡: 14/4 + 14/4 + 84/4 = 28 GB  (节省 75%)                 │
  │                                                                  │
  │  ── ZeRO-Offload / ZeRO-Infinity ──                              │
  │                                                                  │
  │  更激进: 把不常用的数据卸载到 CPU 内存甚至 NVMe SSD              │
  │    GPU 显存放不下? → 溢出到 CPU 的 512GB 内存                    │
  │    CPU 内存也不够? → 溢出到 NVMe SSD (几TB)                     │
  │                                                                  │
  │  代价: 需要在 GPU ↔ CPU/NVMe 之间搬数据 → 速度变慢              │
  │  适用: "宁可慢点也要训起来" 的场景                               │
  └──────────────────────────────────────────────────────────────────┘
```

### 代码示例

```python
import deepspeed

model, optimizer, _, _ = deepspeed.initialize(
    model=model,
    config="ds_config.json"   # 所有优化策略都在配置文件里
)

# ds_config.json 核心配置:
# {
#   "zero_optimization": {
#     "stage": 3,                    // ZeRO Stage
#     "offload_optimizer": {"device": "cpu"},  // 优化器卸载到 CPU
#     "offload_param": {"device": "cpu"}       // 参数也卸载
#   },
#   "bf16": {"enabled": true},
#   "train_micro_batch_size_per_gpu": 4,
#   "gradient_accumulation_steps": 8
# }

# 启动: deepspeed --num_gpus=8 train.py --deepspeed ds_config.json
```

---

## Megatron-LM

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  Megatron-LM = NVIDIA 的"超大模型训练利器"                        │
  │                                                                  │
  │  核心: 3D 并行 (DP + TP + PP) 的最成熟实现                       │
  │                                                                  │
  │  类比: 建造航空母舰                                              │
  │    DDP/FSDP: 适合造驱逐舰 (10B 以内)                             │
  │    DeepSpeed: 能造巡洋舰 (100B 级别)                             │
  │    Megatron-LM: 专门造航母 (175B+ 级别)                          │
  │                                                                  │
  │  为什么 Megatron 的张量并行最强？                                 │
  │                                                                  │
  │  1. 通信和计算完美重叠                                           │
  │     Megatron 深入理解 Transformer 结构                            │
  │     知道 Attention 和 MLP 在哪里切分通信量最小                    │
  │     → Column Parallel + Row Parallel 的设计是原创的               │
  │                                                                  │
  │  2. 序列并行                                                     │
  │     LayerNorm 和 Dropout 也切分                                  │
  │     → 进一步减少激活值显存 (和张量并行互补)                      │
  │                                                                  │
  │  3. 通信优化                                                     │
  │     利用 NVLink 的高带宽做 TP (节点内)                           │
  │     利用 InfiniBand 做 DP 和 PP (节点间)                         │
  │     → 通信拓扑感知的并行策略                                     │
  │                                                                  │
  │  劣势:                                                           │
  │    - 代码量大，学习曲线陡峭                                      │
  │    - 文档相对较少                                                 │
  │    - 深度绑定 NVIDIA 生态                                        │
  │    - 通常需要和 DeepSpeed 联合使用 (Megatron-DeepSpeed)          │
  └──────────────────────────────────────────────────────────────────┘
```

### 代码示例

```python
# Megatron-LM 不是 pip install 就能用的，需要完整部署
# 典型启动命令:
"""
torchrun \
    --nproc_per_node 8 \
    --nnodes 8 \
    pretrain_gpt.py \
    --tensor-model-parallel-size 8 \
    --pipeline-model-parallel-size 8 \
    --num-layers 96 \
    --hidden-size 12288 \
    --num-attention-heads 96 \
    --micro-batch-size 1 \
    --global-batch-size 1536
"""
```

---

## ColossalAI

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  ColossalAI = "让大模型训练更简单"                                │
  │                                                                  │
  │  核心: 把 DeepSpeed + Megatron 的功能用更友好的 API 包装          │
  │                                                                  │
  │  类比: 各框架像不同的车                                          │
  │    DDP = 手动挡轿车 — 入门简单，但高速公路上不够用               │
  │    DeepSpeed = 越野车 — 功能强大，配置复杂                       │
  │    Megatron = F1 赛车 — 最快但需要专业车手                       │
  │    ColossalAI = 自动挡 SUV — 能力不差，最好上手                  │
  │                                                                  │
  │  特色功能:                                                       │
  │    Gemini: 自动管理 GPU/CPU 内存迁移 (不用手动配 offload)        │
  │    自动并行: 自动搜索最优并行策略                                 │
  │    Colossal-LLaMA: 低成本复现 LLaMA 训练                        │
  └──────────────────────────────────────────────────────────────────┘
```

---

## 框架对比总表

```
  ┌──────────────────────────────────────────────────────────────────────────────┐
  │                       训练框架全面对比                                       │
  ├──────────┬──────────────┬──────────────┬───────────────┬──────────────────┤
  │  维度    │ DDP/FSDP     │ DeepSpeed    │ Megatron-LM   │ ColossalAI      │
  ├──────────┼──────────────┼──────────────┼───────────────┼──────────────────┤
  │ 开发者   │ Meta         │ Microsoft    │ NVIDIA        │ HPC-AI Tech     │
  │ 核心技术 │ DP/ZeRO-3    │ ZeRO 1/2/3   │ 3D 并行       │ 封装 ZeRO+TP    │
  │ 张量并行 │ ❌            │ 有限         │ 最成熟        │ ✅               │
  │ 流水线   │ ❌            │ ✅            │ ✅(最佳)      │ ✅               │
  │ CPU卸载  │ ✅ FSDP      │ ✅ Infinity   │ ❌            │ ✅ Gemini       │
  │ 适合规模 │ < 10B        │ 10B-100B+    │ 100B+         │ < 100B          │
  │ 学习曲线 │ 低           │ 中           │ 高            │ 中低             │
  │ 文档     │ 优秀         │ 良好         │ 一般          │ 良好             │
  │ 生态绑定 │ PyTorch 原生 │ 独立         │ NVIDIA        │ 独立             │
  │ 类比     │ 手动挡轿车   │ 越野车       │ F1 赛车       │ 自动挡 SUV      │
  └──────────┴──────────────┴──────────────┴───────────────┴──────────────────┘
```

---

## 选择建议

```
  你的需求是什么？
      │
      ├─── "第一次多卡训练，模型 < 10B"
      │        → PyTorch DDP (最简单) 或 FSDP (省显存)
      │
      ├─── "7B-13B 模型微调 (LoRA/QLoRA)"
      │        → DeepSpeed ZeRO-2 + HuggingFace Trainer
      │          (开箱即用，社区支持最好)
      │
      ├─── "30B-70B 全参数训练"
      │        → DeepSpeed ZeRO-3 (+ CPU Offload 如果卡不够)
      │
      ├─── "100B+ 从头预训练"
      │        → Megatron-LM + DeepSpeed (业界标准)
      │
      ├─── "想快速上手大模型训练"
      │        → ColossalAI (API 最友好)
      │
      └─── "显存不够但一定要训"
               → DeepSpeed ZeRO-3 + CPU Offload
                 或 FSDP + CPU Offload
```

---

*下一篇：[08-communication-optimization.md](08-communication-optimization.md) - 通信优化*
