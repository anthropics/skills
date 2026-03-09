# 流水线并行详解

> 理解流水线并行的按层切分、调度策略和气泡优化。

## 目录

- [流水线并行原理](#流水线并行原理)
- [调度策略](#调度策略)
- [气泡问题与优化](#气泡问题与优化)
- [配置示例](#配置示例)

---

## 流水线并行原理

### 生活类比：工厂流水线

想象一条汽车装配流水线有 4 个车间：

```
┌──────────────────────────────────────────────────────────────────────────┐
│                    汽车装配流水线 = 流水线并行                              │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  车间 1 (GPU 0)    车间 2 (GPU 1)    车间 3 (GPU 2)    车间 4 (GPU 3)  │
│  ┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐      │
│  │ 焊接车架  │ ──→ │ 安装引擎  │ ──→ │ 装配内饰  │ ──→ │ 喷漆检测  │      │
│  │ Layer 0-5│     │ Layer 6-11│     │Layer12-17│     │Layer18-23│      │
│  └──────────┘     └──────────┘     └──────────┘     └──────────┘      │
│                                                                          │
│  每个车间只负责自己的工序，一辆车做完传给下一个车间                        │
│                                                                          │
│  问题：只有一辆车时，其他车间都在等！（气泡问题）                         │
│  优化：同时放多辆车（micro-batch），让每个车间都忙起来                    │
│                                                                          │
│  关键区别于数据并行：                                                     │
│  数据并行 = 4 条完全一样的流水线，各处理不同订单                          │
│  流水线并行 = 1 条流水线被拆成 4 段，分在 4 个车间                       │
└──────────────────────────────────────────────────────────────────────────┘
```

### 按层切分的原理

为什么 Transformer 可以按层切分？三个关键条件：

```
条件 1: 统一接口 —— 每层输入输出形状完全相同
  Layer i 输入:  [batch, seq_len, hidden_dim]
  Layer i 输出:  [batch, seq_len, hidden_dim]
  
  就像标准化的工业接口，任意一层都可以"接上"下一层

条件 2: 无共享参数 —— 各层参数完全独立
  Layer 0 的 W₀ 和 Layer 1 的 W₁ 互不依赖
  切到不同 GPU 后，不需要跨 GPU 访问参数

条件 3: 严格串行依赖 —— 第 i+1 层只依赖第 i 层的输出
  h₁ = Layer1(h₀)       # 只需要上一层的输出
  h₂ = Layer2(h₁)       # 不需要 h₀
  
  通信只发生在相邻 Stage 之间，通信量 = 中间激活值的大小
  远小于张量并行的 AllReduce 通信量
```

### 切分示例：LLaMA-7B（32 层）分到 4 个 GPU

```
GPU 0 (Stage 0): Embedding + Layer 0-7    → ~2.0B 参数
GPU 1 (Stage 1): Layer 8-15               → ~1.8B 参数
GPU 2 (Stage 2): Layer 16-23              → ~1.8B 参数
GPU 3 (Stage 3): Layer 24-31 + LM Head    → ~2.0B 参数

每个 GPU 只存 ~1/4 的参数 → 每 GPU 约 3.5GB (FP16)
加上优化器：每 GPU 约 28GB（远小于 DDP 的 112GB）

Stage 间通信量（每个 micro-batch）：
  传输的数据 = hidden state: [micro_bs, seq_len, 4096]
  = 1 × 2048 × 4096 × 2 bytes(FP16) ≈ 16 MB
  对比 TP 的 AllReduce：每层 2 次，总共约 2GB
  PP 通信量远小于 TP！
```

### 与张量并行的对比

| 特性 | 张量并行 (TP) | 流水线并行 (PP) |
|------|--------------|----------------|
| 切分方式 | 层内矩阵切分 | 按层整体切分 |
| 通信模式 | 每层 2 次 AllReduce | 相邻 Stage 点对点 |
| 通信量 | 大（每层都通信） | 小（仅传激活值） |
| 带宽要求 | 极高（需 NVLink） | 中等（PCIe 可接受） |
| 气泡 | 无 | 有（核心问题） |
| 适用场景 | 机内高速互连 | 跨机低带宽环境 |

---

## 调度策略

### 朴素流水线（Naive Pipeline）

最简单的策略：先做完所有前向，再做所有反向。

```
Time ──────────────────────────────────────────────────────→

GPU 0: │ F0 │ F1 │ F2 │ F3 │         │         │ B3 │ B2 │ B1 │ B0 │
GPU 1: │    │ F0 │ F1 │ F2 │ F3 │    │    │ B3 │ B2 │ B1 │ B0 │    │
GPU 2: │    │    │ F0 │ F1 │ F2 │ F3 │ B3 │ B2 │ B1 │ B0 │    │    │
GPU 3: │    │    │    │ F0 │ F1 │ F2 │ F3/B3│B2 │ B1 │ B0 │    │    │
       └───────────────────────────────────────────────────────────────┘
        ████ = 计算     空白 = 气泡（GPU 空闲）

气泡率 = (P-1)/P = 3/4 = 75%  ← 灾难性浪费！

另一个问题——显存爆炸：
  GPU 0 做完 4 个 micro-batch 的前向后，
  必须保留所有中间激活值等待反向传播
  激活值内存 ∝ micro-batch 数量 × 每个的激活大小
```

**类比**：工厂只有一辆车在流水线上，车间 1 做完传给车间 2 后就干等着，3/4 的时间都在空闲。

### GPipe 调度

核心改进：把一个大 batch 切成多个 micro-batch，"填满"流水线。

```
Global batch (32 samples) → 8 micro-batches (每个 4 samples)

Time ──────────────────────────────────────────────────────────────────→

GPU 0: │f0│f1│f2│f3│f4│f5│f6│f7│  │  │  │b7│b6│b5│b4│b3│b2│b1│b0│ 更新 │
GPU 1: │  │f0│f1│f2│f3│f4│f5│f6│f7│  │b7│b6│b5│b4│b3│b2│b1│b0│  │ 更新 │
GPU 2: │  │  │f0│f1│f2│f3│f4│f5│f6│f7│b7│b6│b5│b4│b3│b2│b1│b0│  │ 更新 │
GPU 3: │  │  │  │f0│f1│f2│f3│f4│f5│f6│f7│b7│b6│b5│b4│b3│b2│b1│b0│ 更新 │
       └───────────────────────────────────────────────────────────────────┘
        █ = 前向   █ = 反向   空白 = 气泡

气泡率 = (P-1)/(P+M-1) = 3/(4+8-1) = 3/11 ≈ 27%  ← 大幅改善！

M 越大气泡越少：
  M = 4:   3/7  = 43%
  M = 8:   3/11 = 27%
  M = 16:  3/19 = 16%
  M = 32:  3/35 = 8.6%
  M → ∞:  → 0%

代价：M 越大，需要保存的激活值越多 → 显存压力增大
```

**类比**：工厂同时放 8 辆车到流水线，车间 1 做完第 1 辆立刻做第 2 辆，等做完 8 辆的焊接后，第 1 辆已经到了车间 4。空闲时间大幅减少。

### 1F1B 调度（One Forward One Backward）

核心改进：**前向和反向交替执行**，不等所有前向做完才开始反向。

```
Time ──────────────────────────────────────────────────────────────→

GPU 0: │f0│f1│f2│f3│  b0│f4│  b1│f5│  b2│f6│  b3│f7│  b4│  b5│  b6│  b7│
GPU 1: │  │f0│f1│f2│f3│  b0│f4│  b1│f5│  b2│f6│  b3│f7│  b4│  b5│  b6│  b7│
GPU 2: │  │  │f0│f1│f2│f3│  b0│f4│  b1│f5│  b2│f6│  b3│f7│  b4│  b5│  b6│b7│
GPU 3: │  │  │  │f0│f1│f2│f3│b0│f4│b1│f5│b2│f6│b3│f7│b4│b5│b6│b7│
       └───────────────────────────────────────────────────────────────────┘

关键优势：
1. 气泡率与 GPipe 相同: ≈ (P-1)/M
2. 但显存占用恒定！只需保存 P 个（而非 M 个）micro-batch 的激活值

为什么？
  GPipe：做完 M 个前向才开始反向 → 需保存 M 个激活
  1F1B：做完 P 个前向后，每做一个前向就做一个反向 → 释放一个激活
  
  活跃激活数始终 ≤ P（pipeline stages 数）
  当 M >> P 时（通常 M=32, P=4），显存节省 M/P = 8 倍！
```

**类比**：不是等所有车做完焊接再一起进引擎车间，而是第 1 辆车做完所有工序后，车间 1 立刻开始做下一辆的同时，已完工的车就出厂了——"边进边出"。

### 三种调度策略的对比

| 策略 | 气泡率 | 激活内存 | 实现复杂度 | 代表框架 |
|------|--------|----------|-----------|---------|
| 朴素 | (P-1)/P | M个 | 简单 | 教学用 |
| GPipe | (P-1)/(P+M-1) | M个 | 中等 | GPipe |
| 1F1B | ≈(P-1)/M | P个 | 较高 | Megatron-LM, DeepSpeed |

---

## 气泡问题与优化

### 气泡是什么？为什么无法完全消除？

```
气泡的本质：由于 Stage 间的串行依赖，GPU 不得不等待上游的输出

Stage 1 必须等 Stage 0 的输出才能开始 → 开始时有延迟
Stage 0 必须等 Stage 3 的反向梯度传回来 → 中间有空闲

这是一个基本的"填充-排空"问题：
  填充阶段：流水线逐渐装满，前面的 Stage 有气泡
  稳态阶段：所有 Stage 都在工作（如果 M 足够大）
  排空阶段：流水线逐渐清空，后面的 Stage 有气泡

不管怎么调度，填充和排空阶段的气泡无法消除，只能缩小
```

### 气泡率计算与数值示例

```
设：P = pipeline stages, M = micro-batches

朴素:   bubble = (P-1)/P
GPipe:  bubble = (P-1)/(P+M-1)
1F1B:   bubble ≈ (P-1)/M

实际计算（P=4, 不同 M 值）:

┌──────┬───────────┬──────────┬──────────┐
│  M   │  朴素     │  GPipe   │   1F1B   │
├──────┼───────────┼──────────┼──────────┤
│  4   │  75.0%    │  42.9%   │  75.0%   │
│  8   │  75.0%    │  27.3%   │  37.5%   │
│  16  │  75.0%    │  15.8%   │  18.8%   │
│  32  │  75.0%    │   8.6%   │   9.4%   │
│  64  │  75.0%    │   4.5%   │   4.7%   │
└──────┴───────────┴──────────┴──────────┘

结论：
- 朴素方案不随 M 改善
- GPipe 和 1F1B 在 M 足够大时，气泡率可降到 <5%
- 但 M 越大 → 单个 micro-batch 越小 → GPU 利用率可能下降（计算量太小）
- 需要在气泡率和计算效率之间找平衡
```

### 进阶优化：Interleaved Pipeline（交错流水线）

Megatron-LM 提出的优化：让每个 GPU 负责多段不相邻的层。

```
普通分配（4 GPU, 16 层）:
  GPU 0: Layer 0-3     (Stage 0)
  GPU 1: Layer 4-7     (Stage 1)
  GPU 2: Layer 8-11    (Stage 2)
  GPU 3: Layer 12-15   (Stage 3)

交错分配（每 GPU 2 段，称为 virtual stages）:
  GPU 0: Layer 0-1, Layer 8-9     (Stage 0a, 0b)
  GPU 1: Layer 2-3, Layer 10-11   (Stage 1a, 1b)
  GPU 2: Layer 4-5, Layer 12-13   (Stage 2a, 2b)
  GPU 3: Layer 6-7, Layer 14-15   (Stage 3a, 3b)

数据流: 0a → 1a → 2a → 3a → 0b → 1b → 2b → 3b

优势：virtual pipeline stages = 2P，气泡率从 (P-1)/M 降到 (P-1)/(v·M)
      其中 v = 每 GPU 的 virtual stage 数
      v=2 时气泡减半！

代价：通信次数翻倍（数据需要在 GPU 间多传几次），
      且实现更复杂
```

### Stage 间负载均衡

```
问题：如果各 Stage 计算量不均匀，快的 Stage 等慢的 → 额外气泡

Transformer 模型中不均匀的来源：
  - Stage 0 通常有 Embedding 层（参数量大，但计算快）
  - Stage 最后有 LM Head（需要计算 logits，vocab_size 很大）
  - 某些层可能有条件计算（MoE 模型）

优化策略：
  1. 按参数量均匀分：partition_method = "parameters"
  2. 按计算量均匀分：partition_method = "type:transformer"  
  3. Profile-based：先跑一遍收集各层时间，再最优分配

  DeepSpeed 的分配方式：
  ┌─────────────────────────────────────────────────────┐
  │  uniform:  每 Stage 分相同层数                       │
  │  parameters: 每 Stage 分相近参数量                   │
  │  custom: 用户指定 [8, 8, 8, 8] 的层数分配           │
  └─────────────────────────────────────────────────────┘
```

---

## 配置示例

### DeepSpeed Pipeline

```python
ds_config = {
    "train_batch_size": 1024,
    "train_micro_batch_size_per_gpu": 4,
    "gradient_accumulation_steps": 64,  # = M (micro-batch 数)
    
    "pipeline": {
        "stages": 4,
        "partition_method": "uniform"  # 或 "parameters"
    }
}

# 理解这些参数的关系：
# train_batch_size = micro_batch_size × gradient_accumulation × data_parallel_size
# 1024 = 4 × 64 × 4 (假设 DP=4)
#
# M = gradient_accumulation_steps = 64
# 气泡率 ≈ (4-1)/64 = 4.7%  ← 很不错！
```

### Megatron-LM

```bash
python pretrain_gpt.py \
    --pipeline-model-parallel-size 4 \         # P = 4 stages
    --micro-batch-size 1 \                      # 每个 micro-batch
    --global-batch-size 512 \                   # 全局 batch
    --num-layers-per-virtual-pipeline-stage 2 \ # 交错流水线
    ...

# virtual stages = num_layers / layers_per_virtual_stage / PP
# 如 32 层: 32 / 2 / 4 = 4 virtual stages per GPU
# 气泡率从 (4-1)/M 降到 (4-1)/(4·M)
```

### 完整的 3D 并行配置示例

```python
# 典型的 LLaMA-65B 训练配置
# 64 GPU = 8 机 × 8 卡
# TP=4 (机内 4 卡), PP=4 (4 个 Stage), DP=4 (4 路数据并行)

megatron_config = {
    "tensor_model_parallel_size": 4,     # TP: 需要 NVLink
    "pipeline_model_parallel_size": 4,   # PP: 可跨机
    "data_parallel_size": 4,             # DP: 自动计算 = 64/(4×4)
    "micro_batch_size": 1,
    "global_batch_size": 1024,
    # gradient_accumulation = 1024 / (1 × 4) = 256 micro-batches
    # 气泡率 ≈ (4-1)/256 = 1.2%  ← 接近理想
}
```

---

## 小结

```
流水线并行的核心要点：

1. 按层切分 → 每 GPU 只存部分层 → 突破单卡显存限制
2. 气泡问题 → GPU 因等待而空闲 → 通过增加 micro-batch 缓解
3. 调度策略进化：
   朴素 (75% 气泡) → GPipe (~10%) → 1F1B (~10% 但省内存) → 交错 (~5%)
4. 通信量小 → 适合跨机部署（不需要 NVLink）
5. 实际使用 → 通常与 TP、DP 组合为 3D 并行
```

---

*下一篇：[06-3d-parallelism.md](06-3d-parallelism.md) - 3D 并行实践*
