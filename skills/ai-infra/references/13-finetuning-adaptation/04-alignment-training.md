# 对齐训练基础设施

> 对齐训练就像让AI"实习"后还要通过"职业道德考试"——不仅要能力强，还要行为合规。

## 目录

- [对齐训练概述](#对齐训练概述)
- [RLHF 基础设施需求](#rlhf-基础设施需求)
- [DPO 基础设施需求](#dpo-基础设施需求)
- [TRL 框架实战](#trl-框架实战)
- [OpenRLHF 框架](#openrlhf-框架)
- [奖励模型训练](#奖励模型训练)
- [生产级对齐训练](#生产级对齐训练)
- [延伸阅读](#延伸阅读)

---

## 对齐训练概述

### 为什么需要对齐训练基础设施

对齐训练与常规 SFT 的基础设施需求有显著差异：

```
SFT vs 对齐训练的复杂度对比

SFT 训练:
┌─────────────────┐
│   单个模型训练    │ ← 简单，一个模型
│   Model + Data   │
└─────────────────┘

RLHF 训练:
┌─────────────────┐   ┌─────────────────┐
│  Actor Model    │   │  Reward Model   │
│  (策略模型)      │   │  (奖励模型)      │
├─────────────────┤   ├─────────────────┤
│  Critic Model   │   │  Reference Model │
│  (价值模型)      │   │  (参考模型)       │
└─────────────────┘   └─────────────────┘
        ↑ 4 个模型需要同时在 GPU 上！

DPO 训练:
┌─────────────────┐   ┌─────────────────┐
│  Policy Model   │   │  Reference Model │
│  (策略模型)      │   │  (参考模型)       │
└─────────────────┘   └─────────────────┘
        ↑ 2 个模型，比 RLHF 简单
```

### 对齐方法的基础设施对比

| 维度 | SFT | DPO | RLHF (PPO) |
|------|-----|-----|------------|
| 同时加载模型数 | 1 | 2 | 4 |
| GPU 需求倍数 | 1x | 2x | 4-6x |
| 实现复杂度 | 低 | 中 | 高 |
| 训练稳定性 | 高 | 中 | 低 |
| 数据需求 | 指令数据 | 偏好对 | 偏好对 + 在线生成 |
| 训练速度 | 快 | 中 | 慢 |
| 效果上限 | 中 | 中高 | 最高 |

---

## RLHF 基础设施需求

### RLHF 训练流程

```
RLHF (PPO) 训练的数据流

                    ┌────────────┐
   Prompt ─────────▶│Actor Model │──────▶ 生成回复
                    └────────────┘           │
                                             ▼
                    ┌────────────┐    ┌──────────────┐
                    │ Ref Model  │───▶│  KL 散度计算  │
                    └────────────┘    └──────────────┘
                                             │
                    ┌────────────┐           ▼
   生成回复 ────────▶│Reward Model│──▶ Reward Score
                    └────────────┘           │
                                             ▼
                    ┌────────────┐    ┌──────────────┐
                    │Critic Model│───▶│ 优势估计(GAE) │
                    └────────────┘    └──────────────┘
                                             │
                                             ▼
                                    ┌──────────────┐
                                    │  PPO 更新     │
                                    │Actor + Critic │
                                    └──────────────┘
```

### GPU 需求估算

```
RLHF 训练的 GPU 显存分布（以 7B 模型为例，FP16）

Actor Model:     14 GB (权重) + 14 GB (梯度) + 56 GB (优化器) = ~84 GB
Critic Model:    14 GB + 14 GB + 56 GB = ~84 GB
Reward Model:    14 GB (仅推理) = ~14 GB
Reference Model: 14 GB (仅推理) = ~14 GB
─────────────────────────────────────────────────
总计:            ~196 GB

实际需求（含中间状态）:
  7B RLHF:   4-8× A100 80GB
  13B RLHF:  8-16× A100 80GB
  70B RLHF:  32-64× A100 80GB

优化策略:
  • Actor/Critic 用 LoRA → 大幅减少显存
  • Reward/Ref 用量化（INT8/INT4）
  • 模型分时加载（牺牲速度换显存）
  • DeepSpeed ZeRO-3 分片
```

### RLHF 的挑战

```
RLHF 工程挑战清单

1. 训练不稳定
   ├── Reward hacking（模型钻奖励模型漏洞）
   ├── KL 散度爆炸
   ├── PPO 的超参数敏感性
   └── 解决：KL 惩罚、梯度裁剪、保守更新

2. 资源消耗大
   ├── 4 个模型同时在 GPU
   ├── 生成回复需要自回归解码（慢）
   ├── 每步需要多次前向/反向传播
   └── 解决：模型并行、LoRA、vLLM 加速生成

3. 工程复杂度高
   ├── 多模型协调调度
   ├── 数据流管理
   ├── 分布式训练配置
   └── 解决：使用成熟框架（TRL/OpenRLHF）
```

---

## DPO 基础设施需求

### DPO 的简化优势

```
DPO vs PPO 基础设施对比

PPO (RLHF):                       DPO:
┌─────────┐ ┌─────────┐          ┌─────────┐ ┌─────────┐
│ Actor   │ │ Critic  │          │ Policy  │ │  Ref    │
│ (train) │ │ (train) │          │ (train) │ │ (frozen)│
├─────────┤ ├─────────┤          └─────────┘ └─────────┘
│ Reward  │ │  Ref    │          
│ (frozen)│ │ (frozen)│          ✅ 不需要 Reward Model
└─────────┘ └─────────┘          ✅ 不需要 Critic Model
                                  ✅ 不需要在线生成
4 个模型 → ~4-6x GPU              2 个模型 → ~2x GPU
训练复杂 → 超参数敏感              训练简单 → 类似 SFT
```

### DPO GPU 需求

```
DPO 训练 GPU 需求

模型规模    Policy (训练)     Ref (推理)      总需求
──────────────────────────────────────────────────────
  7B        LoRA: ~20 GB     INT8: ~7 GB     1× A100 40GB
            Full: ~84 GB     FP16: 14 GB     2× A100 80GB

 13B        LoRA: ~32 GB     INT8: ~13 GB    1× A100 80GB
            Full: ~156 GB    FP16: 26 GB     4× A100 80GB

 70B        LoRA: ~80 GB     INT8: ~35 GB    4× A100 80GB
            Full: ~840 GB    FP16: 140 GB    16× A100 80GB
```

---

## TRL 框架实战

### DPO 训练示例

```python
from trl import DPOTrainer, DPOConfig
from transformers import AutoModelForCausalLM, AutoTokenizer
from datasets import load_dataset
from peft import LoraConfig

# 1. 加载模型
model_name = "meta-llama/Llama-3.1-8B-Instruct"
model = AutoModelForCausalLM.from_pretrained(model_name, torch_dtype=torch.bfloat16)
ref_model = AutoModelForCausalLM.from_pretrained(model_name, torch_dtype=torch.bfloat16)
tokenizer = AutoTokenizer.from_pretrained(model_name)
tokenizer.pad_token = tokenizer.eos_token

# 2. 加载偏好数据集
# 数据格式: {"prompt": "...", "chosen": "...", "rejected": "..."}
dataset = load_dataset("argilla/ultrafeedback-binarized-preferences", split="train")

# 3. LoRA 配置
peft_config = LoraConfig(
    r=16,
    lora_alpha=32,
    target_modules=["q_proj", "k_proj", "v_proj", "o_proj"],
    lora_dropout=0.05,
    task_type="CAUSAL_LM",
)

# 4. DPO 训练配置
dpo_config = DPOConfig(
    output_dir="./dpo-llama3-8b",
    num_train_epochs=1,
    per_device_train_batch_size=2,
    gradient_accumulation_steps=8,
    learning_rate=5e-5,              # DPO 通常用较小学习率
    beta=0.1,                        # KL 惩罚系数
    max_length=1024,
    max_prompt_length=512,
    bf16=True,
    gradient_checkpointing=True,
    logging_steps=10,
    save_steps=500,
)

# 5. 初始化 DPO Trainer
trainer = DPOTrainer(
    model=model,
    ref_model=ref_model,
    args=dpo_config,
    tokenizer=tokenizer,
    train_dataset=dataset,
    peft_config=peft_config,
)

# 6. 训练
trainer.train()
trainer.save_model("./dpo-llama3-8b-final")
```

### PPO 训练示例

```python
from trl import PPOTrainer, PPOConfig, AutoModelForCausalLMWithValueHead
from transformers import AutoTokenizer

# 1. 加载模型（带 Value Head）
model = AutoModelForCausalLMWithValueHead.from_pretrained(
    "sft-model-path",  # 已经过 SFT 的模型
    torch_dtype=torch.bfloat16,
    peft_config=peft_config,  # 可选 LoRA
)

# 2. 加载 Reward Model
reward_model = AutoModelForSequenceClassification.from_pretrained(
    "reward-model-path",
    torch_dtype=torch.bfloat16,
)

# 3. PPO 配置
ppo_config = PPOConfig(
    learning_rate=1e-5,
    batch_size=64,
    mini_batch_size=16,
    gradient_accumulation_steps=4,
    ppo_epochs=4,               # 每批数据 PPO 更新次数
    kl_penalty="kl",            # KL 惩罚类型
    init_kl_coef=0.2,           # 初始 KL 系数
    target_kl=6.0,              # 目标 KL 值
    cliprange=0.2,              # PPO clip 范围
    vf_coef=0.1,                # Value function 损失系数
)

# 4. 初始化 PPO Trainer
ppo_trainer = PPOTrainer(
    config=ppo_config,
    model=model,
    tokenizer=tokenizer,
)

# 5. 训练循环
for batch in dataloader:
    # 生成回复
    response_tensors = ppo_trainer.generate(batch["input_ids"])
    
    # 计算奖励
    rewards = compute_rewards(reward_model, batch, response_tensors)
    
    # PPO 更新
    stats = ppo_trainer.step(batch["input_ids"], response_tensors, rewards)
    
    # 日志
    ppo_trainer.log_stats(stats, batch, rewards)
```

---

## OpenRLHF 框架

### 架构概览

```
OpenRLHF 架构

┌──────────────────────────────────────────────┐
│                OpenRLHF                       │
├──────────────────────────────────────────────┤
│                                               │
│  ┌─────────┐   ┌─────────┐   ┌───────────┐  │
│  │ Ray      │   │vLLM     │   │DeepSpeed  │  │
│  │ 调度框架  │   │推理加速  │   │训练框架    │  │
│  └────┬─────┘   └────┬────┘   └─────┬─────┘  │
│       │              │              │         │
│  ┌────▼──────────────▼──────────────▼─────┐  │
│  │          统一训练引擎                     │  │
│  │  • RLHF (PPO)                          │  │
│  │  • DPO / KTO / ORPO                    │  │
│  │  • Rejection Sampling                   │  │
│  │  • Iterative DPO                        │  │
│  └────────────────────────────────────────┘  │
│                                               │
│  特点:                                        │
│  • 生成和训练分离（Actor-Learner 架构）         │
│  • vLLM 加速生成（3-5x 加速）                 │
│  • 支持 70B+ 模型的 RLHF                      │
│  • Ray 调度多节点分布式                        │
└──────────────────────────────────────────────┘
```

### OpenRLHF 使用示例

```bash
# 安装
pip install openrlhf[vllm]

# RLHF (PPO) 训练 - 使用 Ray 和 vLLM
ray job submit --address="http://ray-head:8265" \
  -- python3 -m openrlhf.cli.train_ppo_ray \
    --ref_num_nodes 1 \
    --ref_num_gpus_per_node 2 \
    --reward_num_nodes 1 \
    --reward_num_gpus_per_node 2 \
    --critic_num_nodes 1 \
    --critic_num_gpus_per_node 2 \
    --actor_num_nodes 1 \
    --actor_num_gpus_per_node 2 \
    --vllm_num_engines 2 \
    --vllm_tensor_parallel_size 2 \
    --pretrain meta-llama/Llama-3.1-8B-Instruct \
    --reward_pretrain reward-model-path \
    --save_path ./rlhf-output \
    --micro_train_batch_size 8 \
    --train_batch_size 128 \
    --micro_rollout_batch_size 16 \
    --rollout_batch_size 1024 \
    --max_epochs 1 \
    --prompt_max_len 1024 \
    --generate_max_len 1024 \
    --actor_learning_rate 5e-7 \
    --critic_learning_rate 9e-6 \
    --init_kl_coef 0.01 \
    --use_wandb your-wandb-key
```

### 框架对比

| 维度 | TRL | OpenRLHF | DeepSpeed-Chat |
|------|-----|----------|----------------|
| 维护方 | HuggingFace | 社区 | Microsoft |
| PPO 支持 | ✅ | ✅ | ✅ |
| DPO/KTO | ✅ | ✅ | ❌ |
| vLLM 集成 | ❌ | ✅ | ❌ |
| 70B+ RLHF | 困难 | ✅ | ✅ |
| 易用性 | 最高 | 中 | 中 |
| 生态集成 | HF 生态 | 独立 | DeepSpeed |

---

## 奖励模型训练

### 奖励模型架构

```
奖励模型 = LLM + 线性分类头

┌──────────────────────────────────┐
│    Input: (prompt, response)     │
│              ↓                   │
│    ┌──────────────────┐         │
│    │  LLM Backbone    │ ← 可以从 SFT 模型初始化
│    │  (Llama-8B etc.) │
│    └────────┬─────────┘         │
│             ↓                   │
│    Last token hidden state      │
│             ↓                   │
│    ┌──────────────────┐         │
│    │  Linear Head     │ ← 新增的标量输出层
│    │  hidden → 1      │
│    └────────┬─────────┘         │
│             ↓                   │
│      Reward Score (标量)         │
└──────────────────────────────────┘
```

### 训练代码

```python
from trl import RewardTrainer, RewardConfig
from transformers import AutoModelForSequenceClassification, AutoTokenizer

# 1. 加载模型（添加分类头）
model = AutoModelForSequenceClassification.from_pretrained(
    "meta-llama/Llama-3.1-8B-Instruct",
    num_labels=1,                    # 标量输出
    torch_dtype=torch.bfloat16,
)
tokenizer = AutoTokenizer.from_pretrained("meta-llama/Llama-3.1-8B-Instruct")
tokenizer.pad_token = tokenizer.eos_token

# 2. 偏好数据格式
# {"chosen": "好的回答...", "rejected": "差的回答...", "prompt": "问题..."}
dataset = load_dataset("Anthropic/hh-rlhf", split="train")

# 3. 训练配置
reward_config = RewardConfig(
    output_dir="./reward-model",
    num_train_epochs=1,
    per_device_train_batch_size=4,
    gradient_accumulation_steps=8,
    learning_rate=1e-5,
    bf16=True,
    max_length=1024,
    logging_steps=10,
    eval_strategy="steps",
    eval_steps=500,
)

# 4. 训练
trainer = RewardTrainer(
    model=model,
    args=reward_config,
    tokenizer=tokenizer,
    train_dataset=dataset["train"],
    eval_dataset=dataset["test"],
)
trainer.train()

# 奖励模型训练的关键指标
# Accuracy: chosen 回复的分数应高于 rejected
# 目标: accuracy > 70%（随机 50%）
```

### 偏好数据收集

```
偏好数据收集流程

1. 人工标注
   ┌─────────────────────────────────────────────┐
   │ Prompt: "如何学习编程？"                       │
   │                                               │
   │ 回复 A: "首先，选择一门语言如 Python..."         │
   │ 回复 B: "编程很简单，随便看看就行了"             │
   │                                               │
   │ 标注员选择: A > B  ← 这就是一条偏好数据         │
   └─────────────────────────────────────────────┘

2. AI 辅助（RLAIF）
   ┌─────────────────────────────────────────────┐
   │ 用 GPT-4/Claude 作为标注者                    │
   │ 成本低、速度快，但可能引入偏见                  │
   └─────────────────────────────────────────────┘

3. 隐式反馈
   ┌─────────────────────────────────────────────┐
   │ 用户点赞/点踩 → 偏好信号                      │
   │ 用户重新生成 → rejected 信号                   │
   │ 用户编辑回复 → chosen 是编辑后的版本            │
   └─────────────────────────────────────────────┘
```

---

## 生产级对齐训练

### 训练管线设计

```
生产级对齐训练管线

Phase 1: 数据准备
┌──────────┐   ┌──────────┐   ┌──────────┐
│ 偏好数据  │──▶│ 质量过滤  │──▶│ 去重去污  │
│ 收集     │   │ 清洗     │   │ 染       │
└──────────┘   └──────────┘   └──────────┘

Phase 2: 奖励模型
┌──────────┐   ┌──────────┐   ┌──────────┐
│ RM 训练   │──▶│ RM 评估   │──▶│ RM 部署   │
│          │   │ (Acc>70%) │   │          │
└──────────┘   └──────────┘   └──────────┘

Phase 3: 对齐训练
┌──────────┐   ┌──────────┐   ┌──────────┐
│ DPO/PPO  │──▶│ 安全评估   │──▶│ 基准测试  │
│ 训练     │   │          │   │          │
└──────────┘   └──────────┘   └──────────┘

Phase 4: 验证上线
┌──────────┐   ┌──────────┐   ┌──────────┐
│ A/B 测试  │──▶│ 人工评估   │──▶│ 灰度发布  │
│          │   │          │   │          │
└──────────┘   └──────────┘   └──────────┘
```

### 超参数速查

```
对齐训练超参数推荐

DPO 超参数:
┌────────────────┬─────────────────┬────────────────────────┐
│ 参数           │ 推荐值           │ 说明                    │
├────────────────┼─────────────────┼────────────────────────┤
│ beta           │ 0.1 - 0.5       │ KL 惩罚系数，越大越保守  │
│ learning_rate  │ 1e-6 - 5e-5     │ 比 SFT 小              │
│ epochs         │ 1 - 3           │ 过多容易过拟合           │
│ batch_size     │ 32 - 128        │ 偏好对的有效批大小       │
│ max_length     │ 1024 - 2048     │ 包含 prompt+response    │
└────────────────┴─────────────────┴────────────────────────┘

PPO 超参数:
┌────────────────┬─────────────────┬────────────────────────┐
│ 参数           │ 推荐值           │ 说明                    │
├────────────────┼─────────────────┼────────────────────────┤
│ init_kl_coef   │ 0.01 - 0.2     │ 初始 KL 惩罚系数        │
│ target_kl      │ 6.0            │ 自适应 KL 目标          │
│ cliprange      │ 0.2            │ PPO clip 范围           │
│ ppo_epochs     │ 2 - 4          │ 每批 PPO 更新次数       │
│ actor_lr       │ 5e-7 - 1e-5    │ Actor 学习率            │
│ critic_lr      │ 5e-6 - 5e-5    │ Critic 通常更大         │
└────────────────┴─────────────────┴────────────────────────┘
```

---

## 延伸阅读

- [Training Language Models to Follow Instructions with Human Feedback](https://arxiv.org/abs/2203.02155) - InstructGPT / RLHF 原论文
- [Direct Preference Optimization](https://arxiv.org/abs/2305.18290) - DPO 原论文
- [OpenRLHF Documentation](https://github.com/OpenRLHF/OpenRLHF)
- [TRL PPO Trainer](https://huggingface.co/docs/trl/ppo_trainer)
- [Scaling Laws for Reward Model Overoptimization](https://arxiv.org/abs/2210.10760) - RM 过优化分析
- [RLHF Workflow: From Reward Modeling to Online RLHF](https://arxiv.org/abs/2405.07863)

---

*上一篇：[03-sft-pipeline.md](03-sft-pipeline.md)* | *下一篇：[05-finetuning-platforms.md](05-finetuning-platforms.md)*

[返回目录](README.md) | [返回主页](../README.md)
