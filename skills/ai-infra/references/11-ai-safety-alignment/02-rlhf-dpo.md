# RLHF 与 DPO

> RLHF 让模型从"知道答案"变成"知道什么是好答案"——通过人类偏好信号训练模型的价值判断能力。

## 目录

- [RLHF 全流程](#rlhf-全流程)
- [奖励模型训练](#奖励模型训练)
- [PPO 训练](#ppo-训练)
- [DPO：无需奖励模型的对齐](#dpo无需奖励模型的对齐)
- [其他偏好优化方法](#其他偏好优化方法)
- [基础设施需求与框架](#基础设施需求与框架)
- [延伸阅读](#延伸阅读)

---

## RLHF 全流程

### 三阶段流程

```
┌─────────────────────────────────────────────────────────────────┐
│                 RLHF 三阶段流程                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  阶段 1: SFT (Supervised Fine-tuning)                            │
│  ┌──────────────────────────────────────────┐                   │
│  │  预训练模型 + 高质量对话数据 → SFT 模型     │                   │
│  │  目的: 让模型学会"对话格式"                 │                   │
│  │  数据: ~10K-100K 条高质量指令-回复对         │                   │
│  └──────────────────────────────────────────┘                   │
│                          │                                      │
│                          ▼                                      │
│  阶段 2: RM (Reward Model Training)                              │
│  ┌──────────────────────────────────────────┐                   │
│  │  收集人类偏好数据:                         │                   │
│  │    Prompt → 模型生成 2+ 个回复              │                   │
│  │    人类标注员选择更好的回复                  │                   │
│  │  训练奖励模型: 学习人类偏好                 │                   │
│  │  数据: ~50K-500K 条偏好对                   │                   │
│  └──────────────────────────────────────────┘                   │
│                          │                                      │
│                          ▼                                      │
│  阶段 3: RL (Reinforcement Learning with PPO)                    │
│  ┌──────────────────────────────────────────┐                   │
│  │  用奖励模型的信号训练 SFT 模型:             │                   │
│  │    SFT 模型生成回复                         │                   │
│  │    奖励模型打分                             │                   │
│  │    PPO 算法更新 SFT 模型参数                │                   │
│  │  约束: KL 散度防止偏离参考模型太远           │                   │
│  └──────────────────────────────────────────┘                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 奖励模型训练

### 偏好数据格式

```python
"""奖励模型训练数据格式"""

# 偏好数据格式 (每条包含一个 prompt + chosen/rejected)
preference_data = {
    "prompt": "解释什么是量子计算",
    "chosen": "量子计算是利用量子力学原理进行计算的新型计算范式...",  # 人类偏好
    "rejected": "量子计算就是很快的计算机，比普通计算机快100万倍...",  # 被拒绝
}

# 奖励模型架构: 在 LLM 基础上加一个标量输出头
# Loss: L = -log(σ(r(chosen) - r(rejected)))
# 即: 让 chosen 的奖励分数高于 rejected
```

### 奖励模型训练代码

```python
"""使用 TRL 训练奖励模型"""
from trl import RewardTrainer, RewardConfig
from transformers import AutoTokenizer, AutoModelForSequenceClassification
from datasets import load_dataset

# 加载基础模型（通常是 SFT 模型）
model = AutoModelForSequenceClassification.from_pretrained(
    "meta-llama/Llama-3.1-8B-Instruct",
    num_labels=1,  # 标量奖励输出
    torch_dtype="bfloat16",
)
tokenizer = AutoTokenizer.from_pretrained("meta-llama/Llama-3.1-8B-Instruct")

# 加载偏好数据
dataset = load_dataset("Anthropic/hh-rlhf")

# 训练配置
config = RewardConfig(
    output_dir="./reward_model",
    per_device_train_batch_size=4,
    num_train_epochs=1,
    learning_rate=1e-5,
    bf16=True,
    max_length=2048,
)

trainer = RewardTrainer(
    model=model,
    tokenizer=tokenizer,
    args=config,
    train_dataset=dataset["train"],
    eval_dataset=dataset["test"],
)

trainer.train()
```

---

## PPO 训练

```
PPO (Proximal Policy Optimization) 在 RLHF 中:

  参与的模型:
  ┌──────────────────────────────────────────────┐
  │  Actor (π_θ):    被训练的策略模型              │
  │  Reference (π_ref): 参考模型（SFT 模型冻结）   │
  │  Reward (r_φ):   奖励模型（冻结）              │
  │  Critic (V_ψ):   价值网络（评估状态价值）      │
  └──────────────────────────────────────────────┘

  一个训练 step:
    1. 采样 prompt batch
    2. Actor 生成回复
    3. Reward 模型给回复打分
    4. 计算 advantage = reward - V(state)
    5. PPO clipped 目标函数更新 Actor
    6. KL penalty: 防止 Actor 偏离 Reference 太远
       reward_total = reward - β * KL(π_θ || π_ref)

  GPU 资源需求 (70B 模型):
    Actor: 全量参数，需要梯度 → 560 GB (BF16+优化器)
    Reference: 冻结，仅推理 → 140 GB
    Reward: 冻结，仅推理 → 通常用较小模型 ~16 GB
    Critic: 需要梯度 → ~16 GB (通常较小)
    → 总计约需要 256 GPU 做 70B 模型的 RLHF
```

---

## DPO：无需奖励模型的对齐

### DPO 原理

```
DPO (Direct Preference Optimization):

  核心洞察:
    RLHF 的奖励模型隐式定义了一个最优策略
    DPO 直接从偏好数据学习策略，跳过奖励模型

  RLHF 流程:  偏好数据 → 训练 RM → 用 RM 做 RL → 对齐模型
  DPO 流程:   偏好数据 → 直接优化策略 → 对齐模型

  DPO Loss:
    L = -log σ(β × (log π_θ(y_w|x)/π_ref(y_w|x) 
                    - log π_θ(y_l|x)/π_ref(y_l|x)))
    
    y_w = preferred (chosen) response
    y_l = dispreferred (rejected) response
    β = temperature parameter

  优势:
    ✓ 不需要训练奖励模型（省 GPU）
    ✓ 不需要 PPO 的复杂采样循环（更稳定）
    ✓ 实现简单，类似 SFT 的训练流程
    ✓ GPU 需求降低 50-70%

  劣势:
    ✗ 对数据质量更敏感
    ✗ 可能不如 PPO 在困难任务上表现好
    ✗ 缺乏奖励模型的可解释性
```

### DPO 训练代码

```python
"""使用 TRL 进行 DPO 训练"""
from trl import DPOTrainer, DPOConfig
from transformers import AutoTokenizer, AutoModelForCausalLM
from datasets import load_dataset
from peft import LoraConfig

# 加载模型
model = AutoModelForCausalLM.from_pretrained(
    "meta-llama/Llama-3.1-8B-Instruct",
    torch_dtype="bfloat16",
)
tokenizer = AutoTokenizer.from_pretrained("meta-llama/Llama-3.1-8B-Instruct")

# LoRA 配置（减少 GPU 需求）
peft_config = LoraConfig(
    r=16, lora_alpha=32, lora_dropout=0.05,
    target_modules=["q_proj", "v_proj", "k_proj", "o_proj"],
)

# 训练配置
config = DPOConfig(
    output_dir="./dpo_model",
    per_device_train_batch_size=2,
    num_train_epochs=1,
    learning_rate=5e-6,
    beta=0.1,           # DPO temperature
    bf16=True,
    max_length=2048,
    max_prompt_length=1024,
)

trainer = DPOTrainer(
    model=model,
    ref_model=None,       # 使用 LoRA 时自动处理 reference
    args=config,
    train_dataset=dataset["train"],
    tokenizer=tokenizer,
    peft_config=peft_config,
)

trainer.train()
```

---

## 其他偏好优化方法

| 方法 | 需要 RM | 需要参考模型 | 数据格式 | 特点 |
|------|---------|------------|---------|------|
| **PPO (RLHF)** | 是 | 是 | 偏好对 | 最经典，效果好 |
| **DPO** | 否 | 是 | 偏好对 | 简单稳定 |
| **KTO** | 否 | 是 | 单条标注(好/坏) | 不需要成对数据 |
| **IPO** | 否 | 是 | 偏好对 | DPO 改进，更鲁棒 |
| **ORPO** | 否 | 否 | 偏好对 | 不需参考模型 |
| **SimPO** | 否 | 否 | 偏好对 | 简单高效 |
| **RLAIF** | AI 生成 | 是 | AI 标注偏好 | AI 替代人类标注 |

---

## 基础设施需求与框架

### GPU 需求对比

```
不同对齐方法的 GPU 需求 (70B 模型):

  RLHF (PPO):
    Actor (70B, 训练): ~128 GPU
    Reference (70B, 推理): ~32 GPU
    Reward Model (8B): ~4 GPU
    Critic (8B, 训练): ~4 GPU
    生成采样: ~32 GPU
    总计: ~200+ GPU

  DPO:
    Model (70B, 训练): ~128 GPU
    Reference (70B, 推理): ~32 GPU (或用 LoRA 省去)
    总计: ~128-160 GPU

  DPO + LoRA:
    Model (70B, LoRA 训练): ~16-32 GPU
    总计: ~16-32 GPU ← 最节省资源
```

### 训练框架

```
主流 RLHF/DPO 框架对比:

  TRL (HuggingFace):
    ✓ 最广泛使用，社区活跃
    ✓ 支持 PPO, DPO, KTO, ORPO 等
    ✓ 与 HuggingFace 生态深度集成
    pip install trl

  OpenRLHF:
    ✓ 专注大规模 RLHF 训练
    ✓ Ray + vLLM 分布式架构
    ✓ 支持 70B+ 模型的 PPO
    github: OpenRLHF/OpenRLHF

  DeepSpeed-Chat:
    ✓ 基于 DeepSpeed 的 RLHF
    ✓ ZeRO 3 支持超大模型
    ✓ 三阶段一体化训练

  LLaMA-Factory:
    ✓ 一站式微调平台
    ✓ 支持 SFT + RLHF + DPO
    ✓ 中文社区活跃
```

---

## 参考资料与引用

1. Ouyang, L., et al. (2022). *Training language models to follow instructions with human feedback* (InstructGPT). arXiv:2203.02155. https://arxiv.org/abs/2203.02155
2. Rafailov, R., et al. (2023). *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*. arXiv:2305.18290. https://arxiv.org/abs/2305.18290
3. Ethayarajh, K., et al. (2024). *KTO: Model Alignment as Prospect Theoretic Optimization*. arXiv:2402.01306. https://arxiv.org/abs/2402.01306
4. Schulman, J., et al. (2017). *Proximal Policy Optimization Algorithms*. arXiv:1707.06347. https://arxiv.org/abs/1707.06347
5. Christiano, P., et al. (2017). *Deep Reinforcement Learning from Human Preferences*. arXiv:1706.03741. https://arxiv.org/abs/1706.03741
6. TRL (Transformer Reinforcement Learning) Documentation. HuggingFace. https://huggingface.co/docs/trl
7. OpenRLHF: Open-Source RLHF Framework. https://github.com/OpenRLHF/OpenRLHF

---

*上一篇：[01-alignment-overview.md](01-alignment-overview.md)* | *下一篇：[03-red-teaming.md](03-red-teaming.md)*

*返回：[README.md](README.md) - 章节索引*
