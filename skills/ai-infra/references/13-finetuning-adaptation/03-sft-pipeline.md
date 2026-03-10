# SFT 流程

> 监督微调（SFT）就像给实习医生安排"标准病例训练"——通过大量优质的问答示范，让模型学会正确的回答方式。

## 目录

- [SFT 概述](#sft-概述)
- [数据准备](#数据准备)
- [Chat Template](#chat-template)
- [训练配置](#训练配置)
- [训练实战](#训练实战)
- [评估方法](#评估方法)
- [常见问题](#常见问题)
- [延伸阅读](#延伸阅读)

---

## SFT 概述

### 什么是 SFT

监督微调（Supervised Fine-Tuning）是将预训练语言模型转变为对话助手的关键步骤。通过在高质量的指令-回复数据对上训练，让模型学会：

```
预训练模型 → SFT → 对话模型

预训练模型的行为：
  输入: "什么是光合作用？"
  输出: "什么是细胞分裂？什么是DNA复制？"  ← 续写，非回答

SFT 后的行为：
  输入: "什么是光合作用？"
  输出: "光合作用是植物利用光能将CO₂和水转化为..."  ← 正确回答
```

### SFT 在训练流程中的位置

```
大模型训练三阶段

Stage 1: 预训练 (Pre-training)
  ├── 数据：万亿 token 无标注文本
  ├── 目标：next-token prediction
  ├── 资源：数千 GPU × 数月
  └── 结果：通用语言模型（Base Model）

Stage 2: 监督微调 (SFT) ⭐ ← 本章重点
  ├── 数据：数千-数万条指令数据
  ├── 目标：学会遵循指令、对话
  ├── 资源：数张-数十张 GPU × 数小时-数天
  └── 结果：指令遵循模型（Chat Model）

Stage 3: 对齐训练 (Alignment)
  ├── RLHF / DPO / KTO
  ├── 目标：符合人类偏好、安全
  ├── 资源：中等
  └── 结果：对齐模型（Aligned Model）
```

---

## 数据准备

### 数据格式

```python
# 格式 1: Alpaca 格式（最常见的指令微调格式）
alpaca_sample = {
    "instruction": "请解释什么是机器学习",
    "input": "",  # 可选的额外输入
    "output": "机器学习是人工智能的一个分支，它让计算机能够通过数据和经验自动改进性能..."
}

# 格式 2: ShareGPT 格式（多轮对话）
sharegpt_sample = {
    "conversations": [
        {"from": "human", "value": "你好，请介绍一下你自己"},
        {"from": "gpt", "value": "你好！我是一个AI助手..."},
        {"from": "human", "value": "你能帮我写代码吗？"},
        {"from": "gpt", "value": "当然可以！请告诉我你需要什么..."}
    ]
}

# 格式 3: OpenAI Messages 格式
openai_sample = {
    "messages": [
        {"role": "system", "content": "你是一个有用的助手"},
        {"role": "user", "content": "解释量子纠缠"},
        {"role": "assistant", "content": "量子纠缠是量子力学中..."}
    ]
}
```

### 数据质量原则

```
LIMA 论则：质量 > 数量

                    性能
                     ↑
                     │          ┌─── 高质量 1000 条
                     │         /
                     │        /
                     │       /    ┌─── 低质量 50000 条
                     │      /   /
                     │     /   /
                     │    /   /
                     │   /   /
                     │  /   /
                     │ /   /
                     └──────────────→ 数据量
                     
关键发现（LIMA 论文）：
  1000 条高质量数据 ≈ 50000 条低质量数据
```

### 数据构建指南

```python
class SFTDataBuilder:
    """SFT 数据构建器"""
    
    def __init__(self):
        self.quality_criteria = {
            "准确性": "答案必须事实正确",
            "完整性": "回答要覆盖问题的各个方面",
            "格式规范": "遵循一致的输出格式",
            "适当长度": "不过于简略也不过于冗长",
            "安全性": "不包含有害内容",
        }
    
    def validate_sample(self, sample: dict) -> dict:
        """验证单条数据的质量"""
        issues = []
        
        # 长度检查
        if len(sample.get("output", "")) < 20:
            issues.append("回答过短")
        if len(sample.get("output", "")) > 4096:
            issues.append("回答过长，考虑精简")
        
        # 指令检查
        if len(sample.get("instruction", "")) < 5:
            issues.append("指令过于简短")
        
        # 重复检查
        output = sample.get("output", "")
        sentences = output.split("。")
        unique_ratio = len(set(sentences)) / max(len(sentences), 1)
        if unique_ratio < 0.7:
            issues.append("回答中存在大量重复内容")
        
        return {"valid": len(issues) == 0, "issues": issues}
    
    def build_diverse_dataset(self, raw_data: list) -> list:
        """构建多样化数据集"""
        # 任务类型分布建议
        task_distribution = {
            "知识问答": 0.25,
            "创意写作": 0.15,
            "代码生成": 0.15,
            "逻辑推理": 0.15,
            "摘要翻译": 0.10,
            "对话闲聊": 0.10,
            "格式化输出": 0.10,
        }
        return self._balance_by_category(raw_data, task_distribution)
```

### 开源数据集推荐

| 数据集 | 语言 | 数据量 | 特点 |
|--------|------|--------|------|
| OpenAssistant (OASST) | 多语言 | 160K | 人工标注多轮对话 |
| Alpaca-52K | 英文 | 52K | GPT-4 生成指令数据 |
| ShareGPT | 多语言 | 70K+ | ChatGPT 对话收集 |
| BELLE | 中文 | 1M+ | 中文指令数据 |
| Firefly | 中文 | 1.6M | 多任务中文指令 |
| UltraChat | 英文 | 1.5M | 大规模多轮对话 |
| OpenHermes-2.5 | 英文 | 1M | 高质量合成数据 |
| Infinity-Instruct | 多语言 | 10M+ | 超大规模指令集 |

---

## Chat Template

### 为什么需要 Chat Template

Chat Template 定义了系统消息、用户输入和模型回复的格式标记，不同模型使用不同的模板。**使用错误的模板是微调失败的最常见原因之一。**

### 主流模型的 Chat Template

```
Llama 3 / 3.1 Template:
<|begin_of_text|><|start_header_id|>system<|end_header_id|>

你是一个有用的助手。<|eot_id|><|start_header_id|>user<|end_header_id|>

你好<|eot_id|><|start_header_id|>assistant<|end_header_id|>

你好！有什么可以帮你的吗？<|eot_id|>

─────────────────────────────────────────

ChatML Template (Qwen / Yi / Mistral):
<|im_start|>system
你是一个有用的助手。<|im_end|>
<|im_start|>user
你好<|im_end|>
<|im_start|>assistant
你好！有什么可以帮你的吗？<|im_end|>

─────────────────────────────────────────

Gemma Template:
<start_of_turn>user
你好<end_of_turn>
<start_of_turn>model
你好！有什么可以帮你的吗？<end_of_turn>
```

### 使用 Tokenizer 的 Chat Template

```python
from transformers import AutoTokenizer

tokenizer = AutoTokenizer.from_pretrained("meta-llama/Llama-3.1-8B-Instruct")

messages = [
    {"role": "system", "content": "你是一个专业的编程助手。"},
    {"role": "user", "content": "写一个快速排序"},
    {"role": "assistant", "content": "好的，以下是 Python 快速排序的实现：\n```python\ndef quicksort(arr):\n    ...```"},
]

# 自动应用模型对应的 Chat Template
formatted = tokenizer.apply_chat_template(
    messages,
    tokenize=False,
    add_generation_prompt=True,  # 添加 assistant 的起始标记
)
print(formatted)

# 关键：训练时的 Label Masking
# 只对 assistant 的回复计算 loss，system 和 user 的部分被 mask
tokenized = tokenizer.apply_chat_template(
    messages,
    tokenize=True,
    return_dict=True,
)
```

---

## 训练配置

### 关键超参数

```python
from transformers import TrainingArguments

training_args = TrainingArguments(
    # === 基础配置 ===
    output_dir="./output",
    num_train_epochs=3,              # 轮次：通常 1-5
    
    # === 批大小 ===
    per_device_train_batch_size=4,   # 每 GPU 批大小
    gradient_accumulation_steps=4,   # 梯度累积步数
    # 有效批大小 = 4 × 4 × num_gpus
    
    # === 学习率 ===
    learning_rate=2e-4,              # LoRA 推荐 1e-4 ~ 3e-4
    lr_scheduler_type="cosine",      # 余弦退火
    warmup_ratio=0.03,               # 预热比例
    
    # === 精度与优化 ===
    bf16=True,                       # 使用 BF16（A100/H100）
    optim="adamw_torch",             # 优化器
    weight_decay=0.01,               # 权重衰减
    max_grad_norm=1.0,               # 梯度裁剪
    
    # === 序列长度 ===
    # max_seq_length=2048,           # 在 SFTTrainer 中设置
    
    # === 保存与日志 ===
    save_strategy="steps",
    save_steps=200,
    logging_steps=10,
    eval_strategy="steps",
    eval_steps=200,
    
    # === 资源优化 ===
    gradient_checkpointing=True,     # 显存不足时开启
    dataloader_num_workers=4,
)
```

### 超参数推荐

```
超参数速查表

┌─────────────────┬──────────────┬───────────────┬──────────────┐
│ 参数            │ 全量微调      │ LoRA          │ QLoRA        │
├─────────────────┼──────────────┼───────────────┼──────────────┤
│ 学习率          │ 1e-5 ~ 5e-5  │ 1e-4 ~ 3e-4   │ 1e-4 ~ 2e-4  │
│ 轮次            │ 1-3          │ 2-5           │ 2-5          │
│ 批大小          │ 128-512      │ 32-128        │ 16-64        │
│ 序列长度        │ 2048-4096    │ 2048-4096     │ 1024-2048    │
│ 预热            │ 3-5%         │ 3-10%         │ 3-10%        │
│ 调度器          │ cosine       │ cosine        │ cosine       │
│ 权重衰减        │ 0.01-0.1     │ 0.01          │ 0.01         │
│ 梯度裁剪        │ 1.0          │ 1.0           │ 1.0          │
└─────────────────┴──────────────┴───────────────┴──────────────┘
```

---

## 训练实战

### 使用 TRL SFTTrainer

```python
from trl import SFTTrainer, SFTConfig
from datasets import load_dataset
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import LoraConfig

# 1. 加载模型和分词器
model_name = "meta-llama/Llama-3.1-8B"
model = AutoModelForCausalLM.from_pretrained(model_name, torch_dtype=torch.bfloat16)
tokenizer = AutoTokenizer.from_pretrained(model_name)
tokenizer.pad_token = tokenizer.eos_token

# 2. 加载数据集
dataset = load_dataset("tatsu-lab/alpaca", split="train")

# 3. 数据格式化函数
def format_alpaca(example):
    """将 Alpaca 格式转换为对话格式"""
    if example["input"]:
        instruction = f"{example['instruction']}\n\n输入：{example['input']}"
    else:
        instruction = example["instruction"]
    
    return {
        "messages": [
            {"role": "user", "content": instruction},
            {"role": "assistant", "content": example["output"]},
        ]
    }

dataset = dataset.map(format_alpaca)

# 4. LoRA 配置
peft_config = LoraConfig(
    r=16,
    lora_alpha=32,
    target_modules=["q_proj", "k_proj", "v_proj", "o_proj",
                     "gate_proj", "up_proj", "down_proj"],
    lora_dropout=0.05,
    task_type="CAUSAL_LM",
)

# 5. 训练配置
sft_config = SFTConfig(
    output_dir="./sft-llama3-8b",
    max_seq_length=2048,
    num_train_epochs=3,
    per_device_train_batch_size=4,
    gradient_accumulation_steps=4,
    learning_rate=2e-4,
    lr_scheduler_type="cosine",
    warmup_ratio=0.03,
    bf16=True,
    logging_steps=10,
    save_steps=200,
    eval_strategy="steps",
    eval_steps=200,
    gradient_checkpointing=True,
)

# 6. 初始化 Trainer
trainer = SFTTrainer(
    model=model,
    args=sft_config,
    train_dataset=dataset,
    tokenizer=tokenizer,
    peft_config=peft_config,
)

# 7. 开始训练
trainer.train()

# 8. 保存模型
trainer.save_model("./sft-llama3-8b-final")
```

### 多轮对话微调

```python
# 多轮对话数据处理
def format_multi_turn(example):
    """处理多轮对话数据"""
    messages = []
    
    # 添加系统消息
    if "system" in example:
        messages.append({"role": "system", "content": example["system"]})
    
    # 添加对话轮次
    for conv in example["conversations"]:
        role = "user" if conv["from"] == "human" else "assistant"
        messages.append({"role": role, "content": conv["value"]})
    
    return {"messages": messages}

# 关键：只对 assistant 回复计算 loss
# TRL 的 SFTTrainer 在使用 messages 格式时自动处理这一点
# 通过 tokenizer.apply_chat_template 的 return_assistant_tokens_mask
```

---

## 评估方法

### 评估维度

```
SFT 模型评估框架

┌────────────────────────────────────────────────────┐
│                    评估维度                          │
├──────────────┬──────────────┬───────────────────────┤
│  自动评估     │  LLM 评估    │  人工评估              │
├──────────────┼──────────────┼───────────────────────┤
│ • MMLU       │ • MT-Bench   │ • Elo 评分            │
│ • GSM8K      │ • AlpacaEval │ • A/B 测试            │
│ • HumanEval  │ • Arena Hard │ • 标注员评分           │
│ • TruthfulQA │ • WildBench  │ • 领域专家审核         │
│ • ARC        │              │                       │
│ • HellaSwag  │ GPT-4 作为   │  黄金标准但成本高      │
│              │ 评判者        │                       │
└──────────────┴──────────────┴───────────────────────┘
```

### 自动评估实践

```python
import lm_eval

# 使用 lm-evaluation-harness 进行基准评估
results = lm_eval.simple_evaluate(
    model="hf",
    model_args="pretrained=./sft-llama3-8b-final",
    tasks=["mmlu", "gsm8k", "hellaswag", "truthfulqa"],
    batch_size=8,
    device="cuda",
)

# 输出结果
for task, metrics in results["results"].items():
    print(f"{task}: {metrics.get('acc_norm,none', metrics.get('acc,none', 'N/A'))}")
```

### MT-Bench 评估

```python
# MT-Bench: 使用 GPT-4 对模型的多轮对话能力打分（1-10）

# 1. 生成回答
# python gen_model_answer.py --model-path ./sft-model --model-id my-sft-model

# 2. GPT-4 评分
# python gen_judgment.py --model-list my-sft-model

# 3. 查看结果
# python show_result.py

# 评分标准（示例）：
#   Writing:        创意写作、邮件撰写
#   Roleplay:       角色扮演
#   Reasoning:      逻辑推理
#   Math:           数学计算
#   Coding:         编程能力
#   Extraction:     信息提取
#   STEM:           科学技术
#   Humanities:     人文社科
```

### 评估检查清单

```
SFT 模型上线前检查清单

□ 基准测试不低于基座模型（防止灾难性遗忘）
□ 目标任务指标达到预期
□ MT-Bench 评分 ≥ 7.0（对话能力）
□ 安全性测试通过（无有害输出）
□ 多样性测试（不同类型的指令都能正确处理）
□ 边缘案例测试（空输入、超长输入、对抗输入）
□ 推理延迟符合 SLO 要求
□ A/B 测试验证用户满意度
```

---

## 常见问题

### 问题诊断表

| 现象 | 可能原因 | 解决方案 |
|------|---------|---------|
| Loss 不下降 | 学习率太低/数据格式错误 | 检查数据格式，提高学习率 |
| Loss 快速归零 | 数据泄漏/训练集太小 | 检查是否 label 包含 input |
| 输出重复 | 温度太低/训练过度 | 增大 temperature，减少 epoch |
| 忘记原有能力 | 过拟合/学习率太高 | 降低学习率，混入通用数据 |
| Chat Template 错误 | 使用了错误的模板 | 用 tokenizer.chat_template 验证 |
| 中文乱码 | tokenizer 不匹配 | 确认模型支持中文 |

### Loss 曲线诊断

```
健康的训练 Loss 曲线：

Loss ↑
  3.0│\
     │ \
  2.0│  \
     │   \___
  1.0│       \____
     │            \________
  0.5│                     \_________
     └─────────────────────────────→ Steps

异常模式：
  锯齿形 → 学习率太大
  平坦不降 → 学习率太小或数据有问题
  快速归零 → 数据泄漏
  先降后升 → 过拟合，需要早停
```

---

## 参考资料与引用

1. Zhou, C., et al. (2023). *LIMA: Less Is More for Alignment*. arXiv:2305.11206. https://arxiv.org/abs/2305.11206
2. Liu, W., et al. (2023). *Deita: What Makes Good Data for Alignment: A Comprehensive Study of Automatic Data Selection in Instruction Tuning*. arXiv:2312.15685. https://arxiv.org/abs/2312.15685
3. Köpf, A., et al. (2023). *OpenAssistant Conversations - Democratizing Large Language Model Alignment*. arXiv:2304.07327. https://arxiv.org/abs/2304.07327
4. TRL (Transformer Reinforcement Learning) - SFTTrainer Documentation. HuggingFace. https://huggingface.co/docs/trl
5. Alignment Handbook - LLM Training Recipes. HuggingFace. https://github.com/huggingface/alignment-handbook
6. OpenAssistant Dataset (oasst2). https://huggingface.co/datasets/OpenAssistant/oasst2

---

*上一篇：[02-lora-family.md](02-lora-family.md)* | *下一篇：[04-alignment-training.md](04-alignment-training.md)*

[返回目录](README.md) | [返回主页](../README.md)
