# 微调平台

> 微调平台就像"一站式健身房"——你不需要自己搭建器材，选好训练计划就能开练。

## 目录

- [微调平台概述](#微调平台概述)
- [Axolotl](#axolotl)
- [LLaMA-Factory](#llama-factory)
- [Unsloth](#unsloth)
- [其他开源工具](#其他开源工具)
- [云上微调服务](#云上微调服务)
- [平台选型指南](#平台选型指南)
- [延伸阅读](#延伸阅读)

---

## 微调平台概述

### 为什么需要微调平台

直接用 Transformers + PEFT 编写微调代码需要处理大量工程细节。微调平台将这些复杂性封装为简单的配置文件：

```
手动编码 vs 微调平台

手动编码（~200 行代码）：              微调平台（一个 YAML 文件）：
├── 模型加载与量化配置                 ┌─────────────────────────┐
├── 数据加载与格式转换                 │ model: llama-3.1-8b     │
├── Chat Template 处理                │ method: qlora            │
├── LoRA/QLoRA 配置                   │ dataset: my-data         │
├── 训练参数设置                      │ epochs: 3                │
├── 分布式训练配置                    │ lr: 2e-4                 │
├── 梯度检查点                       └─────────────────────────┘
├── 日志与监控                        
├── 模型保存与合并                     → 一条命令启动训练
└── 评估与推理
```

### 主要平台对比

| 平台 | 定位 | 优势 | 劣势 |
|------|------|------|------|
| Axolotl | 配置化微调 | 灵活强大、社区活跃 | 学习曲线较陡 |
| LLaMA-Factory | 一站式平台 | Web UI、中文友好 | 大规模部署偏弱 |
| Unsloth | 极速微调 | 2x 速度、低显存 | 模型支持有限 |
| AutoTrain | 零代码微调 | 最简单 | 灵活性低 |
| torchtune | PyTorch 原生 | 官方支持、可扩展 | 较新、生态不完善 |

---

## Axolotl

### 简介

Axolotl 是最流行的开源微调框架之一，通过 YAML 配置文件控制微调的所有方面。

### 配置示例

```yaml
# axolotl_config.yml - Llama 3.1 8B QLoRA 微调

# 模型配置
base_model: meta-llama/Llama-3.1-8B-Instruct
model_type: LlamaForCausalLM
tokenizer_type: AutoTokenizer

# 数据配置
datasets:
  - path: tatsu-lab/alpaca
    type: alpaca
  - path: ./my-custom-data.jsonl
    type: sharegpt
    conversation: chatml  # Chat Template

# 量化配置
load_in_4bit: true
adapter: qlora
lora_r: 16
lora_alpha: 32
lora_dropout: 0.05
lora_target_modules:
  - q_proj
  - k_proj
  - v_proj
  - o_proj
  - gate_proj
  - up_proj
  - down_proj
lora_target_linear: true

# 训练配置
sequence_len: 2048
sample_packing: true          # 多样本打包，提高效率
pad_to_sequence_len: true

num_epochs: 3
micro_batch_size: 4
gradient_accumulation_steps: 4
learning_rate: 2e-4
lr_scheduler: cosine
warmup_ratio: 0.03
optimizer: adamw_torch

# 精度与优化
bf16: auto
gradient_checkpointing: true
flash_attention: true

# 日志与保存
output_dir: ./output
logging_steps: 10
save_steps: 200
eval_steps: 200
wandb_project: my-finetune

# DeepSpeed（多卡训练）
deepspeed: deepspeed_configs/zero2.json
```

### 使用方法

```bash
# 安装
pip install axolotl[flash-attn]

# 单卡训练
accelerate launch -m axolotl.cli.train axolotl_config.yml

# 多卡训练
accelerate launch --multi_gpu --num_processes 4 \
  -m axolotl.cli.train axolotl_config.yml

# 推理测试
accelerate launch -m axolotl.cli.inference axolotl_config.yml \
  --lora_model_dir ./output

# 合并 LoRA 权重
python -m axolotl.cli.merge_lora axolotl_config.yml \
  --lora_model_dir ./output
```

### 核心特性

```
Axolotl 核心特性

1. Sample Packing（样本打包）
   ┌─── 普通训练 ─────────────────────────────────┐
   │ [样本1____PAD_PAD] [样本2________PAD_PAD_PAD] │ ← 大量 padding 浪费
   ├─── Sample Packing ──────────────────────────────┤
   │ [样本1____样本2________样本3__] [样本4______]    │ ← 紧密打包
   └───────────────────────────────────────────────────┘
   效果: 训练速度提升 30-50%

2. Flash Attention 2 集成
   • 自动启用（需要安装 flash-attn）
   • 减少显存、加速注意力计算

3. 多数据集混合
   • 支持 Alpaca、ShareGPT、OpenAI 等多种格式
   • 支持多数据集混合训练（按比例采样）

4. DeepSpeed 集成
   • 内置 ZeRO Stage 1/2/3 配置模板
   • 多节点训练支持
```

---

## LLaMA-Factory

### 简介

LLaMA-Factory（又名 LlamaFactory）是一个面向中文用户的一站式微调平台，提供 Web UI 和命令行两种方式。

### Web UI 使用

```bash
# 安装
pip install llamafactory

# 启动 Web UI
llamafactory-cli webui

# 浏览器打开 http://localhost:7860
```

```
LLaMA-Factory Web UI 界面

┌──────────────────────────────────────────────────┐
│  LLaMA-Factory                                    │
├──────────────────────────────────────────────────┤
│                                                    │
│  模型选择: [Llama-3.1-8B ▼]                       │
│  微调方法: [QLoRA ▼]                              │
│  数据集:   [✓] alpaca [✓] my-data                 │
│                                                    │
│  ── 训练参数 ──                                    │
│  学习率: [2e-4]  轮次: [3]  批大小: [4]           │
│  LoRA Rank: [16]  Alpha: [32]                     │
│                                                    │
│  [开始训练]  [预览数据]  [在线对话]                 │
│                                                    │
│  ── 训练日志 ──                                    │
│  Step 10/1000 | Loss: 2.31 | LR: 1.2e-4          │
│  Step 20/1000 | Loss: 1.85 | LR: 1.8e-4          │
│                                                    │
└──────────────────────────────────────────────────┘
```

### 命令行使用

```bash
# 命令行微调
llamafactory-cli train \
  --model_name_or_path meta-llama/Llama-3.1-8B \
  --stage sft \
  --finetuning_type lora \
  --dataset alpaca_en \
  --template llama3 \
  --lora_rank 16 \
  --lora_alpha 32 \
  --lora_target all \
  --output_dir ./output \
  --per_device_train_batch_size 4 \
  --gradient_accumulation_steps 4 \
  --learning_rate 2e-4 \
  --num_train_epochs 3 \
  --bf16 true

# 支持的训练阶段
# --stage sft        监督微调
# --stage dpo        DPO 对齐训练
# --stage ppo        PPO 对齐训练
# --stage kto        KTO 对齐训练
# --stage rm         奖励模型训练
```

### 核心特性

| 特性 | 说明 |
|------|------|
| 100+ 模型支持 | Llama、Qwen、Mistral、Yi、ChatGLM... |
| Web UI | 零代码微调，可视化训练过程 |
| 多阶段训练 | SFT → RM → PPO/DPO 全流程 |
| 数据预览 | 训练前可视化检查数据格式 |
| 在线对话 | 训练后直接在 UI 中测试模型 |
| 模型导出 | LoRA 合并、GGUF 转换一键完成 |

---

## Unsloth

### 简介

Unsloth 通过手写 CUDA Kernel 和内存优化实现 2x 训练加速和 50% 显存节省。

### 核心优势

```
Unsloth 性能对比

训练速度（tokens/sec，7B 模型，A100）:
┌──────────────────────────────────────────────┐
│ HuggingFace + PEFT:  ████████████  3200      │
│ Unsloth:             ████████████████████████ 6400  │ ← 2x 加速
│ Unsloth + 4bit:      ██████████████████████   5800  │
└──────────────────────────────────────────────┘

显存使用（7B 模型 QLoRA）:
┌──────────────────────────────────────────────┐
│ HuggingFace:  ████████████████████  18 GB    │
│ Unsloth:      ██████████           9 GB      │ ← 50% 节省
└──────────────────────────────────────────────┘
```

### 使用示例

```python
from unsloth import FastLanguageModel
import torch

# 1. 加载模型（自动优化）
model, tokenizer = FastLanguageModel.from_pretrained(
    model_name="unsloth/Llama-3.1-8B-bnb-4bit",  # 预量化版本
    max_seq_length=2048,
    dtype=None,             # 自动检测
    load_in_4bit=True,
)

# 2. 添加 LoRA（Unsloth 优化版）
model = FastLanguageModel.get_peft_model(
    model,
    r=16,
    target_modules=["q_proj", "k_proj", "v_proj", "o_proj",
                     "gate_proj", "up_proj", "down_proj"],
    lora_alpha=16,
    lora_dropout=0,         # Unsloth 推荐 0
    bias="none",
    use_gradient_checkpointing="unsloth",  # Unsloth 优化版
)

# 3. 训练（使用 TRL SFTTrainer）
from trl import SFTTrainer, SFTConfig

trainer = SFTTrainer(
    model=model,
    tokenizer=tokenizer,
    train_dataset=dataset,
    args=SFTConfig(
        output_dir="./output",
        per_device_train_batch_size=4,
        gradient_accumulation_steps=4,
        num_train_epochs=3,
        learning_rate=2e-4,
        bf16=True,
        max_seq_length=2048,
    ),
)
trainer.train()

# 4. 保存（多种格式）
model.save_pretrained_merged("./merged-model", tokenizer)     # 合并后保存
model.save_pretrained_gguf("./gguf-model", tokenizer)         # GGUF 格式
model.push_to_hub_merged("username/my-model", tokenizer)      # 上传 HF Hub
```

### Unsloth 优化原理

```
Unsloth 的优化手段

1. 手写 Triton Kernel
   ├── 优化 LoRA 的前向/反向传播
   ├── 融合 QKV 投影计算
   └── 减少内存拷贝

2. 智能内存管理
   ├── 梯度检查点优化
   ├── 减少中间激活值的存储
   └── 更高效的 4-bit 反量化

3. 编译器优化
   ├── torch.compile 集成
   └── 自动选择最优 kernel
```

---

## 其他开源工具

### torchtune (PyTorch 官方)

```bash
# 安装
pip install torchtune

# 下载模型
tune download meta-llama/Llama-3.1-8B-Instruct --output-dir ./model

# 使用内置配方微调
tune run lora_finetune_single_device \
  --config llama3_1/8B_lora_single_device.yaml
```

### AutoTrain (HuggingFace)

```bash
# 零代码微调
autotrain llm \
  --train \
  --model meta-llama/Llama-3.1-8B \
  --data-path ./my-data \
  --text-column text \
  --lr 2e-4 \
  --batch-size 4 \
  --epochs 3 \
  --trainer sft \
  --peft \
  --quantization int4
```

### 工具对比表

| 特性 | Axolotl | LLaMA-Factory | Unsloth | torchtune | AutoTrain |
|------|---------|---------------|---------|-----------|-----------|
| 配置方式 | YAML | YAML/UI/CLI | Python | YAML | CLI/UI |
| Web UI | ❌ | ✅ | ❌ | ❌ | ✅ |
| 速度优化 | ⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| DPO/RLHF | ✅ | ✅ | ✅(DPO) | ✅(DPO) | ❌ |
| 多卡支持 | ✅ | ✅ | ❌(单卡) | ✅ | ✅ |
| 学习曲线 | 中 | 低 | 低 | 中 | 最低 |
| 社区活跃度 | 高 | 高 | 高 | 中 | 中 |

---

## 云上微调服务

### 主要云服务对比

| 服务 | 提供商 | 定价模型 | 特点 |
|------|--------|---------|------|
| SageMaker | AWS | 按 GPU 实例时 | 功能最全、生态完善 |
| Vertex AI | Google | 按 GPU 时间 | TPU 支持、AutoML |
| Azure ML | Microsoft | 按计算时间 | OpenAI 集成 |
| Together AI | Together | 按 token | 最简单、API 微调 |
| Anyscale | Anyscale | 按 GPU 时间 | Ray 生态 |
| Lambda Labs | Lambda | 按 GPU 时间 | 性价比高 |
| Modal | Modal | 按 GPU 秒 | Serverless GPU |

### API 微调示例（Together AI）

```python
import together

# 上传训练数据
file_id = together.Files.upload(file="train.jsonl")

# 创建微调任务
response = together.Fine_tuning.create(
    training_file=file_id,
    model="meta-llama/Llama-3.1-8B-Instruct",
    n_epochs=3,
    learning_rate=2e-5,
    batch_size=32,
    suffix="my-custom-model",
)

# 查看训练状态
status = together.Fine_tuning.retrieve(response.id)
print(f"Status: {status.status}, Progress: {status.training_progress}")

# 使用微调后的模型
output = together.Complete.create(
    model=f"my-org/Llama-3.1-8B-Instruct-my-custom-model",
    prompt="你好",
)
```

---

## 平台选型指南

```
微调平台选型决策树

你的情况是？
│
├── 没有 GPU，不想管基础设施
│   └── 云上微调服务（Together AI / AWS SageMaker）
│
├── 有 GPU，想快速上手
│   ├── 有编程经验？
│   │   ├── 想要最快速度 → Unsloth
│   │   └── 想要最大灵活性 → Axolotl
│   └── 偏好可视化界面 → LLaMA-Factory
│
├── 需要 DPO/RLHF 对齐训练
│   ├── 模型 < 70B → TRL + Axolotl
│   └── 模型 ≥ 70B → OpenRLHF
│
├── 企业生产环境
│   ├── 已有 PyTorch 基础设施 → torchtune
│   ├── 需要端到端 MLOps → AWS SageMaker
│   └── 需要灵活扩展 → Axolotl + 自定义
│
└── 教学/研究
    └── LLaMA-Factory（Web UI 易于演示）
```

---

## 延伸阅读

- [Axolotl GitHub](https://github.com/OpenAccess-AI-Collective/axolotl) - 配置化微调框架
- [LLaMA-Factory GitHub](https://github.com/hiyouga/LLaMA-Factory) - 一站式微调平台
- [Unsloth GitHub](https://github.com/unslothai/unsloth) - 2x 加速微调
- [torchtune GitHub](https://github.com/pytorch/torchtune) - PyTorch 官方微调工具
- [AutoTrain Documentation](https://huggingface.co/docs/autotrain) - 零代码微调
- [Together AI Fine-tuning](https://docs.together.ai/docs/fine-tuning) - API 微调服务

---

*上一篇：[04-alignment-training.md](04-alignment-training.md)* | *下一篇：[06-finetuning-best-practices.md](06-finetuning-best-practices.md)*

[返回目录](README.md) | [返回主页](../README.md)
