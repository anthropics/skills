# LoRA 家族

> LoRA 就像给大模型戴上一副"专业眼镜"——不改变大脑的结构，只通过一副轻量化的"镜片"让它看到特定领域的细节。

## 目录

- [LoRA 原理](#lora-原理)
- [LoRA 的关键超参数](#lora-的关键超参数)
- [QLoRA：量化 + LoRA](#qlora量化--lora)
- [DoRA：权重分解适配](#dora权重分解适配)
- [LoRA+ 与其他变体](#lora-与其他变体)
- [适配器合并策略](#适配器合并策略)
- [LoRA 实战指南](#lora-实战指南)
- [延伸阅读](#延伸阅读)

---

## LoRA 原理

### 核心思想：低秩分解

LoRA（Low-Rank Adaptation）的核心洞察：**模型微调时的权重变化矩阵是低秩的**，即可以用两个小矩阵的乘积来近似。

```
传统全量微调 vs LoRA

全量微调:                          LoRA:
┌─────────────────┐               ┌─────────────────┐
│                 │               │                 │
│   W₀ + ΔW      │               │   W₀ (冻结)     │ ← 原始权重不更新
│                 │               │                 │
│  d×d 参数全更新  │               │   + B × A       │ ← 低秩适配器
│                 │               │   (d×r)(r×d)    │
└─────────────────┘               └─────────────────┘

参数量: d × d                     参数量: 2 × d × r (r << d)

例如 d=4096, r=16:
全量: 4096 × 4096 = 16,777,216    LoRA: 2 × 4096 × 16 = 131,072
                                   压缩比: 128x
```

### 数学表达

```
原始前向传播:  h = W₀ · x

LoRA 前向传播: h = W₀ · x + (B · A) · x · (α/r)

其中:
  W₀ ∈ R^{d×k}   — 预训练权重（冻结）
  A  ∈ R^{r×k}   — 下投影矩阵（随机初始化）
  B  ∈ R^{d×r}   — 上投影矩阵（零初始化）
  r              — 秩（rank），通常 4-64
  α              — 缩放因子，控制适配强度
  α/r            — 实际缩放比例
```

### 为什么有效？

```
直觉理解：

预训练模型的权重空间
┌─────────────────────────────────────┐
│                                     │
│   完整权重空间（数百万维）            │
│                                     │
│   ┌───────────────────┐            │
│   │ 任务相关的变化     │            │
│   │ （低秩子空间）     │ ← LoRA 只  │
│   │                   │    适配这里  │
│   └───────────────────┘            │
│                                     │
│   Aghajanyan et al. (2020) 证明：   │
│   预训练模型有非常低的"内在维度"     │
│   (intrinsic dimensionality)       │
│                                     │
└─────────────────────────────────────┘
```

### PyTorch 实现示例

```python
import torch
import torch.nn as nn

class LoRALinear(nn.Module):
    """LoRA 适配的线性层"""
    
    def __init__(
        self,
        original_linear: nn.Linear,
        rank: int = 16,
        alpha: float = 32,
        dropout: float = 0.05,
    ):
        super().__init__()
        self.original = original_linear
        self.rank = rank
        self.alpha = alpha
        self.scaling = alpha / rank
        
        in_features = original_linear.in_features
        out_features = original_linear.out_features
        
        # 冻结原始权重
        self.original.weight.requires_grad = False
        if self.original.bias is not None:
            self.original.bias.requires_grad = False
        
        # LoRA 矩阵
        self.lora_A = nn.Linear(in_features, rank, bias=False)
        self.lora_B = nn.Linear(rank, out_features, bias=False)
        self.lora_dropout = nn.Dropout(dropout)
        
        # 初始化：A 用 Kaiming，B 用零
        nn.init.kaiming_uniform_(self.lora_A.weight)
        nn.init.zeros_(self.lora_B.weight)
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        # 原始路径 + LoRA 路径
        original_output = self.original(x)
        lora_output = self.lora_B(self.lora_A(self.lora_dropout(x)))
        return original_output + lora_output * self.scaling
    
    def merge_weights(self):
        """将 LoRA 权重合并到原始权重中（推理时用）"""
        with torch.no_grad():
            merged = self.lora_B.weight @ self.lora_A.weight * self.scaling
            self.original.weight += merged
```

---

## LoRA 的关键超参数

### 超参数详解

| 超参数 | 说明 | 推荐值 | 影响 |
|--------|------|--------|------|
| `r` (rank) | 低秩矩阵的秩 | 8-64 | 越大参数越多，表达力越强 |
| `alpha` | 缩放因子 | 通常 = 2×r | 控制 LoRA 更新的强度 |
| `dropout` | LoRA 层的 Dropout | 0.0-0.1 | 防止过拟合 |
| `target_modules` | 应用 LoRA 的层 | q_proj, v_proj, ... | 覆盖越多效果越好 |

### rank 的选择指南

```
rank 选择策略

任务复杂度与 rank 的关系:

r=4  ────── 简单任务（格式调整、风格迁移）
r=8  ────── 一般任务（指令遵循、单领域适配）
r=16 ────── 中等任务（多任务、中等领域差异）
r=32 ────── 复杂任务（大领域差异、多语言）
r=64 ────── 极复杂任务（接近全量微调效果）

经验法则：
  • 从 r=16 开始尝试
  • 效果不够 → 增大 r
  • 过拟合 → 减小 r 或增大 dropout
  • alpha 通常设为 2×r
```

### target_modules 选择

```python
# 不同模型架构的推荐 target_modules

# Llama / Qwen / Mistral（推荐：全覆盖注意力 + MLP）
target_modules_full = [
    "q_proj", "k_proj", "v_proj", "o_proj",  # 注意力层
    "gate_proj", "up_proj", "down_proj",       # MLP 层
]

# 轻量版（仅注意力层的 Q 和 V）
target_modules_light = ["q_proj", "v_proj"]

# 效果对比（以 Llama-7B 为例，r=16）
# ┌───────────────────┬──────────────┬───────────────┐
# │ 配置              │ 可训练参数    │ 相对效果       │
# ├───────────────────┼──────────────┼───────────────┤
# │ q, v only         │ ~4M (0.06%)  │ 基准          │
# │ q, k, v, o        │ ~8M (0.12%)  │ +2-5%        │
# │ 全覆盖 (attn+mlp) │ ~20M (0.3%)  │ +5-10%       │
# └───────────────────┴──────────────┴───────────────┘
```

---

## QLoRA：量化 + LoRA

### 核心创新

QLoRA 将基础模型量化到 4-bit，然后在量化模型上应用 LoRA，实现"单卡微调大模型"。

```
QLoRA 的三大创新

1. 4-bit NormalFloat (NF4)
   ┌─────────────────────────────────────┐
   │ 信息论最优的 4-bit 量化格式          │
   │ 假设权重服从正态分布 → 最优量化      │
   │ 比标准 INT4 更精确                  │
   └─────────────────────────────────────┘

2. 双重量化 (Double Quantization)
   ┌─────────────────────────────────────┐
   │ 对量化常数本身再次量化              │
   │ FP32 常数 → 量化为 FP8             │
   │ 额外节省 ~0.4 GB / billion params  │
   └─────────────────────────────────────┘

3. 分页优化器 (Paged Optimizers)
   ┌─────────────────────────────────────┐
   │ GPU 显存不足时自动卸载到 CPU        │
   │ 利用 NVIDIA 统一内存管理            │
   │ 避免 OOM（显存溢出）               │
   └─────────────────────────────────────┘
```

### 显存对比

```
Llama-2-70B 微调显存对比

方法              GPU 需求          总显存
─────────────────────────────────────────
全量微调 FP16    32× A100 80GB    ~2560 GB
LoRA FP16        8× A100 80GB     ~640 GB
QLoRA 4-bit      4× A100 40GB     ~160 GB   ← 16x 节省!
QLoRA 单卡       1× A100 80GB     ~48 GB    ← 单卡可行
```

### QLoRA 使用示例

```python
from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
from peft import LoraConfig, get_peft_model, prepare_model_for_kbit_training

# 1. 4-bit 量化配置
bnb_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_quant_type="nf4",           # NF4 量化
    bnb_4bit_compute_dtype=torch.bfloat16, # 计算用 BF16
    bnb_4bit_use_double_quant=True,       # 双重量化
)

# 2. 加载量化模型
model = AutoModelForCausalLM.from_pretrained(
    "meta-llama/Llama-3.1-8B",
    quantization_config=bnb_config,
    device_map="auto",
)

# 3. 准备模型
model = prepare_model_for_kbit_training(model)

# 4. LoRA 配置
lora_config = LoraConfig(
    r=16,
    lora_alpha=32,
    target_modules=["q_proj", "k_proj", "v_proj", "o_proj",
                     "gate_proj", "up_proj", "down_proj"],
    lora_dropout=0.05,
    bias="none",
    task_type="CAUSAL_LM",
)

# 5. 应用 LoRA
model = get_peft_model(model, lora_config)
model.print_trainable_parameters()
# 输出: trainable params: 20,971,520 || all params: 8,030,261,248 || trainable%: 0.26%
```

---

## DoRA：权重分解适配

### 原理

DoRA（Weight-Decomposed Low-Rank Adaptation）将权重分解为**幅度**和**方向**两个分量，只用 LoRA 适配方向分量。

```
DoRA 的权重分解

传统 LoRA:
  W' = W₀ + BA        （直接加法更新）

DoRA:
  W₀ → 分解为 ||W₀|| · (W₀/||W₀||)
       幅度 m    方向 V

  W' = m · (W₀ + BA) / ||W₀ + BA||
       ↑      ↑
       可学习  LoRA 适配方向

关键优势:
  • 幅度和方向解耦，更精细的控制
  • 更接近全量微调的更新模式
  • 通常比标准 LoRA 效果更好
```

### DoRA vs LoRA 效果对比

| 基准 | LoRA (r=16) | DoRA (r=16) | 全量微调 |
|------|------------|------------|---------|
| MT-Bench | 7.2 | 7.5 | 7.6 |
| MMLU | 62.1 | 63.8 | 64.5 |
| GSM8K | 45.3 | 48.1 | 49.2 |
| HumanEval | 34.8 | 36.5 | 37.2 |

---

## LoRA+ 与其他变体

### LoRA+ ：差异化学习率

```
标准 LoRA:    lr(A) = lr(B) = η
LoRA+:       lr(A) = η,  lr(B) = λ × η   (λ > 1)

理论依据：
  B 矩阵（上投影）的梯度信噪比较低
  给 B 更大的学习率可以加速收敛

推荐设置：λ = 16 （B 的学习率是 A 的 16 倍）
效果：收敛速度提升 2x，最终效果提升 1-2%
```

### 其他重要变体

```
LoRA 变体速查

┌───────────────┬───────────────────────────────────────────────┐
│ 方法          │ 核心改进                                       │
├───────────────┼───────────────────────────────────────────────┤
│ AdaLoRA       │ 自适应分配不同层的 rank                        │
│ rsLoRA        │ 使用 1/√r 而非 α/r 缩放，大 r 更稳定          │
│ LoRA-FA       │ 冻结 A 矩阵，只训练 B（减少一半参数）           │
│ VeRA          │ 共享 A/B，只学习缩放向量（参数极少）            │
│ PiSSA         │ 用 SVD 初始化 A/B 而非随机+零                  │
│ GaLore        │ 梯度低秩投影，全参数训练但低显存                │
│ Spectrum      │ 基于 SNR 选择性冻结层                          │
│ MELoRA        │ 多个小 rank LoRA 的集成                        │
└───────────────┴───────────────────────────────────────────────┘
```

---

## 适配器合并策略

### 为什么需要合并？

```
部署场景：一个基座模型 + 多个 LoRA 适配器

              ┌──── LoRA-医学 ──── 医学问诊服务
              │
基座模型 ─────┼──── LoRA-法律 ──── 法律咨询服务
              │
              └──── LoRA-代码 ──── 编程助手服务

方案 A: 动态切换（运行时）
  • 一个基座模型加载到 GPU
  • 按请求动态切换 LoRA 适配器
  • 切换延迟 < 1ms

方案 B: 合并部署（推理时）
  • 将 LoRA 权重合并到基座模型
  • 消除 LoRA 前向传播的额外计算
  • 每个任务一个完整模型
```

### 合并方法对比

```python
from peft import PeftModel

# 方法 1: 直接合并（最简单）
merged_model = model.merge_and_unload()

# 方法 2: 多适配器加权合并
# 场景：合并医学 LoRA + 通用指令 LoRA
model.load_adapter("medical-lora", adapter_name="medical")
model.load_adapter("instruct-lora", adapter_name="instruct")

# 加权合并
model.add_weighted_adapter(
    adapters=["medical", "instruct"],
    weights=[0.7, 0.3],              # 医学权重更高
    adapter_name="merged",
    combination_type="linear",
)

# 方法 3: TIES 合并（Task-specific TrimElectSign）
model.add_weighted_adapter(
    adapters=["medical", "instruct"],
    weights=[0.7, 0.3],
    adapter_name="merged_ties",
    combination_type="ties",
    density=0.5,  # 保留 50% 最重要的参数
)

# 方法 4: DARE 合并（Drop And REscale）
model.add_weighted_adapter(
    adapters=["medical", "instruct"],
    weights=[1.0, 1.0],
    adapter_name="merged_dare",
    combination_type="dare_ties",
    density=0.3,  # 随机丢弃 70% 参数后重缩放
)
```

### 合并方法对比

| 方法 | 原理 | 优点 | 缺点 |
|------|------|------|------|
| Linear | 加权平均 | 简单直接 | 任务冲突时效果差 |
| TIES | 修剪+选择符号一致的参数 | 减少任务干扰 | 需调 density |
| DARE | 随机丢弃+重缩放 | 保留多样性 | 有随机性 |
| SVD | 对合并后做 SVD 降秩 | 控制模型大小 | 计算开销大 |

---

## LoRA 实战指南

### 常见问题与解决方案

```
问题排查清单

1. 训练 Loss 不下降
   ├── 检查学习率（LoRA 推荐 1e-4 到 2e-4）
   ├── 检查 alpha/r 比值（推荐 2:1）
   ├── 检查 target_modules 是否正确
   └── 尝试增大 rank

2. 过拟合（验证集 Loss 上升）
   ├── 减小 rank
   ├── 增大 dropout（0.05 → 0.1）
   ├── 减少训练轮次
   └── 增加数据量或数据增强

3. 灾难性遗忘
   ├── 减小学习率
   ├── 减小 alpha（降低适配强度）
   ├── 混入通用指令数据（5-10%）
   └── 使用更小的 rank

4. 输出质量差
   ├── 检查数据质量（垃圾进垃圾出）
   ├── 检查 Chat Template 是否匹配
   ├── 验证 tokenizer 和模型一致
   └── 尝试更大的基座模型
```

### 生产部署的 LoRA 管理

```python
class LoRAManager:
    """生产级 LoRA 适配器管理"""
    
    def __init__(self, base_model_path: str):
        self.base_model = AutoModelForCausalLM.from_pretrained(
            base_model_path, device_map="auto"
        )
        self.adapters = {}
        self.active_adapter = None
    
    def register_adapter(self, name: str, path: str, metadata: dict):
        """注册 LoRA 适配器"""
        self.adapters[name] = {
            "path": path,
            "metadata": metadata,  # 版本、训练数据、指标等
            "loaded": False,
        }
    
    def switch_adapter(self, name: str):
        """热切换 LoRA 适配器（< 1ms）"""
        if name not in self.adapters:
            raise ValueError(f"未知适配器: {name}")
        
        if not self.adapters[name]["loaded"]:
            self.base_model.load_adapter(
                self.adapters[name]["path"],
                adapter_name=name,
            )
            self.adapters[name]["loaded"] = True
        
        self.base_model.set_adapter(name)
        self.active_adapter = name
    
    def get_adapter_info(self, name: str) -> dict:
        """获取适配器信息"""
        return self.adapters.get(name, {}).get("metadata", {})
```

---

## 参考资料与引用

1. Hu, E. J., et al. (2021). *LoRA: Low-Rank Adaptation of Large Language Models*. arXiv:2106.09685. https://arxiv.org/abs/2106.09685
2. Dettmers, T., et al. (2023). *QLoRA: Efficient Finetuning of Quantized LLMs*. arXiv:2305.14314. https://arxiv.org/abs/2305.14314
3. Liu, S., et al. (2024). *DoRA: Weight-Decomposed Low-Rank Adaptation*. arXiv:2402.09353. https://arxiv.org/abs/2402.09353
4. Hayou, S., et al. (2024). *LoRA+: Efficient Low Rank Adaptation of Large Models*. arXiv:2402.12354. https://arxiv.org/abs/2402.12354
5. Yadav, P., et al. (2023). *TIES-Merging: Resolving Interference When Merging Models*. arXiv:2306.01708. https://arxiv.org/abs/2306.01708
6. Yu, L., et al. (2023). *Language Model is a Superlativeq Evaluator via DARE*. arXiv:2311.03099. https://arxiv.org/abs/2311.03099
7. PEFT Library Source Code. HuggingFace. https://github.com/huggingface/peft

---

*上一篇：[01-finetuning-overview.md](01-finetuning-overview.md)* | *下一篇：[03-sft-pipeline.md](03-sft-pipeline.md)*

[返回目录](README.md) | [返回主页](../README.md)
