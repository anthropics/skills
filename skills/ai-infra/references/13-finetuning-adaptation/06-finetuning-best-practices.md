# 微调最佳实践

> 微调就像烹饪——食材（数据）、火候（超参数）、时间（轮次）都要恰到好处，否则不是夹生就是糊了。

## 目录

- [数据策略](#数据策略)
- [超参数调优](#超参数调优)
- [过拟合防护](#过拟合防护)
- [灾难性遗忘](#灾难性遗忘)
- [评估与验证](#评估与验证)
- [成本优化](#成本优化)
- [生产级最佳实践清单](#生产级最佳实践清单)
- [延伸阅读](#延伸阅读)

---

## 数据策略

### 数据质量 > 数据数量

```
数据质量对微调效果的影响

关键研究发现:

LIMA (2023):  1000 条精选数据 ≈ 52000 条 GPT 生成数据
Phi-1 (2023): "教科书级"数据 → 1.3B 模型超越 10x 大模型
LESS (2024):  5% 最优数据 ≈ 100% 全量数据

结论: 花在数据质量上的时间，回报远大于增加数据量
```

### 数据质量检查清单

```python
class DataQualityChecker:
    """微调数据质量检查器"""
    
    def check_dataset(self, dataset: list) -> dict:
        """全面检查数据集质量"""
        results = {
            "total_samples": len(dataset),
            "issues": [],
            "stats": {},
        }
        
        # 1. 长度分布检查
        output_lengths = [len(d.get("output", "")) for d in dataset]
        results["stats"]["avg_output_length"] = sum(output_lengths) / len(output_lengths)
        results["stats"]["min_output_length"] = min(output_lengths)
        results["stats"]["max_output_length"] = max(output_lengths)
        
        if results["stats"]["min_output_length"] < 10:
            results["issues"].append("存在过短的回复（<10 字符）")
        
        # 2. 重复检查
        instructions = [d.get("instruction", "") for d in dataset]
        unique_ratio = len(set(instructions)) / len(instructions)
        results["stats"]["unique_instruction_ratio"] = unique_ratio
        if unique_ratio < 0.95:
            results["issues"].append(f"指令重复率过高: {1-unique_ratio:.1%}")
        
        # 3. 任务多样性检查
        # 分类统计（简单启发式）
        task_types = self._classify_tasks(dataset)
        results["stats"]["task_distribution"] = task_types
        
        # 4. 语言一致性检查
        mixed_lang = sum(1 for d in dataset 
                        if self._is_mixed_language(d))
        if mixed_lang > len(dataset) * 0.1:
            results["issues"].append("超过 10% 的数据存在中英混杂")
        
        return results
    
    def _classify_tasks(self, dataset):
        """简单的任务类型分类"""
        categories = {"问答": 0, "生成": 0, "分析": 0, "代码": 0, "其他": 0}
        for d in dataset:
            inst = d.get("instruction", "").lower()
            if any(w in inst for w in ["什么", "为什么", "如何", "解释"]):
                categories["问答"] += 1
            elif any(w in inst for w in ["写", "生成", "创作", "编写"]):
                categories["生成"] += 1
            elif any(w in inst for w in ["分析", "对比", "评估"]):
                categories["分析"] += 1
            elif any(w in inst for w in ["代码", "函数", "程序", "code"]):
                categories["代码"] += 1
            else:
                categories["其他"] += 1
        return categories
```

### 数据准备最佳实践

| 实践 | 说明 | 重要程度 |
|------|------|---------|
| 去重 | 移除重复和近似重复的样本 | ⭐⭐⭐⭐⭐ |
| 去污染 | 确保测试集中的数据不在训练集中 | ⭐⭐⭐⭐⭐ |
| 质量筛选 | 移除低质量、不准确的回复 | ⭐⭐⭐⭐⭐ |
| 任务多样性 | 覆盖多种类型的指令 | ⭐⭐⭐⭐ |
| 长度均衡 | 避免过度倾向于短/长回复 | ⭐⭐⭐ |
| 格式一致 | 统一的 Chat Template 和格式 | ⭐⭐⭐⭐ |
| 混入通用数据 | 防止灾难性遗忘（5-10%） | ⭐⭐⭐⭐ |

---

## 超参数调优

### 学习率选择

```
学习率选择经验法则

方法              推荐学习率范围         起始建议
───────────────────────────────────────────────
全量微调          1e-5 ~ 5e-5          2e-5
LoRA             1e-4 ~ 3e-4          2e-4
QLoRA            1e-4 ~ 2e-4          1e-4
DPO              1e-6 ~ 5e-5          5e-6
PPO (Actor)      5e-7 ~ 1e-5          1e-6

学习率过大的症状:
  • Loss 剧烈波动（锯齿形）
  • 训练后模型输出退化
  • NaN/Inf 出现

学习率过小的症状:
  • Loss 下降极慢
  • 多个 epoch 后效果无明显提升
  • 训练时间浪费
```

### 学习率调度器

```
常用调度器对比

Cosine (推荐):
  lr │\
     │ \
     │  \_____
     │        \___
     └────────────→ steps
  特点: 平滑衰减，末期细粒度优化

Linear:
  lr │\
     │ \
     │  \
     │   \
     └────→ steps
  特点: 简单直接，适合短训练

Cosine with Restarts:
  lr │\  /\  /\
     │ \/  \/  \
     │          \
     └───────────→ steps
  特点: 周期性重启，探索更多解
```

### 批大小与梯度累积

```python
# 有效批大小 = per_device_batch_size × gradient_accumulation × num_gpus

# 场景 1: 单卡 24GB（RTX 4090）
# per_device=2, grad_accum=16 → 有效批大小=32
training_args = TrainingArguments(
    per_device_train_batch_size=2,
    gradient_accumulation_steps=16,
)

# 场景 2: 4× A100 80GB
# per_device=8, grad_accum=4 → 有效批大小=128
training_args = TrainingArguments(
    per_device_train_batch_size=8,
    gradient_accumulation_steps=4,
)

# 经验法则:
#   小数据集 (<5K): 有效批大小 16-32
#   中数据集 (5K-50K): 有效批大小 32-128
#   大数据集 (>50K): 有效批大小 128-512
```

### 超参数搜索策略

```python
# 推荐的超参数搜索顺序

# Step 1: 固定其他参数，搜索学习率
learning_rates = [5e-5, 1e-4, 2e-4, 3e-4, 5e-4]

# Step 2: 确定学习率后，搜索 LoRA rank
lora_ranks = [4, 8, 16, 32, 64]

# Step 3: 确定 rank 后，微调轮次
epochs = [1, 2, 3, 5]

# Step 4: 其他参数微调
# warmup_ratio, weight_decay, dropout

# 提示：使用短训练（100-500 steps）做初步筛选
# 然后用最佳配置做完整训练
```

---

## 过拟合防护

### 过拟合信号检测

```
过拟合的典型信号

Loss 曲线:
     │
Loss │ Train Loss: ───────────── (持续下降)
     │ Eval Loss:  ────────/    (先降后升 ← 过拟合信号！)
     │                   /
     └──────────────────→ Steps

其他过拟合信号:
  □ 模型开始逐字重复训练数据中的回答
  □ 对训练集中的问题回答完美，对新问题表现差
  □ 输出多样性下降（生成内容趋同）
  □ 在基准测试上的分数反而下降
```

### 防过拟合策略

```python
class OverfittingPrevention:
    """过拟合防护策略集"""
    
    strategies = {
        "数据层面": {
            "增加数据量": "最直接有效的方法",
            "数据增强": "同义改写、回译、格式变换",
            "混入通用数据": "5-10% 的通用指令数据",
        },
        "模型层面": {
            "减小 LoRA rank": "r=16 → r=8",
            "增大 dropout": "0.0 → 0.05 → 0.1",
            "减少 target_modules": "全覆盖 → 只 q_proj, v_proj",
        },
        "训练层面": {
            "减少轮次": "3 epochs → 1 epoch",
            "早停法 (Early Stopping)": "验证集 loss 不降则停止",
            "降低学习率": "2e-4 → 1e-4",
            "增大权重衰减": "0.01 → 0.1",
        },
    }

# 早停法实现
from transformers import EarlyStoppingCallback

trainer = SFTTrainer(
    model=model,
    args=TrainingArguments(
        eval_strategy="steps",
        eval_steps=100,
        load_best_model_at_end=True,     # 结束时加载最佳模型
        metric_for_best_model="eval_loss",
        greater_is_better=False,
    ),
    callbacks=[
        EarlyStoppingCallback(
            early_stopping_patience=3,    # 3 次评估不改善则停止
            early_stopping_threshold=0.01, # 改善阈值
        ),
    ],
)
```

---

## 灾难性遗忘

### 什么是灾难性遗忘

```
灾难性遗忘示意

微调前（Base Model）:
  "什么是光合作用？" → "光合作用是植物利用光能..." ✅
  "写首诗"         → "春眠不觉晓，处处闻啼鸟..." ✅
  "1+1=?"         → "2"                          ✅

领域微调后（过度微调）:
  "什么是光合作用？" → "根据我们公司的产品文档..." ❌ ← 遗忘了！
  "写首诗"         → "您好，请问有什么产品需求？"  ❌ ← 遗忘了！
  "1+1=?"         → "请参考我们的FAQ..."          ❌ ← 遗忘了！
```

### 防止灾难性遗忘的策略

| 策略 | 实现方法 | 效果 |
|------|---------|------|
| 使用 LoRA | 只更新少量参数，保留大部分原始能力 | ⭐⭐⭐⭐⭐ |
| 混入通用数据 | 训练数据中加 5-10% 的通用指令 | ⭐⭐⭐⭐ |
| 低学习率 | 使用较小的学习率减少权重变化 | ⭐⭐⭐⭐ |
| 少训练轮次 | 1-2 个 epoch 通常足够 | ⭐⭐⭐ |
| 正则化 | 权重衰减、KL 约束 | ⭐⭐⭐ |
| 课程学习 | 先通用后专业，渐进式训练 | ⭐⭐⭐ |

```python
# 混入通用数据的实现
def create_mixed_dataset(domain_data, general_data, general_ratio=0.1):
    """
    创建混合数据集：领域数据 + 通用数据
    
    Args:
        domain_data: 领域微调数据
        general_data: 通用指令数据（如 Alpaca）
        general_ratio: 通用数据占比（默认 10%）
    """
    num_general = int(len(domain_data) * general_ratio / (1 - general_ratio))
    
    # 从通用数据中随机采样
    import random
    general_sample = random.sample(general_data, min(num_general, len(general_data)))
    
    # 合并并打乱
    mixed = domain_data + general_sample
    random.shuffle(mixed)
    
    print(f"混合数据集: {len(domain_data)} 领域 + {len(general_sample)} 通用 "
          f"= {len(mixed)} 总计 ({len(general_sample)/len(mixed)*100:.1f}% 通用)")
    
    return mixed
```

### 遗忘检测

```python
def detect_catastrophic_forgetting(model, tokenizer, test_cases: list) -> dict:
    """
    检测灾难性遗忘
    
    test_cases: [{"query": "...", "expected_keywords": [...]}]
    """
    results = {"passed": 0, "failed": 0, "details": []}
    
    for case in test_cases:
        response = generate(model, tokenizer, case["query"])
        
        # 检查关键词是否在回复中
        keywords_found = sum(
            1 for kw in case["expected_keywords"]
            if kw.lower() in response.lower()
        )
        passed = keywords_found >= len(case["expected_keywords"]) * 0.5
        
        results["passed" if passed else "failed"] += 1
        results["details"].append({
            "query": case["query"],
            "passed": passed,
            "response_preview": response[:200],
        })
    
    results["retention_rate"] = results["passed"] / len(test_cases)
    return results

# 使用示例
general_tests = [
    {"query": "什么是光合作用？", "expected_keywords": ["植物", "光", "二氧化碳"]},
    {"query": "1+1等于几？", "expected_keywords": ["2"]},
    {"query": "写一首关于春天的诗", "expected_keywords": ["春", "花"]},
    {"query": "翻译：Hello World", "expected_keywords": ["你好", "世界"]},
]

result = detect_catastrophic_forgetting(model, tokenizer, general_tests)
print(f"能力保持率: {result['retention_rate']:.1%}")
# 建议: 保持率 > 90% 视为可接受
```

---

## 评估与验证

### 评估框架

```
微调模型评估的三个层次

Layer 1: 自动基准测试（基础门槛）
┌──────────────────────────────────────┐
│ • MMLU: 通用知识 (≥ base model)      │
│ • GSM8K: 数学推理 (≥ base model)     │
│ • HumanEval: 代码 (≥ base model)     │
│ • 领域特定基准                        │
│                                       │
│ 目标: 确保不低于基座模型              │
└──────────────────────────────────────┘

Layer 2: LLM-as-Judge（快速评估）
┌──────────────────────────────────────┐
│ • MT-Bench: 多轮对话 (目标 ≥ 7.0)    │
│ • AlpacaEval: 指令遵循               │
│ • Arena Hard: 高难度对话              │
│                                       │
│ 目标: 对话能力达到商用水平            │
└──────────────────────────────────────┘

Layer 3: 人工评估（黄金标准）
┌──────────────────────────────────────┐
│ • 领域专家评审                        │
│ • A/B 测试（vs 基座模型）             │
│ • 用户满意度调查                      │
│                                       │
│ 目标: 真实用户场景验证                │
└──────────────────────────────────────┘
```

### 评估脚本示例

```python
def comprehensive_evaluation(model_path: str) -> dict:
    """综合评估微调模型"""
    
    results = {}
    
    # 1. 基准测试（使用 lm-evaluation-harness）
    import subprocess
    benchmarks = ["mmlu", "gsm8k", "hellaswag", "arc_challenge"]
    
    cmd = (f"lm_eval --model hf --model_args pretrained={model_path} "
           f"--tasks {','.join(benchmarks)} --batch_size 8 --output_path ./eval")
    subprocess.run(cmd, shell=True)
    
    # 2. 灾难性遗忘检测
    retention = detect_catastrophic_forgetting(model, tokenizer, general_tests)
    results["retention_rate"] = retention["retention_rate"]
    
    # 3. 领域任务评估
    domain_accuracy = evaluate_domain_tasks(model, tokenizer, domain_test_set)
    results["domain_accuracy"] = domain_accuracy
    
    # 4. 安全性测试
    safety_score = run_safety_tests(model, tokenizer)
    results["safety_score"] = safety_score
    
    # 5. 生成质量
    quality = evaluate_generation_quality(model, tokenizer, quality_test_set)
    results["quality_score"] = quality
    
    return results
```

---

## 成本优化

### 降低微调成本的策略

```
成本优化策略排行

效果     策略                     说明
─────────────────────────────────────────────
⭐⭐⭐⭐⭐  使用 QLoRA              显存降低 4-16x，使用消费级 GPU
⭐⭐⭐⭐⭐  减少数据量              质量优先，1000 条可能就够
⭐⭐⭐⭐   用小模型               7B 通常够用，不要盲目选大模型
⭐⭐⭐⭐   Sample Packing         训练效率提升 30-50%
⭐⭐⭐     Flash Attention        速度 2-4x，显存降低
⭐⭐⭐     Spot/Preemptible GPU   成本降低 60-70%
⭐⭐⭐     短训练 + 早停           避免不必要的训练时间
⭐⭐      梯度检查点              用时间换显存
⭐⭐      混合精度 (BF16)         减少显存、加速计算
```

### 成本对比示例

```
微调 Llama-3.1-8B，10000 条数据，3 epochs

方案 A: 全量微调（A100 80GB × 4）
  GPU 费用: 4 × $2.0/h × 8h = $64
  
方案 B: LoRA（A100 80GB × 1）
  GPU 费用: 1 × $2.0/h × 4h = $8     ← 8x 便宜

方案 C: QLoRA（RTX 4090 24GB × 1）
  GPU 费用: 1 × $0.4/h × 6h = $2.4   ← 27x 便宜

方案 D: QLoRA + Unsloth（RTX 4090 24GB × 1）
  GPU 费用: 1 × $0.4/h × 3h = $1.2   ← 53x 便宜

方案 E: API 微调（Together AI）
  费用: ~$5（按 token 计费）          ← 最简单
```

---

## 生产级最佳实践清单

```
微调上线前完整检查清单

Phase 1: 数据准备 ✓
  □ 数据去重和去污染完成
  □ 数据质量人工抽检通过
  □ 数据格式和 Chat Template 验证
  □ 训练集/验证集/测试集划分合理
  □ 混入 5-10% 通用数据

Phase 2: 训练配置 ✓
  □ 基座模型选择合理
  □ 超参数经过初步搜索
  □ 使用适当的微调方法（LoRA/QLoRA）
  □ 开启梯度检查点和混合精度
  □ Wandb/TensorBoard 监控配置

Phase 3: 训练监控 ✓
  □ Loss 曲线正常下降
  □ 学习率调度正确
  □ 无 NaN/Inf 出现
  □ 显存使用合理
  □ 定期保存 Checkpoint

Phase 4: 模型评估 ✓
  □ 基准测试 ≥ 基座模型
  □ 领域任务指标达标
  □ 灾难性遗忘检测通过（保持率 > 90%）
  □ 安全性测试通过
  □ 人工评估样本质量

Phase 5: 部署准备 ✓
  □ LoRA 权重合并（如需要）
  □ 模型量化（GPTQ/AWQ/GGUF）
  □ 推理延迟满足 SLO
  □ A/B 测试方案就绪
  □ 回滚策略准备好
```

---

## 参考资料与引用

1. Zhou, C., et al. (2023). *LIMA: Less Is More for Alignment*. arXiv:2305.11206. https://arxiv.org/abs/2305.11206
2. Zhao, J., et al. (2024). *LoRA Land: 310 Fine-tuned LLMs that Rival GPT-4, A Technical Report*. arXiv:2405.00732. https://arxiv.org/abs/2405.00732
3. Luo, Y., et al. (2023). *An Empirical Study of Catastrophic Forgetting in Large Language Models During Continual Fine-tuning*. arXiv:2308.08747. https://arxiv.org/abs/2308.08747
4. Raschka, S. (2023). *Practical Tips for Finetuning LLMs*. https://magazine.sebastianraschka.com/p/practical-tips-for-finetuning-llms
5. The Novice's LLM Training Guide (Community). https://rentry.org/llm-training
6. Alignment Handbook - HuggingFace. https://github.com/huggingface/alignment-handbook

---

*上一篇：[05-finetuning-platforms.md](05-finetuning-platforms.md)*

[返回目录](README.md) | [返回主页](../README.md)
