# 梯度累积与评估指标

> 梯度累积让你用小显存模拟大 Batch Size；评估指标帮你判断模型是否真正学好了。

## 目录

- [梯度累积](#梯度累积)
- [评估指标](#评估指标)

---

## 梯度累积

### 为什么需要梯度累积

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          梯度累积的动机                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  问题: 大 batch size 训练效果好，但显存装不下                                │
│                                                                             │
│  例: 你想用 batch_size=64，但 GPU 只能装 batch_size=8                       │
│                                                                             │
│  方案: 做 8 次 mini-batch (每次 8 个样本)                                   │
│        累积梯度，最后一次性更新参数                                          │
│        效果等价于 batch_size=64！                                           │
│                                                                             │
│  ──────────────────────────────────────────────────────────────────────     │
│                                                                             │
│  类比: 你要搬 64 箱货，但推车一次只能装 8 箱                                 │
│    方案 A (大 batch): 借一辆大卡车 → 一次搬完 (太贵!)                       │
│    方案 B (梯度累积): 推车跑 8 趟 → 效果一样，就是慢一点                     │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 工作原理

```
  没有梯度累积 (batch_size=8):
  ═══════════════════════════════════════════

  Step 1: 8个样本 → 前向 → 反向 → 得到梯度 g₁ → 更新参数
  Step 2: 8个样本 → 前向 → 反向 → 得到梯度 g₂ → 更新参数
  每步只用 8 个样本的信息，梯度噪声大


  梯度累积 (accumulation_steps=8, micro_batch=8):
  ═══════════════════════════════════════════

  Step 1.1: 8个样本 → 前向 → 反向 → g₁ (不更新，累积)
  Step 1.2: 8个样本 → 前向 → 反向 → g₁ += g₂ (继续累积)
  Step 1.3: 8个样本 → 前向 → 反向 → g₁ += g₃ (继续累积)
  ...
  Step 1.8: 8个样本 → 前向 → 反向 → g₁ += g₈ → 更新参数!

  等价于 batch_size = 8 × 8 = 64，梯度更稳定
```

### PyTorch 实现

```python
model = MyModel().cuda()
optimizer = torch.optim.AdamW(model.parameters(), lr=3e-4)

accumulation_steps = 8  # 累积 8 步
micro_batch_size = 8    # 每步处理 8 个样本
# 等效 batch_size = 8 × 8 = 64

for step, batch in enumerate(dataloader):
    # 前向 + 反向（不清零梯度）
    loss = model(batch)
    loss = loss / accumulation_steps  # 重要! 除以累积步数取平均
    loss.backward()
    
    # 每 accumulation_steps 步更新一次
    if (step + 1) % accumulation_steps == 0:
        # 可选: 梯度裁剪
        torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
        
        optimizer.step()
        optimizer.zero_grad()  # 更新后才清零

    if step % (accumulation_steps * 10) == 0:
        print(f"Step {step // accumulation_steps}: loss={loss.item() * accumulation_steps:.4f}")
```

### 关键注意事项

| 要点 | 说明 |
|------|------|
| **Loss 要除以累积步数** | `loss / accumulation_steps` 确保梯度均值正确 |
| **`zero_grad()` 的时机** | 在 `optimizer.step()` 之后调用，而非每个 mini-batch |
| **学习率不需要调整** | 因为梯度已经平均过了 |
| **Batch Norm 行为不同** | BN 统计量只基于 micro-batch 计算，与真实大 batch 不完全等价 |
| **分布式训练中** | 梯度同步只在 `optimizer.step()` 前做一次，中间累积步可跳过同步以提速 |

### 与分布式训练的结合

```
  4 GPU × 梯度累积 4 步 × micro_batch_size 8 = 全局 batch_size 128

  GPU 0: [b₁] → grad → [b₂] → grad += → [b₃] → grad += → [b₄] → grad +=
  GPU 1: [b₅] → grad → [b₆] → grad += → [b₇] → grad += → [b₈] → grad +=
  GPU 2: [b₉] → grad → [b₁₀]→ grad += → [b₁₁]→ grad += → [b₁₂]→ grad +=
  GPU 3: [b₁₃]→ grad → [b₁₄]→ grad += → [b₁₅]→ grad += → [b₁₆]→ grad +=
                                                                  ↓
                                                          AllReduce 梯度
                                                                  ↓
                                                          更新参数

  注意: 中间的累积步不需要 AllReduce (DDP 的 no_sync 上下文管理器)
```

```python
# DDP + 梯度累积的高效实现
from torch.nn.parallel import DistributedDataParallel as DDP

model = DDP(model, device_ids=[local_rank])

for step, batch in enumerate(dataloader):
    # 中间步: 跳过梯度同步
    is_accumulating = (step + 1) % accumulation_steps != 0
    
    with model.no_sync() if is_accumulating else nullcontext():
        loss = model(batch) / accumulation_steps
        loss.backward()
    
    if not is_accumulating:
        optimizer.step()
        optimizer.zero_grad()
```

---

## 评估指标

### 为什么 Loss 不够

```
  Loss 告诉你模型在「训练数据」上的表现
  但你真正关心的是:
    - 分类任务: 分对了多少? → Accuracy / F1
    - 生成任务: 生成的文本质量如何? → BLEU / ROUGE / Perplexity
    - 检索任务: 找到了正确答案吗? → Recall@K / MRR
```

### 常用评估指标速查

| 指标 | 适用任务 | 直觉理解 | 范围 |
|------|----------|----------|------|
| **Accuracy** | 分类 | 分对了的比例 | 0-1 |
| **Precision** | 分类 | "你说是的"里面真正是的比例 | 0-1 |
| **Recall** | 分类 | "真正是的"里面你找到的比例 | 0-1 |
| **F1 Score** | 分类 | Precision 和 Recall 的调和平均 | 0-1 |
| **Perplexity (PPL)** | 语言模型 | 模型的"困惑度"，越低越好 | 1-∞ |
| **BLEU** | 翻译/生成 | 与参考答案的 n-gram 重叠度 | 0-1 |
| **ROUGE** | 摘要/生成 | 与参考答案的召回率 | 0-1 |
| **AUC-ROC** | 二分类 | 分类器区分正负样本的能力 | 0-1 |

### 分类指标详解

```
混淆矩阵 (Confusion Matrix):

                    预测为正   预测为负
  ─────────────── ─────────── ───────────
  实际为正 (100)  │  TP = 80  │  FN = 20  │  ← 漏掉了 20 个
  实际为负 (100)  │  FP = 10  │  TN = 90  │  ← 误判了 10 个
  ─────────────── ─────────── ───────────

  Accuracy  = (TP+TN) / 总数     = (80+90)/200  = 85%
  Precision = TP / (TP+FP)       = 80/(80+10)   = 88.9%  "预测为正的准确率"
  Recall    = TP / (TP+FN)       = 80/(80+20)   = 80%    "正样本的覆盖率"
  F1        = 2×P×R / (P+R)      = 2×0.889×0.8/(0.889+0.8) = 84.2%
```

### LLM 评估指标

| 指标 | 计算方式 | 用途 |
|------|----------|------|
| **Perplexity** | PPL = e^(avg_loss) | 语言模型质量的通用指标 |
| **BLEU-4** | 4-gram 精确率的几何平均 | 翻译质量 |
| **ROUGE-L** | 最长公共子序列 / 参考长度 | 摘要质量 |
| **MMLU** | 多领域多选题准确率 | LLM 知识广度 |
| **HumanEval** | 代码通过率 (pass@k) | 代码生成能力 |
| **RAGAS** | 忠实度 + 相关性 + 答案质量 | RAG 系统质量 |

```python
# 计算 Perplexity
import torch
import math

total_loss = 0
total_tokens = 0

with torch.no_grad():
    for batch in eval_dataloader:
        outputs = model(**batch)
        total_loss += outputs.loss.item() * batch["input_ids"].numel()
        total_tokens += batch["input_ids"].numel()

avg_loss = total_loss / total_tokens
ppl = math.exp(avg_loss)
print(f"Perplexity: {ppl:.2f}")
```

---

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **Ott, M., et al. (2018).** *Scaling Neural Machine Translation.* — 大 batch 训练与梯度累积策略  
   https://arxiv.org/abs/1806.00187

2. **Goyal, P., et al. (2017).** *Accurate, Large Minibatch SGD: Training ImageNet in 1 Hour.* — 大 batch 训练技巧  
   https://arxiv.org/abs/1706.02677

3. **PyTorch Documentation.** *gradient accumulation.* — PyTorch 梯度累积最佳实践  
   https://pytorch.org/docs/stable/notes/amp_examples.html

4. **HuggingFace Documentation.** *Training with gradient accumulation.* — Transformers 库梯度累积  
   https://huggingface.co/docs/transformers/perf_train_gpu_one

5. **Merity, S., Keskar, N. S., & Socher, R. (2018).** *An Analysis of Neural Language Modeling at Multiple Scales.* — Perplexity 评估指标  
   https://arxiv.org/abs/1803.08240
