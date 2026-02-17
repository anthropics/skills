# 剪枝与蒸馏

> 移除冗余权重或训练更小的等效模型。

## 剪枝 (Pruning)

### 类型对比

| 类型 | 方式 | 硬件友好 | 压缩率 |
|------|------|----------|--------|
| 非结构化 | 单个权重置零 | 低 | 高 |
| 结构化 | 整行/列/头移除 | 高 | 中 |

### 结构化剪枝示例

```python
# 移除不重要的 Attention Heads
def prune_attention_heads(model, heads_to_prune):
    for layer_idx, heads in heads_to_prune.items():
        layer = model.transformer.h[layer_idx]
        # 移除指定的 attention heads
        layer.attn.prune_heads(heads)
```

## 知识蒸馏 (Distillation)

### 原理

```
Teacher (大模型): 7B → 生成 soft labels
Student (小模型): 1B → 学习 teacher 的输出分布

Loss = α × CE(student, hard_label) + 
       (1-α) × KL(student_logits, teacher_logits)
```

### 训练代码

```python
def distillation_loss(student_logits, teacher_logits, labels, alpha=0.5, T=2.0):
    # Hard label loss
    hard_loss = F.cross_entropy(student_logits, labels)
    
    # Soft label loss (KL divergence)
    soft_loss = F.kl_div(
        F.log_softmax(student_logits / T, dim=-1),
        F.softmax(teacher_logits / T, dim=-1),
        reduction='batchmean'
    ) * (T ** 2)
    
    return alpha * hard_loss + (1 - alpha) * soft_loss
```

### 常见蒸馏模型

| Teacher | Student | 效果 |
|---------|---------|------|
| LLaMA-7B | TinyLLaMA-1.1B | 保留 ~80% 能力 |
| GPT-4 | Phi 系列 | 微软数据蒸馏研究 |
| BERT-Large | DistilBERT | 6层替代12层 |

---

*下一篇：[04-inference-engines.md](04-inference-engines.md) - 推理引擎详解*
