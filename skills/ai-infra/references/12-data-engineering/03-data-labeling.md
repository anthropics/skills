# 数据标注

> 高质量的标注数据是 AI 对齐的黄金——没有人类标注员的判断，模型就学不会"什么是好回答"。

## 目录

- [标注数据类型](#标注数据类型)
- [标注平台对比](#标注平台对比)
- [主动学习](#主动学习)
- [标注质量控制](#标注质量控制)
- [人机协同标注](#人机协同标注)
- [延伸阅读](#延伸阅读)

---

## 标注数据类型

```
LLM 训练所需的标注数据类型:

  1. 指令-回复对 (SFT 数据):
     {"instruction": "...", "response": "..."}
     用途: 监督微调，教模型遵循指令

  2. 偏好数据 (RLHF/DPO 数据):
     {"prompt": "...", "chosen": "...", "rejected": "..."}
     用途: 对齐训练，教模型什么是更好的回答

  3. 安全标注:
     {"text": "...", "label": "safe/unsafe", "category": "S1"}
     用途: 训练安全分类器 (如 Llama Guard)

  4. 事实性标注:
     {"claim": "...", "label": "true/false/unverifiable"}
     用途: 训练幻觉检测器
```

---

## 标注平台对比

| 平台 | 类型 | 特点 | 适用 |
|------|------|------|------|
| **Label Studio** | 开源自建 | 灵活、可定制、免费 | 团队内部标注 |
| **Prodigy** | 商业(spaCy) | 高效、主动学习集成 | NLP 专业标注 |
| **Scale AI** | 商业服务 | 专业标注团队、质量高 | 大规模标注 |
| **Surge AI** | 商业服务 | AI 训练专家标注 | LLM 偏好标注 |
| **Argilla** | 开源 | HuggingFace 集成好 | AI 反馈数据 |
| **Amazon SageMaker GT** | 云服务 | AWS 集成、MTurk | 大规模标注 |

### Label Studio 部署

```bash
# Label Studio 快速部署
pip install label-studio
label-studio start

# Docker 部署（生产推荐）
docker run -it -p 8080:8080 \
    -v label-studio-data:/label-studio/data \
    heartexlabs/label-studio:latest

# 配置 LLM 偏好标注模板:
# - 显示 Prompt
# - 并排显示两个回复 (A/B)
# - 标注员选择更好的回复
# - 标注维度: 有帮助性、真实性、安全性
```

---

## 主动学习

```
主动学习 — 用最少的标注获得最大的收益:

  传统标注: 随机选择数据标注（大量浪费）
  主动学习: 智能选择最有价值的数据标注

  策略:
    1. 不确定性采样: 选模型最不确定的样本
    2. 多样性采样: 选最多样化的样本
    3. 混合策略: 不确定性 + 多样性

  流程:
    初始少量标注 → 训练模型 → 选择最有价值的未标注数据
    → 标注 → 重新训练 → 循环

  效果: 通常只需标注 20-30% 的数据
        就能达到全量标注 90%+ 的效果
```

---

## 标注质量控制

```
标注质量控制最佳实践:

  1. 标注规范 (Annotation Guideline)
     详细的标注标准和示例
     边界情况的处理规则
     定期更新和培训

  2. 多人标注 + 一致性检查
     每条数据至少 2-3 人标注
     计算标注者间一致性 (Cohen's Kappa / Krippendorff's Alpha)
     Kappa > 0.7 视为可接受

  3. 黄金标准数据
     混入已知正确答案的测试数据
     自动计算标注员准确率
     低于阈值的标注员需重新培训

  4. 分层审核
     初级标注 → 高级审核 → 专家仲裁
     争议样本进入仲裁流程

  5. 定期校准
     标注团队定期讨论边界案例
     更新标注规范
     保持标注一致性
```

---

## 人机协同标注

```
AI 辅助标注 — 降低成本，提升效率:

  方式 1: 预标注
    AI 模型先自动标注 → 人工审核和修正
    效率提升: 2-5x

  方式 2: AI 质检
    人工标注 → AI 检测异常标注 → 人工复查
    质量提升: 减少 30%+ 的标注错误

  方式 3: RLAIF (AI 替代人类反馈)
    用强大的 AI (如 GPT-4) 生成偏好标注
    → 用于训练较弱的模型
    成本: 比人工标注低 90%+

  注意:
    ✗ AI 标注不能完全替代人工（存在偏见传播风险）
    ✓ 适合作为初筛和辅助工具
    ✓ 关键安全标注仍需人工
```

---

## 参考资料与引用

1. Lee, H., et al. (2023). *RLAIF: Scaling Reinforcement Learning from Human Feedback with AI Feedback*. arXiv:2309.00267. https://arxiv.org/abs/2309.00267
2. Zheng, L., et al. (2023). *Judging LLM-as-a-Judge with MT-Bench and Chatbot Arena*. arXiv:2306.05685. https://arxiv.org/abs/2306.05685
3. Label Studio - Open Source Data Labeling Tool. https://labelstud.io/
4. Argilla - Data Curation for AI. https://argilla.io/
5. Prodigy - Annotation Tool by Explosion AI. https://prodi.gy/
6. Honovich, O., et al. (2023). *Unnatural Instructions: Tuning Language Models with (Almost) No Human Labor*. arXiv:2212.09689. https://arxiv.org/abs/2212.09689

---

*上一篇：[02-data-collection-cleaning.md](02-data-collection-cleaning.md)* | *下一篇：[04-synthetic-data.md](04-synthetic-data.md)*

*返回：[README.md](README.md) - 章节索引*
