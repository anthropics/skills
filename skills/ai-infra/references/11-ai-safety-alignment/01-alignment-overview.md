# 对齐概述

> AI 对齐不是让模型更笨，而是让模型在保持能力的同时，做一个"靠谱的助手"而非"不可控的天才"。

## 目录

- [什么是 AI 对齐](#什么是-ai-对齐)
- [为什么需要对齐](#为什么需要对齐)
- [对齐税：安全 vs 能力的平衡](#对齐税安全-vs-能力的平衡)
- [对齐技术发展时间线](#对齐技术发展时间线)
- [对齐的基础设施需求](#对齐的基础设施需求)
- [延伸阅读](#延伸阅读)

---

## 什么是 AI 对齐

### 生活类比：培养新员工

```
AI 对齐就像培训一个超级聪明但没有常识的新员工:

  预训练 = 这个人读了全世界所有的书
    → 知识渊博，但可能什么都说
    → 可能输出有害内容、虚假信息、偏见观点

  对齐 = 入职培训 + 行为规范
    → 学会拒绝不当请求
    → 学会承认不知道
    → 学会遵守公司价值观
    → 学会友好、有帮助地回答

  对齐的目标 (3H):
    Helpful (有帮助): 真正帮用户解决问题
    Harmless (无害): 不输出有害内容
    Honest (诚实): 不编造事实，承认不确定性
```

### 对齐的层次

```
┌─────────────────────────────────────────────────────────────────┐
│                   AI 对齐的层次                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Level 1: 行为对齐 (Behavioral Alignment)                        │
│    目标: 模型输出符合期望的行为规范                               │
│    方法: RLHF, DPO, SFT                                        │
│    现状: 当前主流方法，已广泛应用                                 │
│                                                                 │
│  Level 2: 意图对齐 (Intent Alignment)                            │
│    目标: 模型理解并执行用户的真实意图                             │
│    方法: 更好的指令跟随、上下文理解                               │
│    现状: 持续改进中                                              │
│                                                                 │
│  Level 3: 价值对齐 (Value Alignment)                             │
│    目标: 模型内化人类价值观                                      │
│    方法: Constitutional AI, 伦理推理                             │
│    现状: 研究前沿                                                │
│                                                                 │
│  Level 4: 超级对齐 (Superalignment)                              │
│    目标: 确保超过人类能力的 AI 仍可控                             │
│    方法: 待研究 (可扩展监督、弱到强泛化等)                       │
│    现状: 开放问题                                                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 为什么需要对齐

### 不对齐的风险

```
未经对齐的模型可能:

  1. 输出有害内容
     "如何制造 XX"  → 直接给出详细步骤
     "写一段仇恨言论" → 照做不误

  2. 产生幻觉
     编造不存在的论文、法律条文、事实
     以极高的自信度输出完全错误的信息

  3. 放大偏见
     训练数据中的偏见被模型学习并放大
     对某些群体的歧视性输出

  4. 隐私泄露
     复述训练数据中的个人信息
     在对话中泄露其他用户的信息

  5. 被恶意利用
     Prompt Injection 绕过限制
     被用于生成虚假信息、钓鱼邮件等

  对齐是从"一个知道很多东西的工具"
  变成"一个可信赖的助手"的关键步骤
```

---

## 对齐税：安全 vs 能力的平衡

```
"对齐税" (Alignment Tax):

  对齐过程可能降低模型的某些能力

  ┌──────────────────────────────────────────────┐
  │                                              │
  │  能力                                        │
  │  ▲                                           │
  │  │  ●  预训练模型 (高能力，不安全)             │
  │  │     ╲                                     │
  │  │      ╲  对齐过程                           │
  │  │       ╲                                   │
  │  │        ●  对齐模型 (略低能力，安全)         │
  │  │                                           │
  │  └─────────────────────────▶ 安全性           │
  │                                              │
  │  理想情况: 对齐税很小                          │
  │  现实: 过度对齐可能导致模型过于保守             │
  │    - 拒绝回答合理的问题                        │
  │    - 输出过于冗长的安全警告                     │
  │    - 在边界情况过于谨慎                        │
  │                                              │
  │  目标: 最小化对齐税的同时最大化安全性           │
  └──────────────────────────────────────────────┘
```

---

## 对齐技术发展时间线

| 时间 | 里程碑 | 方法 |
|------|--------|------|
| 2017 | Deep RL from Human Preferences | 奖励模型 + RL |
| 2020 | GPT-3 | Few-shot 提示，无对齐 |
| 2022 | InstructGPT | RLHF (SFT → RM → PPO) |
| 2022 | Constitutional AI | AI 自我约束 |
| 2023 | DPO | 无需奖励模型的直接偏好优化 |
| 2023 | Llama 2 | 开源 RLHF 实践 |
| 2024 | KTO / IPO / ORPO | 更多偏好优化变体 |
| 2024 | Llama 3 | 大规模安全评估 |
| 2025 | Constitutional AI 2.0, RLAIF | AI 反馈替代人类反馈 |

---

## 对齐的基础设施需求

```
对齐训练的基础设施特殊需求:

  1. RLHF 需要同时运行多个模型
     ┌──────────────────────────────────────┐
     │  Actor Model (被训练的模型)            │ → 需要 GPU
     │  Reference Model (参考模型)            │ → 需要 GPU
     │  Reward Model (奖励模型)               │ → 需要 GPU
     │  Critic Model (价值网络, PPO)           │ → 需要 GPU
     └──────────────────────────────────────┘
     → 70B 模型的 RLHF 需要 ~4× GPU 资源

  2. 人类标注基础设施
     标注平台: Label Studio, Scale AI, Surge AI
     标注员管理: 培训、质量控制、一致性检查
     数据管理: 偏好数据的收集、存储、版本管理

  3. 安全评估基础设施
     自动评估管线: 定期运行安全基准测试
     红队测试平台: 自动化攻击测试
     监控系统: 生产环境的安全指标监控

  4. 框架工具
     TRL (Transformers RL): HuggingFace 的 RLHF 框架
     OpenRLHF: 开源 RLHF 训练框架
     DeepSpeed-Chat: 基于 DeepSpeed 的 RLHF
```

---

## 参考资料与引用

1. Ouyang, L., et al. (2022). *Training language models to follow instructions with human feedback* (InstructGPT). arXiv:2203.02155. https://arxiv.org/abs/2203.02155
2. Bai, Y., et al. (2022). *Constitutional AI: Harmlessness from AI Feedback*. Anthropic. arXiv:2212.08073. https://arxiv.org/abs/2212.08073
3. Amodei, D., et al. (2016). *Concrete Problems in AI Safety*. arXiv:1606.06565. https://arxiv.org/abs/1606.06565
4. Ngo, R., et al. (2022). *The Alignment Problem from a Deep Learning Perspective*. arXiv:2209.00626. https://arxiv.org/abs/2209.00626
5. Anthropic's Core Views on AI Safety. https://www.anthropic.com/research
6. OpenAI's Approach to AI Safety. https://openai.com/safety
7. DeepMind Safety Research. https://deepmind.google/discover/blog/?category=Safety

---

*下一篇：[02-rlhf-dpo.md](02-rlhf-dpo.md)*

*返回：[README.md](README.md) - 章节索引*
