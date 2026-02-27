---
name: training-vs-inference
overview: 在 00-training-fundamentals 目录下新增第 11 篇文档 `11-training-vs-inference.md`，专门深入讲解大模型训练与推理的差异，同时更新 README.md 导航。
todos:
  - id: create-doc
    content: 新建 11-training-vs-inference.md，完成训练 vs 推理深度对比文档的全部内容（ASCII 框图、生活类比、LLaMA-7B 数值、总结对比表）
    status: completed
  - id: update-readme
    content: 更新 README.md：导航表新增第 11 行、知识地图添加节点、学习路径 C 添加条目、更新总阅读时间
    status: completed
    dependencies:
      - create-doc
---

## 用户需求

在 AI 训练基础知识系列中新增第 11 篇文档，专门深入讲解大模型训练与推理的系统性差异。

## 产品概述

在现有 10 篇训练基础文档之后，新增一篇"训练 vs 推理"深度对比文档，从计算模式、显存占用、计算瓶颈、并行策略、Batch 处理、精度策略、Prefill/Decode 阶段等多维度系统性对比训练和推理的本质区别。同时更新 README.md 导航、知识地图和学习路径。

## 核心功能

1. **全局对比**：训练是"学习"（调参），推理是"应用"（用参数做预测），用生活类比建立直觉
2. **计算模式差异**：训练需要前向+反向传播，推理仅需前向传播（自回归逐 token 生成）
3. **显存占用差异**：训练需要参数+梯度+优化器状态+激活值，推理仅需参数+KV Cache；用 LLaMA-7B 具体数字对比
4. **计算瓶颈差异**：训练是 compute-bound（大矩阵乘法），推理是 memory-bound（频繁访存）
5. **并行策略差异**：训练使用 DP/TP/PP 组合，推理主要用 TP + KV Cache 分布
6. **Batch 处理差异**：训练用大 batch 充分利用 GPU，推理用小 batch + continuous batching
7. **精度策略差异**：训练使用混合精度（BF16/FP16），推理可激进量化（INT8/INT4）
8. **Prefill vs Decode 阶段**：推理的两阶段特性及其不同的计算特征
9. **总结对比表**：一张表涵盖所有维度的训练 vs 推理对比
10. **README 更新**：导航表、知识地图、学习路径、阅读时间同步更新

## 技术栈

- 文档格式：Markdown (.md)
- 写作规范：纯文本 + ASCII 框图，无需任何前端/后端技术栈
- 参考模型：LLaMA-7B（hidden=4096, 32 层, 32 头）作为统一数值案例

## 实现方案

### 策略概述

新建 `11-training-vs-inference.md` 文档，严格遵循现有 10 篇文档的写作风格和结构模式：使用 ASCII 框图进行可视化、生活类比辅助理解、LLaMA-7B 具体数值举例。然后更新 `README.md` 中的导航表、知识地图、学习路径和总阅读时间。

### 关键决策

1. **编号选择 11**：按现有序列 01-10 自然递增，编号为 11
2. **与 10-transformer-architecture.md 的关系**：第 10 篇末尾已简要介绍 KV Cache（约 30 行），新文档将深入展开，但不重复基础概念，而是引用第 10 篇作为前置阅读
3. **数值案例统一用 LLaMA-7B**：与现有文档保持一致（hidden=4096, 32 层, 32 头, 7B 参数），便于读者跨文档对照
4. **文档风格一致性**：

- 开头用 `>` 引用做一句话概述
- 紧接 `## 目录` 列出所有章节锚链接
- 大量使用 ``` 代码块内的 ASCII 框图
- 生活类比贯穿（如训练=上学备考，推理=上考场答题）
- 每节以 `---` 分隔
- 末尾有总结表 + 相关文档链接

## 实现注意事项

1. **显存计算数值需准确**：

- 训练 LLaMA-7B FP16：参数 14GB + 梯度 14GB + AdamW 状态 28GB + 激活值 ≈ 若干 GB = ~60GB+
- 推理 LLaMA-7B FP16：参数 14GB + KV Cache（随 seq_len 线性增长，seq=2048 约 1GB/用户）

2. **与现有文档衔接**：引用 03-前向传播、05-反向传播、06-梯度下降、10-Transformer 等已有文档
3. **README 更新范围控制**：仅修改导航表（加一行）、知识地图（ASCII 图加一个节点）、学习路径（按需查阅加一条）、总阅读时间（+25 分钟），不改动其他内容

## 架构设计

### 新文档章节结构

```
11-training-vs-inference.md
├── 开头引言 + 目录
├── 一句话区分：训练 vs 推理
├── 全景对比图（ASCII）
├── 计算模式差异（前向+反向 vs 仅前向自回归）
├── 显存占用差异（含 LLaMA-7B 具体数值计算）
├── 计算瓶颈差异（compute-bound vs memory-bound）
├── 并行策略差异（DP/TP/PP vs TP + KV Cache 分布）
├── Batch 处理差异（大 batch vs continuous batching）
├── 精度策略差异（混合精度 vs 量化推理）
├── Prefill vs Decode 阶段详解
├── 总结对比表
└── 相关文档链接
```

### README 修改点

```
README.md
├── 导航表：第 40 行后新增第 11 行条目
├── 知识地图：ASCII 图中添加 "11 训练vs推理" 节点
├── 学习路径 C：按需查阅新增一条
├── 总阅读时间：4 小时 → 4.5 小时
└── 路径 B 总时间描述同步更新
```

## 目录结构

```
skills/ai-infra/references/00-training-fundamentals/
├── README.md                        # [MODIFY] 更新导航表（新增第11行）、知识地图（新增节点）、
│                                    #   学习路径C（新增条目）、总阅读时间（4h→4.5h）、
│                                    #   路径B时间（3.5h→4h）
└── 11-training-vs-inference.md      # [NEW] 训练 vs 推理深度对比。系统性对比训练和推理在
                                     #   计算模式、显存占用、计算瓶颈、并行策略、Batch处理、
                                     #   精度策略、Prefill/Decode等维度的差异。使用ASCII框图、
                                     #   生活类比、LLaMA-7B具体数值，风格与现有文档一致。
                                     #   预计约800-1000行，阅读时间25分钟。
```

## Agent Extensions

### Skill

- **skill-creator**
- 用途：本项目是一个 skill 仓库，新增文档后可能需要确认是否需要更新 SKILL.md 中的描述
- 预期结果：确认 SKILL.md 无需修改（因为新文档仅是已有章节的扩展），或在必要时指导更新