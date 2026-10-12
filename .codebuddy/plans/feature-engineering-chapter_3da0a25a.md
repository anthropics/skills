---
name: feature-engineering-chapter
overview: 在 `00-training-fundamentals/` 模块下新增 `12-feature-engineering.md` 章节，系统讲解 AI 时代大数据特征工程的完整知识体系，包括方案、技术栈、深度案例，以及 AI 如何使用特征工程。
todos:
  - id: create-feature-engineering
    content: 创建 00-training-fundamentals/12-feature-engineering.md 特征工程深度讲解全文（概述、特征类型、大数据技术栈、方案全景、两个深度案例、Pipeline 架构、AI 使用特征工程）
    status: completed
  - id: update-indexes
    content: 更新 README.md 导航表/知识地图/阅读时间，以及 SKILL.md 核心内容列表，添加特征工程条目
    status: completed
    dependencies:
      - create-feature-engineering
---

## 用户需求

在 AI Infrastructure 知识库的 `00-training-fundamentals` 模块中新增一篇特征工程深度讲解章节。

## 产品概述

新增 `12-feature-engineering.md`，作为训练基础知识的最后一篇，系统讲解 AI 时代大数据特征工程的方法论、技术栈、深度案例，以及 AI 如何使用特征工程。

## 核心特征

1. **特征工程概述**：用生活类比引入概念，解释为什么在深度学习/LLM 时代特征工程依然重要
2. **特征类型与构造方法**：数值特征、类别特征、时序特征、文本特征、图特征的处理手段与代码示例
3. **大数据特征工程技术栈**：Spark / Flink / Hive / Pandas / Polars / Dask 的适用场景、对比和用法示例
4. **特征工程方案全景**：传统 ML 手工特征 vs 深度学习自动特征 vs LLM 时代特征的演进
5. **深度案例**（两个完整端到端案例）：

- 电商推荐系统特征工程（用户画像 + 行为序列 + 实时特征 + Embedding）
- 金融风控特征工程（时间窗口聚合 + 图特征 + 实时规则引擎）

6. **特征工程完整 Pipeline**：从原始数据到训练就绪的端到端流程架构
7. **AI 如何使用特征工程**：传统 ML 特征输入、深度学习 Embedding 替代、LLM 时代 Prompt 作为新特征工程、AutoFeature 自动特征生成
8. **同步更新索引**：更新 README.md、00-training-fundamentals.md 索引页和 SKILL.md 核心内容列表

## 技术栈

- 文件格式：Markdown（与现有知识库一致）
- 代码示例语言：Python（PySpark、Flink PyAPI、Pandas、PyTorch）
- 图表：ASCII 字符图（与现有章节一致的风格）

## 实现方案

### 策略

新增一篇约 800-1000 行的深度 Markdown 文档 `12-feature-engineering.md`，放置在 `00-training-fundamentals/` 目录下（编号 12，紧接 `11-training-vs-inference.md`）。同时更新 3 个索引文件以保持导航完整性。

### 关键决策

1. **放在 `00-training-fundamentals/` 而非 `04-mlops-llmops/`**：特征工程是训练前的数据准备核心环节，属于训练基础知识；而 `04-mlops-llmops/05-feature-store.md` 聚焦的是 Feature Store 平台工具层，二者互补不冲突。新文章末尾会交叉引用 Feature Store 章节。

2. **写作风格与现有章节保持一致**：

- 每个概念先用生活类比引入（如"厨师备料"类比特征工程）
- ASCII 图表展示架构和流程（非 Mermaid）
- 对比表格展示方案差异
- 深度代码示例（真实场景，非 hello-world）
- 量化数据支撑论点

3. **章节标题格式**：`# 标题：副标题` + `> 一句话简介` + `## 目录` + `---` + 各小节（与 `11-training-vs-inference.md` 保持一致）

### 实现要点

- 新文件路径：`skills/ai-infra/references/00-training-fundamentals/12-feature-engineering.md`
- 更新文件 1：`skills/ai-infra/references/00-training-fundamentals/README.md` — 子文档导航表添加第 12 行、知识地图添加节点、学习路径添加条目、更新总阅读时间
- 更新文件 2：`skills/ai-infra/references/00-training-fundamentals.md` — 索引页无需修改（当前为跳转页，指向 README.md）
- 更新文件 3：`skills/ai-infra/SKILL.md` — "0. AI 训练基础"核心内容列表添加特征工程条目

### 注意事项

- 与 `04-mlops-llmops/05-feature-store.md` 内容互补：新文章讲"如何做特征工程"（方法论+技术），Feature Store 讲"如何管理特征"（平台工具），末尾互相引用
- 代码示例需涵盖 PySpark（大数据离线特征）、Flink（实时特征）、Pandas（小数据快速实验）、PyTorch（Embedding/模型输入），确保技术栈覆盖全面
- 两个深度案例（电商推荐 + 金融风控）需包含完整的数据 -> 特征 -> 模型输入链路

## 目录结构

```
skills/ai-infra/references/
├── 00-training-fundamentals/
│   ├── README.md                      # [MODIFY] 添加第12篇导航、更新知识地图和阅读时间
│   ├── 12-feature-engineering.md      # [NEW] 特征工程深度讲解，约800-1000行。涵盖：特征工程概述与生活类比、特征类型与构造方法（数值/类别/时序/文本/图）、大数据技术栈对比（Spark/Flink/Hive/Pandas/Polars）及代码示例、方案演进全景（传统ML→深度学习→LLM）、两个深度案例（电商推荐+金融风控的端到端Pipeline）、特征工程完整Pipeline架构图、AI如何使用特征工程（Embedding/Prompt/AutoFeature）、与Feature Store交叉引用
│   └── ...（现有11个文件不变）
├── 00-training-fundamentals.md        # 无需修改（纯跳转页）
└── skills/ai-infra/SKILL.md          # [MODIFY] "0. AI训练基础"核心内容列表添加特征工程条目
```

## Agent Extensions

### SubAgent

- **code-explorer**
- 用途：在编写新文件前，验证现有章节的精确格式、交叉引用路径和代码示例风格
- 预期结果：确保新文件的格式、导航链接与现有 11 篇文档完全一致