---
name: economic-cycles-research
overview: 在 skills/ 下创建新的 skills/economic-cycles/ skill 目录，用于系统性研究经济周期理论。先聚焦涛动周期和熊彼特理论，同时覆盖康德拉季耶夫长波、朱格拉周期、基钦周期、库兹涅茨周期、明斯基金融不稳定假说等主要理论。通过联网搜索收集学术论文、博客、百科等多种来源的资料，整理为 Markdown 总结文档并附带来源链接。
todos:
  - id: create-skeleton
    content: 使用 [skill:skill-creator] 创建 skills/economic-cycles/ 目录骨架，包括 SKILL.md 和所有空的 references 子目录及索引文件
    status: pending
  - id: research-overview
    content: 联网搜索经济周期总论资料，撰写 00-overview/ 下的 README.md 及两个子文档（经济周期定义、各理论对比）
    status: pending
    dependencies:
      - create-skeleton
  - id: research-tao-schumpeter
    content: 联网搜索涛动周期（周金涛）和熊彼特创新周期资料，撰写 01-tao-cycle/ 和 02-schumpeter-cycle/ 下的全部文档
    status: pending
    dependencies:
      - create-skeleton
  - id: research-kondratieff-juglar
    content: 联网搜索康德拉季耶夫长波和朱格拉周期资料，撰写 03-kondratieff-wave/ 和 04-juglar-cycle/ 下的全部文档
    status: pending
    dependencies:
      - create-skeleton
  - id: research-kitchin-kuznets
    content: 联网搜索基钦周期和库兹涅茨周期资料，撰写 05-kitchin-cycle/ 和 06-kuznets-cycle/ 下的全部文档
    status: pending
    dependencies:
      - create-skeleton
  - id: research-minsky
    content: 联网搜索明斯基金融不稳定假说资料，撰写 07-minsky-moment/ 下的全部文档
    status: pending
    dependencies:
      - create-skeleton
  - id: finalize-skill
    content: 完善 SKILL.md 总览内容（全景图、知识领域列表、文档索引表），确保所有交叉引用链接正确
    status: pending
    dependencies:
      - research-overview
      - research-tao-schumpeter
      - research-kondratieff-juglar
      - research-kitchin-kuznets
      - research-minsky
---

## 用户需求

创建一个新的 skill 目录 `skills/economic-cycles/`，用于系统性研究经济周期理论，参照现有 `ai-infra` skill 的目录结构和文档风格。

## 产品概述

一个经济周期理论的系统性知识库，以 Markdown 文档形式组织，覆盖主流经济周期理论。所有内容为 Markdown 总结文档，附带来源链接。采用联网搜索（模拟 NotebookLM 的 deep research 方式）收集学术论文、中英文博客/文章、百科资源等，整理后保存到本地。

## 核心功能

1. **经济周期总论/导读**：经济周期概念全景，各周期理论概览与对比，嵌套关系图
2. **涛动周期（周金涛）**：周金涛的涛动周期理论核心观点、康波周期在中国的应用、经典语录与预测回顾
3. **熊彼特经济周期（创新周期）**：创造性破坏理论、三周期嵌套模型（康德拉季耶夫+朱格拉+基钦）、技术创新驱动长波
4. **康德拉季耶夫长波（50-60年）**：长波理论起源与实证、五次长波的划分与特征、技术革命与长波的关系
5. **朱格拉周期（7-11年）**：固定资本投资周期、与企业盈利/信贷扩张的关系
6. **基钦周期（3-5年）**：库存周期机制、库存投资的四阶段
7. **库兹涅茨周期（15-25年）**：建筑/房地产周期、人口结构与城市化驱动
8. **明斯基金融不稳定假说**：金融内生不稳定性、三类融资结构（对冲/投机/庞氏）、明斯基时刻

每个章节包含：理论背景与核心观点、关键人物与代表作、历史实证与数据、与其他周期的关系、来源链接汇总

## 技术栈

- 内容格式：Markdown（.md）
- 项目框架：遵循现有 Anthropic Skills 目录结构规范
- 联网资料获取：通过 web_search + web_fetch 进行 deep research 式资料收集

## 实现方案

### 策略

参照 `skills/ai-infra/` 的成熟目录组织模式，创建 `skills/economic-cycles/` 作为独立 skill。目录结构采用编号递增的章节形式，每个章节包含一个索引 `.md` 文件和一个同名子目录，子目录内放置 README.md（章节总览导航）及编号的子文档。

### 关键决策

1. **目录结构完全对齐 ai-infra 模式**：`SKILL.md` 作为入口 → `references/` 下编号章节 → 每个章节有索引 .md + 子目录。这确保了项目内 skill 风格的一致性。

2. **联网搜索策略（模拟 Deep Research）**：

- 对每个经济周期理论主题，分别执行中文和英文搜索
- 搜索维度：理论概述、关键人物与代表作、历史实证、学术论文、中文分析文章
- 获取搜索结果后，使用 web_fetch 抓取高质量页面的详细内容
- 将获取的内容整理、提炼为结构化 Markdown，附注来源 URL

3. **内容编号规划**：

- 00: 经济周期总论与导读
- 01: 涛动周期（周金涛）
- 02: 熊彼特经济周期
- 03: 康德拉季耶夫长波
- 04: 朱格拉周期
- 05: 基钦周期
- 06: 库兹涅茨周期
- 07: 明斯基金融不稳定假说

4. **文档风格**：

- 中文写作，与 ai-infra 风格一致
- 使用 emoji 标记章节（📚、📖、🗺️、🎯 等）
- 包含学习目标、核心概念速览、知识地图（ASCII 或 Mermaid）
- 每个子文档底部有"上一篇/下一篇"导航
- README.md 包含子文档导航表（序号、文档链接、内容概述、预计阅读时间）

## 实现注意事项

- **来源链接有效性**：所有引用的 URL 在文档中标注搜索日期，便于后续验证
- **内容深度控制**：每个章节的总论 README 控制在 2000-3000 字，子文档 1500-2500 字，避免过于冗长
- **交叉引用**：各周期理论之间存在嵌套和关联关系（如熊彼特的三周期嵌套），需在文档中用链接互相引用
- **渐进扩展**：先建立完整骨架和核心内容，后续可在每个子目录内持续添加深入文档

## 架构设计

### 目录结构与 ai-infra 的对应关系

```
ai-infra/                          economic-cycles/
├── SKILL.md                       ├── SKILL.md
├── references/                    ├── references/
│   ├── 00-training-fundamentals.md│   ├── 00-overview.md
│   ├── 00-training-fundamentals/  │   ├── 00-overview/
│   │   ├── README.md              │   │   ├── README.md
│   │   └── 01-xxx.md              │   │   └── 01-xxx.md
│   ├── 01-gpu-hardware.md         │   ├── 01-tao-cycle.md
│   └── ...                        │   └── ...
```

## 目录结构

本实现创建一个全新的 skill 目录，包含 SKILL.md 入口文件和 8 个主题章节。

```
skills/economic-cycles/
├── SKILL.md                                    # [NEW] Skill 元数据和总览入口。包含 YAML frontmatter (name: economic-cycles, description, license)，经济周期全景图（ASCII 图表展示各周期嵌套关系），核心知识领域列表（8 个章节的概要和链接），学习路径指南，文档索引表。参照 ai-infra/SKILL.md 的完整格式。
├── references/
│   ├── 00-overview.md                          # [NEW] 经济周期总论索引页。简短导读，指向 00-overview/ 子目录的 README.md。
│   ├── 00-overview/                            
│   │   ├── README.md                           # [NEW] 经济周期总论详细内容。包含：经济周期的定义与分类、各周期理论全景对比表（周期名/时长/驱动力/代表人物）、周期嵌套关系知识地图、子文档导航表。联网搜索经济周期综述类资源。
│   │   ├── 01-what-is-economic-cycle.md        # [NEW] 什么是经济周期。定义、四阶段（繁荣-衰退-萧条-复苏）、历史认知演变。
│   │   └── 02-cycle-comparison.md              # [NEW] 各周期理论横向对比。时间尺度、驱动因子、相互关系的系统对比。
│   ├── 01-tao-cycle.md                         # [NEW] 涛动周期索引页。简短导读，指向子目录。
│   ├── 01-tao-cycle/
│   │   ├── README.md                           # [NEW] 涛动周期详细总览。周金涛生平、核心理论框架、子文档导航。联网搜索周金涛相关资料、演讲记录、分析文章。
│   │   ├── 01-zhou-jintao-theory.md            # [NEW] 周金涛理论核心。康波周期在中国的映射、人生财富规划与康波、经典语录与预测验证。
│   │   └── 02-tao-cycle-practice.md            # [NEW] 涛动周期实践应用。2019/2025 年时间窗口分析、资产配置建议、局限性讨论。
│   ├── 02-schumpeter-cycle.md                  # [NEW] 熊彼特经济周期索引页。
│   ├── 02-schumpeter-cycle/
│   │   ├── README.md                           # [NEW] 熊彼特周期详细总览。创造性破坏理论、三周期嵌套模型、子文档导航。联网搜索熊彼特创新周期相关学术资源。
│   │   ├── 01-creative-destruction.md          # [NEW] 创造性破坏理论详解。企业家精神、技术创新与经济变革、五次技术革命浪潮。
│   │   └── 02-three-cycle-model.md             # [NEW] 三周期嵌套模型。康德拉季耶夫+朱格拉+基钦的嵌套关系与数学表达。
│   ├── 03-kondratieff-wave.md                  # [NEW] 康德拉季耶夫长波索引页。
│   ├── 03-kondratieff-wave/
│   │   ├── README.md                           # [NEW] 康波详细总览。五次长波划分、技术革命驱动、子文档导航。联网搜索 Kondratieff wave 学术资料。
│   │   ├── 01-five-waves.md                    # [NEW] 五次长波详解。每次长波的起止时间、驱动技术、经济特征、典型事件。
│   │   └── 02-evidence-and-debate.md           # [NEW] 实证与争议。统计证据、批评与反驳、现代研究进展。
│   ├── 04-juglar-cycle.md                      # [NEW] 朱格拉周期索引页。
│   ├── 04-juglar-cycle/
│   │   ├── README.md                           # [NEW] 朱格拉周期详细总览。固定资本投资周期机制、子文档导航。联网搜索朱格拉周期相关资源。
│   │   ├── 01-investment-mechanism.md          # [NEW] 固定投资周期机制。企业资本开支决策、信贷扩张与收缩、产能过剩与出清。
│   │   └── 02-juglar-in-practice.md            # [NEW] 朱格拉周期实证。中美欧的朱格拉周期历史数据、当前所处阶段分析。
│   ├── 05-kitchin-cycle.md                     # [NEW] 基钦周期索引页。
│   ├── 05-kitchin-cycle/
│   │   ├── README.md                           # [NEW] 基钦周期详细总览。库存周期四阶段、子文档导航。联网搜索库存周期相关资源。
│   │   ├── 01-inventory-mechanism.md           # [NEW] 库存周期机制。主动补库存→被动补库存→主动去库存→被动去库存四阶段。
│   │   └── 02-kitchin-indicators.md            # [NEW] 基钦周期指标。PMI、库存同比、产成品库存等领先/同步/滞后指标解读。
│   ├── 06-kuznets-cycle.md                     # [NEW] 库兹涅茨周期索引页。
│   ├── 06-kuznets-cycle/
│   │   ├── README.md                           # [NEW] 库兹涅茨周期详细总览。建筑/房地产周期、人口驱动、子文档导航。联网搜索 Kuznets cycle 相关资源。
│   │   ├── 01-real-estate-cycle.md             # [NEW] 房地产周期详解。土地开发→建设→库存→出清的完整周期、人口结构影响。
│   │   └── 02-urbanization-drive.md            # [NEW] 城市化与库兹涅茨周期。全球城市化进程对建筑周期的驱动、中国房地产周期分析。
│   ├── 07-minsky-moment.md                     # [NEW] 明斯基金融不稳定假说索引页。
│   └── 07-minsky-moment/
│       ├── README.md                           # [NEW] 明斯基假说详细总览。金融内生不稳定性理论、子文档导航。联网搜索 Minsky moment 相关学术和新闻资源。
│       ├── 01-financial-instability.md         # [NEW] 金融不稳定假说详解。三类融资结构（对冲/投机/庞氏）、从稳定到不稳定的内生演化机制。
│       └── 02-minsky-moments-history.md        # [NEW] 历史上的明斯基时刻。2008年次贷危机、1997年亚洲金融危机、日本泡沫等案例分析。
```

## Agent Extensions

### Skill

- **skill-creator**
- 用途：指导创建符合规范的 SKILL.md 文件，确保 frontmatter 格式、描述内容等满足 Anthropic Skills 标准
- 预期结果：生成结构规范、描述准确的 SKILL.md 入口文件

### SubAgent

- **code-explorer**
- 用途：在需要参考 ai-infra 现有文档格式细节时，批量读取多个参考文件以确保风格一致性
- 预期结果：准确复用现有文档的格式惯例（emoji 标记、导航表、知识地图等）