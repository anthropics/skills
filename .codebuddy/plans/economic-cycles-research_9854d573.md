---
name: economic-cycles-research
overview: 在 skills/ 下创建新的 skills/economic-cycles/ skill 目录，用于系统性研究经济周期理论。先聚焦涛动周期和熊彼特理论，同时覆盖康德拉季耶夫长波、朱格拉周期、基钦周期、库兹涅茨周期、明斯基金融不稳定假说等主要理论。通过联网搜索收集学术论文、博客、百科等多种来源的资料，整理为 Markdown 总结文档并附带来源链接。
todos:
  - id: create-skeleton
    content: 创建 skills/economic-cycles/ 目录骨架，包括 SKILL.md 和所有 references 子目录及索引文件
    status: completed
  - id: research-overview
    content: 联网搜索经济周期总论资料，撰写 00-overview/ 下的 README.md 及两个子文档（经济周期定义、各理论对比）
    status: completed
    dependencies:
      - create-skeleton
  - id: research-tao-schumpeter
    content: 联网搜索涛动周期（周金涛）和熊彼特创新周期资料，撰写 01-tao-cycle/ 和 02-schumpeter-cycle/ 下的全部文档
    status: completed
    dependencies:
      - create-skeleton
  - id: research-kondratieff-juglar
    content: 联网搜索康德拉季耶夫长波和朱格拉周期资料，撰写 03-kondratieff-wave/ 和 04-juglar-cycle/ 下的全部文档
    status: completed
    dependencies:
      - create-skeleton
  - id: research-kitchin-kuznets
    content: 联网搜索基钦周期和库兹涅茨周期资料，撰写 05-kitchin-cycle/ 和 06-kuznets-cycle/ 下的全部文档
    status: completed
    dependencies:
      - create-skeleton
  - id: research-minsky
    content: 联网搜索明斯基金融不稳定假说资料，撰写 07-minsky-moment/ 下的全部文档
    status: completed
    dependencies:
      - create-skeleton
  - id: research-gold-oil
    content: 联网搜索黄金与石油的经济周期资料，撰写 08-gold-cycle/ 和 09-oil-cycle/ 下的全部文档
    status: completed
    dependencies:
      - create-skeleton
  - id: research-coal-metals
    content: 联网搜索煤炭与工业金属的经济周期资料，撰写 10-coal-cycle/ 和 11-industrial-metals/ 下的全部文档
    status: completed
    dependencies:
      - create-skeleton
  - id: research-pig-housing
    content: 联网搜索猪周期与房价周期资料，撰写 12-pig-cycle/ 和 13-housing-cycle/ 下的全部文档
    status: completed
    dependencies:
      - create-skeleton
  - id: finalize-skill
    content: 完善 SKILL.md 总览内容（全景图、知识领域列表、文档索引表），确保所有交叉引用链接正确
    status: completed
    dependencies:
      - research-overview
      - research-tao-schumpeter
      - research-kondratieff-juglar
      - research-kitchin-kuznets
      - research-minsky
      - research-gold-oil
      - research-coal-metals
      - research-pig-housing
---

## 用户需求

创建一个新的 skill 目录 `skills/economic-cycles/`，用于系统性研究经济周期理论，并将理论与大宗商品/资产价格的实际周期表现相结合，参照现有 `ai-infra` skill 的目录结构和文档风格。

## 产品概述

一个经济周期理论与大宗商品/资产价格周期研究的系统性知识库，以 Markdown 文档形式组织，分为两大板块：理论篇和实证篇。所有内容为 Markdown 总结文档，附带来源链接。采用联网搜索（模拟 NotebookLM 的 deep research 方式）收集学术论文、中英文博客/文章、百科资源等，整理后保存到本地。

## 核心功能

### Part I - 经济周期理论篇

1. **经济周期总论/导读**：经济周期概念全景，各周期理论概览与对比，嵌套关系图
2. **涛动周期（周金涛）**：康波周期在中国的应用、经典语录与预测回顾
3. **熊彼特经济周期**：创造性破坏理论、三周期嵌套模型、技术创新驱动长波
4. **康德拉季耶夫长波（50-60年）**：五次长波的划分与特征、技术革命与长波的关系
5. **朱格拉周期（7-11年）**：固定资本投资周期、与企业盈利/信贷扩张的关系
6. **基钦周期（3-5年）**：库存周期机制、库存投资的四阶段
7. **库兹涅茨周期（15-25年）**：建筑/房地产周期、人口结构与城市化驱动
8. **明斯基金融不稳定假说**：三类融资结构、明斯基时刻

### Part II - 大宗商品与资产价格周期研究篇

9. **黄金与经济周期**：避险属性、与康波/美元周期/通胀周期的关系、金价长期趋势
10. **石油与经济周期**：石油超级周期、OPEC供给侧、地缘政治冲击、与朱格拉/康波的关系
11. **煤炭与经济周期**：煤炭产能周期、与工业化/能源转型的关系、中国煤炭周期特征
12. **工业金属与经济周期**：铜/铝/铁矿石等、与基钦库存周期/朱格拉投资周期的关系
13. **猪周期**：能繁母猪→生猪供给 3-4 年周期、与基钦周期的类比、中国猪周期历史回顾
14. **房价与经济周期**：与库兹涅茨建筑周期、人口周期、信贷周期/明斯基时刻的关系、中美日房价周期对比

每个章节包含：理论背景与核心观点、关键人物与代表作、历史实证与数据、与其他周期的关系、来源链接汇总

## 技术栈

- 内容格式：Markdown（.md）
- 项目框架：遵循现有 Anthropic Skills 目录结构规范
- 联网资料获取：通过 web_search + web_fetch 进行 deep research 式资料收集

## 实现方案

### 策略

参照 `skills/ai-infra/` 的成熟目录组织模式，创建 `skills/economic-cycles/` 作为独立 skill。目录结构采用编号递增的章节形式，每个章节包含一个索引 `.md` 文件和一个同名子目录，子目录内放置 README.md（章节总览导航）及编号的子文档。

### 关键决策

1. **目录结构完全对齐 ai-infra 模式**：`SKILL.md` 作为入口 → `references/` 下编号章节 → 每个章节有索引 .md + 子目录。

2. **联网搜索策略（模拟 Deep Research）**：对每个主题分别执行中文和英文搜索，搜索维度：理论概述、关键人物与代表作、历史实证、学术论文、中文分析文章。获取搜索结果后用 web_fetch 抓取高质量页面的详细内容，整理提炼为结构化 Markdown，附注来源 URL。

3. **内容编号规划**：

- Part I 理论篇：00 总论, 01 涛动周期, 02 熊彼特, 03 康波, 04 朱格拉, 05 基钦, 06 库兹涅茨, 07 明斯基
- Part II 实证篇：08 黄金, 09 石油, 10 煤炭, 11 工业金属, 12 猪周期, 13 房价

4. **文档风格**：中文写作，emoji 标记章节，包含学习目标、核心概念速览，子文档导航表，交叉引用链接

## 目录结构

```
skills/economic-cycles/
├── SKILL.md
├── references/
│   ├── 00-overview.md
│   ├── 00-overview/
│   │   ├── README.md
│   │   ├── 01-what-is-economic-cycle.md
│   │   └── 02-cycle-comparison.md
│   ├── 01-tao-cycle.md
│   ├── 01-tao-cycle/
│   │   ├── README.md
│   │   ├── 01-zhou-jintao-theory.md
│   │   └── 02-tao-cycle-practice.md
│   ├── 02-schumpeter-cycle.md
│   ├── 02-schumpeter-cycle/
│   │   ├── README.md
│   │   ├── 01-creative-destruction.md
│   │   └── 02-three-cycle-model.md
│   ├── 03-kondratieff-wave.md
│   ├── 03-kondratieff-wave/
│   │   ├── README.md
│   │   ├── 01-five-waves.md
│   │   └── 02-evidence-and-debate.md
│   ├── 04-juglar-cycle.md
│   ├── 04-juglar-cycle/
│   │   ├── README.md
│   │   ├── 01-investment-mechanism.md
│   │   └── 02-juglar-in-practice.md
│   ├── 05-kitchin-cycle.md
│   ├── 05-kitchin-cycle/
│   │   ├── README.md
│   │   ├── 01-inventory-mechanism.md
│   │   └── 02-kitchin-indicators.md
│   ├── 06-kuznets-cycle.md
│   ├── 06-kuznets-cycle/
│   │   ├── README.md
│   │   ├── 01-real-estate-cycle.md
│   │   └── 02-urbanization-drive.md
│   ├── 07-minsky-moment.md
│   ├── 07-minsky-moment/
│   │   ├── README.md
│   │   ├── 01-financial-instability.md
│   │   └── 02-minsky-moments-history.md
│   ├── 08-gold-cycle.md
│   ├── 08-gold-cycle/
│   │   ├── README.md
│   │   ├── 01-gold-safe-haven.md
│   │   └── 02-gold-kondratieff.md
│   ├── 09-oil-cycle.md
│   ├── 09-oil-cycle/
│   │   ├── README.md
│   │   ├── 01-oil-super-cycle.md
│   │   └── 02-oil-geopolitics.md
│   ├── 10-coal-cycle.md
│   ├── 10-coal-cycle/
│   │   ├── README.md
│   │   ├── 01-coal-capacity-cycle.md
│   │   └── 02-coal-china.md
│   ├── 11-industrial-metals.md
│   ├── 11-industrial-metals/
│   │   ├── README.md
│   │   ├── 01-copper-aluminum-cycle.md
│   │   └── 02-china-demand.md
│   ├── 12-pig-cycle.md
│   ├── 12-pig-cycle/
│   │   ├── README.md
│   │   ├── 01-pig-cycle-mechanism.md
│   │   └── 02-pig-cycle-china.md
│   ├── 13-housing-cycle.md
│   └── 13-housing-cycle/
│       ├── README.md
│       ├── 01-housing-kuznets.md
│       └── 02-housing-global-comparison.md
```