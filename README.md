# Teaching AI Skills Marketplace

这是一个免费的技能市场，提供各种实用的 AI 技能集合，可以在 Claude Code 中使用。

> **说明：** 本仓库合并了 Anthropic 的示例技能和 Agent Skills 的技能集合，提供各种实用的 AI 技能，可以在 Claude Code、Claude.ai 和 API 中使用。关于 Agent Skills 标准，请参见 [agentskills.io](http://agentskills.io)。

## 什么是 Skills？

Skills 是由说明、脚本和资源组成的文件夹，Claude 会按需动态加载它们，以提升在特定任务上的表现。Skills 用于以可复用的方式教会 Claude 完成具体工作，例如：按你公司的品牌规范创建文档、用你组织的既定流程分析数据，或自动化个人任务。

### 更多信息

- [什么是技能？](https://support.claude.com/en/articles/12512176-what-are-skills)
- [在 Claude 中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [如何创建自定义技能](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [用 Agent Skills 为现实世界装备智能体](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)
- [Agent Skills 规范](https://agentskills.io/)

## 关于本仓库

本仓库包含一组技能，用于展示 Claude 的技能系统能够实现哪些能力。这些技能覆盖从创意应用（艺术、音乐、设计）到技术任务（测试 Web 应用、生成 MCP 服务器）再到企业工作流（沟通、品牌等），以及教学与教育场景。

每个技能都自包含在单独的文件夹中，并包含一个 `SKILL.md` 文件，里面有 Claude 使用的说明和元数据。你可以浏览这些技能来获取灵感，或理解不同的模式与实现方式。

本仓库中的许多技能是开源的（Apache 2.0）。我们还在 [`skills/docx`](./skills/docx)、[`skills/pdf`](./skills/pdf)、[`skills/pptx`](./skills/pptx) 和 [`skills/xlsx`](./skills/xlsx) 子目录中包含了用于支撑 [Claude 文档能力](https://www.anthropic.com/news/create-files) 的文档创建与编辑技能。这些技能是"可查看源码"的（source-available），但并非开源；我们希望将其作为更复杂技能的参考示例，因为它们已在生产级 AI 应用中实际使用。

### 免责声明

**这些技能仅用于演示与教育用途。** 虽然其中部分能力可能在 Claude 中可用，但你从 Claude 获得的实现与行为可能与这些技能所展示的不同。这些技能旨在展示模式与可能性。在依赖它们处理关键任务之前，请务必在你自己的环境中充分测试。

## 如何使用

### 在 Claude Code 中使用

#### 1. 注册 Marketplace

在 Claude Code 中运行以下命令，将本仓库注册为 Claude Code 的插件市场：

```
/plugin marketplace add teaching-ai/skills
```

> **注意**: 请将 `teaching-ai/skills` 替换为您的实际 GitHub 仓库路径（格式：`用户名/仓库名`）

#### 2. 安装插件

安装插件有两种方式：

**方式一：通过界面安装**

1. 选择 `Browse and install plugins`
2. 选择 `teaching-ai-skills`
3. 选择要安装的插件（见下方可用插件列表）
4. 选择 `Install now`

**方式二：通过命令安装**

直接使用命令安装插件：

```
/plugin install teaching-skills@teaching-ai-skills
/plugin install document-skills@teaching-ai-skills
/plugin install markdown-skills@teaching-ai-skills
/plugin install development-skills@teaching-ai-skills
/plugin install design-skills@teaching-ai-skills
/plugin install social-skills@teaching-ai-skills
/plugin install utility-skills@teaching-ai-skills
```

#### 3. 使用技能

安装插件后，您只需提到该技能即可使用。Claude 会根据技能描述自动判断何时使用该技能。

### 在 Claude.ai 中使用

这些示例技能在 Claude.ai 的付费套餐中已默认可用。

如需使用本仓库中的任意技能或上传自定义技能，请参考 [在 Claude 中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude#h_a4222fa77b) 的说明。

### 在 Claude API 中使用

你可以通过 Claude API 使用 Anthropic 预置的技能并上传自定义技能。详情参见 [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill)。

### 在其他平台使用

这些 skills 也可以在其他 AI 平台使用，如 Cursor、Trae、Qoder、CodeBuddy 等。

**详细说明：**
- [跨平台使用指南](./PLATFORM_GUIDE.md) - 完整的平台适配说明
- [平台适配器工具](./adapters/README.md) - 自动转换工具和示例
- [适配器示例](./adapters/EXAMPLES.md) - 转换后的示例文件

**快速转换：**
```bash
cd adapters
python convert_all.py ../skills ../adapters-output
```

## 可用插件和技能

本仓库的技能按功能分为 7 个插件类别，共包含 23 个技能：

### 1. teaching-skills（教学技能集合）

教学与教育相关技能集合，包括课程设计、学习评估、教学资源生成等。

#### course-designer（课程设计技能）

帮助设计和规划课程内容，包括课程大纲、学习目标、教学计划和评估方案。

**使用示例：**
- "使用课程设计技能帮我设计一门 Python 编程课程"
- "设计一个为期 8 周的机器学习入门课程"
- "创建一个关于 Web 开发的课程大纲"

#### learning-assessor（学习评估技能）

帮助创建学习评估工具，包括测验题目、评估标准、评分 rubric 和学习分析。

**使用示例：**
- "使用学习评估技能为我的课程创建一套测验题目"
- "设计一个评估学生学习效果的 rubric"
- "生成一份学习分析报告"

#### teaching-resource-generator（教学资源生成技能）

帮助生成各种教学资源，包括课件、练习题、教学案例、学习指南等。

**使用示例：**
- "使用教学资源生成技能为我的课程创建一套课件"
- "生成一些关于数据结构的练习题"
- "创建一个教学案例用于讲解设计模式"

### 2. document-skills（文档处理技能集合）

文档处理技能集合，支持 Excel、Word、PowerPoint、PDF 等办公文档的创建、编辑和处理。

#### docx（Word 文档处理）

创建、编辑和处理 Microsoft Word 文档。

**使用示例：**
- "Use the DOCX skill to create a new Word document"
- "Extract text from this Word document"
- "Format this document with headings and styles"

#### pptx（PowerPoint 演示文稿处理）

创建、编辑和处理 Microsoft PowerPoint 演示文稿。

**使用示例：**
- "Use the PPTX skill to create a presentation"
- "Add slides to this PowerPoint file"
- "Apply a theme to this presentation"

#### pdf（PDF 文档处理）

处理 PDF 文档，包括提取文本、填写表单、合并拆分等。

**使用示例：**
- "Use the PDF skill to extract the form fields from `path/to/some-file.pdf`"
- "Fill out this PDF form"
- "Merge multiple PDF files"

#### xlsx（Excel 表格处理）

创建、编辑和处理 Microsoft Excel 电子表格。

**使用示例：**
- "Use the XLSX skill to create a spreadsheet"
- "Analyze data in this Excel file"
- "Generate charts from this spreadsheet"

#### doc-coauthoring（文档协作）

支持多人协作编辑文档的功能。

**使用示例：**
- "Use the doc-coauthoring skill to prepare this document for collaboration"
- "Add comments and suggestions to this document"

### 3. markdown-skills（Markdown 技能集合）

Markdown 相关技能集合，包括 Mermaid 图表绘制等。

#### mermaid（Mermaid 图表绘制）

创建各种类型的 Mermaid 图表，包括流程图、时序图、类图、状态图、甘特图等。

**使用示例：**
- "使用 Mermaid 创建一个流程图"
- "绘制一个系统架构的 C4 图"
- "生成一个项目时间线的甘特图"
- "创建一个用户旅程图"

**支持的图表类型：**
- 流程图（flowchart）
- 时序图（sequence diagram）
- 类图（class diagram）
- 状态图（state diagram）
- 实体关系图（ER diagram）
- 用户旅程图（user journey）
- 甘特图（Gantt chart）
- 饼图（pie chart）
- 象限图（quadrant chart）
- Git 图（Git graph）
- C4 架构图（C4 diagram）
- 思维导图（mindmap）
- 时间线图（timeline）
- 桑基图（Sankey diagram）
- 以及其他多种图表类型

### 4. development-skills（开发技能集合）

开发技能集合，包括代码生成、测试编写、文档构建、MCP 构建器、Web 开发、前端设计等。

#### code-generator（代码生成技能）

帮助生成高质量的代码，支持多种编程语言，遵循最佳实践和设计模式。

**使用示例：**
- "使用代码生成技能生成一个用户认证的 Python 类"
- "创建一个 RESTful API 的 Node.js 实现"
- "生成一个符合 SOLID 原则的 Java 类"

#### test-writer（测试编写技能）

帮助编写单元测试、集成测试和端到端测试。

**使用示例：**
- "为这个函数编写单元测试"
- "创建集成测试来验证 API 接口"
- "生成端到端测试用例"

#### documentation-builder（文档构建技能）

帮助生成技术文档，包括 API 文档、用户手册、开发指南、README 等。

**使用示例：**
- "使用文档构建技能为我的项目生成 API 文档"
- "创建一个用户使用手册"
- "编写开发环境搭建指南"

#### mcp-builder（MCP 构建器）

帮助创建和配置 Model Context Protocol (MCP) 服务器。

**使用示例：**
- "使用 MCP 构建器创建一个新的 MCP 服务器"
- "配置 MCP 服务器的工具和资源"
- "生成 MCP 服务器的代码模板"

#### webapp-testing（Web 应用测试）

帮助测试 Web 应用程序，包括功能测试、性能测试等。

**使用示例：**
- "测试这个 Web 应用的功能"
- "检查这个网站的响应时间"
- "验证这个应用的跨浏览器兼容性"

#### frontend-design（前端设计）

创建高质量的前端界面，避免通用的 AI 美学，生成具有独特设计感的代码。

**使用示例：**
- "使用前端设计技能创建一个登录页面"
- "设计一个现代化的仪表板界面"
- "创建一个响应式的产品展示页面"

#### web-artifacts-builder（Web 工件构建器）

使用现代前端技术（React、Tailwind CSS、shadcn/ui）创建复杂的多组件 HTML 工件。

**使用示例：**
- "使用 Web 工件构建器创建一个交互式数据可视化工具"
- "构建一个带有状态管理的单页应用"
- "创建一个使用 shadcn/ui 组件的复杂界面"

#### theme-factory（主题工厂）

为工件应用主题样式，包括 10 种预设主题，可以应用到幻灯片、文档、报告、HTML 落地页等。

**使用示例：**
- "为这个演示文稿应用 Ocean Depths 主题"
- "使用 Modern Minimalist 主题样式化这个文档"
- "为这个网页应用 Golden Hour 主题"

### 5. design-skills（设计技能集合）

设计与创意技能集合，包括算法艺术、品牌指南、画布设计等。

#### algorithmic-art（算法艺术）

使用 p5.js 创建算法艺术，支持种子随机数和交互式参数探索。

**使用示例：**
- "使用算法艺术技能创建一个生成式艺术作品"
- "生成一个基于粒子系统的可视化"
- "创建一个流动场效果的艺术作品"

#### brand-guidelines（品牌指南）

应用 Anthropic 官方品牌颜色和排版到任何工件。

**使用示例：**
- "使用品牌指南技能应用品牌样式到这个文档"
- "为这个演示文稿应用品牌颜色"
- "使用品牌字体格式化这个文档"

#### canvas-design（画布设计）

在 HTML Canvas 上创建高质量的设计和可视化。

**使用示例：**
- "使用画布设计技能创建一个数据可视化图表"
- "在 Canvas 上绘制一个交互式图形"
- "创建一个 Canvas 动画效果"

### 6. social-skills（社交技能集合）

社交与协作技能集合，包括内部沟通、Slack GIF 创建等。

#### internal-comms（内部沟通）

帮助编写各种内部沟通文档，包括状态报告、领导更新、3P 更新、公司通讯、FAQ 等。

**使用示例：**
- "使用内部沟通技能编写一份项目状态报告"
- "创建一个公司通讯稿"
- "编写一份 FAQ 文档"

#### slack-gif-creator（Slack GIF 创建器）

创建用于 Slack 的 GIF 动图。

**使用示例：**
- "使用 Slack GIF 创建器创建一个欢迎动画"
- "生成一个用于 Slack 消息的 GIF"
- "创建一个通知动画 GIF"

### 7. utility-skills（工具技能集合）

工具与实用技能集合，包括技能创建器等。

#### skill-creator（技能创建器）

指导如何创建有效的技能，扩展 Claude 的能力。

**使用示例：**
- "使用技能创建器帮助我创建一个新技能"
- "如何设计一个技能的结构"
- "创建一个技能的最佳实践是什么"

## 项目结构

```
.
├── .claude-plugin/
│   └── marketplace.json          # Marketplace 配置文件
├── skills/                        # Skills 目录
│   ├── teaching-skills/          # 教学技能
│   │   ├── course-designer/
│   │   ├── learning-assessor/
│   │   └── teaching-resource-generator/
│   ├── document-skills/          # 文档处理技能
│   │   ├── docx/
│   │   ├── pptx/
│   │   ├── pdf/
│   │   ├── xlsx/
│   │   └── doc-coauthoring/
│   ├── markdown-skills/          # Markdown 技能
│   │   └── mermaid/
│   ├── development-skills/       # 开发技能
│   │   ├── code-generator/
│   │   ├── test-writer/
│   │   ├── documentation-builder/
│   │   ├── mcp-builder/
│   │   ├── webapp-testing/
│   │   ├── frontend-design/
│   │   ├── web-artifacts-builder/
│   │   └── theme-factory/
│   ├── design-skills/            # 设计技能
│   │   ├── algorithmic-art/
│   │   ├── brand-guidelines/
│   │   └── canvas-design/
│   ├── social-skills/            # 社交技能
│   │   ├── internal-comms/
│   │   └── slack-gif-creator/
│   └── utility-skills/           # 工具技能
│       └── skill-creator/
├── spec/                          # Agent Skills 规范
├── template/                      # 技能模板
└── README.md                      # 本文件
```

## 如何创建新技能

### 创建一个基础技能

创建技能非常简单——只需要一个包含带 YAML frontmatter 的 `SKILL.md` 文件的文件夹即可。你可以使用本仓库中的 **template-skill** 作为起点：

```markdown
---
name: my-skill-name
description: A clear description of what this skill does and when to use it
---

# My Skill Name

[Add your instructions here that Claude will follow when this skill is active]

## Examples
- Example usage 1
- Example usage 2

## Guidelines
- Guideline 1
- Guideline 2
```

frontmatter 只需要两个字段：
- `name` - 你的技能的唯一标识符（小写，空格用连字符）
- `description` - 对该技能做什么、何时使用的完整描述

下面的 Markdown 内容包含了该技能激活时 Claude 要遵循的说明、示例和指南。更多细节请参见 [如何创建自定义技能](https://support.claude.com/en/articles/12512198-creating-custom-skills)。

### 技能结构

每个技能包含：
- `SKILL.md` - 给智能体的说明（必需）
- `scripts/` - 自动化辅助脚本（可选）
- `references/` - 支撑文档（可选）
- `assets/` - 资源文件（可选）

### 添加新技能的步骤

#### 1. 创建 Skill 目录

在 `skills/` 目录下创建新的技能目录：

```bash
mkdir -p skills/your-skill-name
```

#### 2. 创建 SKILL.md 文件

每个技能必须包含一个 `SKILL.md` 文件，格式如上所示。

#### 3. 更新 marketplace.json

在 `.claude-plugin/marketplace.json` 中添加新技能到相应的插件中：

```json
{
  "plugins": [
    {
      "name": "your-plugin-name",
      "description": "插件描述",
      "source": "./",
      "strict": false,
      "skills": [
        "./skills/your-skill-name"
      ]
    }
  ]
}
```

#### 4. 提交到 GitHub

将更改提交并推送到 GitHub 仓库：

```bash
git add .
git commit -m "Add new skill: your-skill-name"
git push
```

## Marketplace 配置文件说明

`.claude-plugin/marketplace.json` 文件定义了 marketplace 的元数据和可用的插件：

```json
{
  "name": "marketplace-name",        // Marketplace 名称
  "owner": {                         // 所有者信息
    "name": "Owner Name",
    "email": "owner@example.com"
  },
  "metadata": {                      // 元数据
    "description": "Marketplace 描述",
    "version": "1.0.0"
  },
  "plugins": [                       // 插件列表
    {
      "name": "plugin-name",         // 插件名称
      "description": "插件描述",
      "source": "./",                // 源代码路径
      "strict": false,               // 是否严格模式
      "skills": [                    // 技能列表
        "./skills/skill1",
        "./skills/skill2"
      ]
    }
  ]
}
```

## 工作原理

1. **Marketplace 注册**: 当您运行 `/plugin marketplace add teaching-ai/skills` 时，Claude Code 会：
   - 从 GitHub 仓库获取 `.claude-plugin/marketplace.json` 文件
   - 解析 marketplace 配置
   - 将 marketplace 添加到可用列表

2. **插件安装**: 当您安装插件时，Claude Code 会：
   - 下载插件中定义的所有 skills
   - 将 skills 存储到本地
   - 使 skills 可用于 Claude

3. **技能使用**: 当您使用技能时，Claude 会：
   - 根据技能描述判断是否使用该技能
   - 加载技能的 `SKILL.md` 文件
   - 按照技能说明执行任务

## 最佳实践

### Skill 设计

- **清晰的描述**: `description` 字段应该清楚地说明何时使用该技能
- **简洁的内容**: 保持 `SKILL.md` 简洁，避免不必要的冗长（建议控制在 500 行以内）
- **结构化组织**: 使用清晰的章节和结构
- **实用示例**: 提供实际可用的示例
- **渐进式披露**: 将详细参考资料放在单独文件中，按需加载

### Marketplace 组织

- **逻辑分组**: 将相关技能组织到同一个插件中
- **清晰的命名**: 使用清晰、描述性的名称
- **版本管理**: 在 `metadata` 中维护版本号

## 许可证

本仓库中的许多技能采用 Apache 2.0 许可证。文档处理技能（docx、pdf、pptx、xlsx）是"可查看源码"的（source-available），但并非开源。详见各技能目录中的 LICENSE 文件。

## 贡献

欢迎贡献新的技能！请遵循以下步骤：

1. Fork 本仓库
2. 创建新的技能或改进现有技能
3. 提交 Pull Request

## 合作伙伴技能

技能是教会 Claude 更好使用特定软件的一种好方式。我们看到来自合作伙伴的优秀示例技能时，也可能会在这里进行展示：

- **Notion** - [Notion Skills for Claude](https://www.notion.so/notiondevs/Notion-Skills-for-Claude-28da4445d27180c7af1df7d8615723d0)

## 跨平台适配

本仓库提供了将 skills 适配到其他平台的工具和示例：

- **适配器工具**: `adapters/` 目录包含转换脚本
- **平台支持**: Cursor、Trae、Qoder、CodeBuddy
- **示例文件**: `adapters/examples/` 包含转换后的示例

详细说明请参考：
- [跨平台使用指南](./PLATFORM_GUIDE.md)
- [适配器工具文档](./adapters/README.md)
- [适配器示例](./adapters/EXAMPLES.md)

**快速转换：**
```bash
cd adapters
python convert_all.py ../skills ../adapters-output
```

## 参考资源

- [Agent Skills 规范](https://agentskills.io/)
- [Claude Skills 文档](https://support.claude.com/en/articles/12512176-what-are-skills)
- [在 Claude 中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [如何创建自定义技能](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [用 Agent Skills 为现实世界装备智能体](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)
- [Anthropic Skills 示例](https://github.com/anthropics/skills)
- [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill)

## 联系方式

如有问题或建议，请通过 GitHub Issues 联系我们。
