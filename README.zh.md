<!--
IMPORTANT: This file is a localized version of README.md. 
When updating README.md, please ensure that the corresponding changes are also applied to this file to maintain parity.
-->

> **注意：** 本仓库包含 Anthropic 为 Claude 实现的“技能”(Skills)。如需了解关于 Agent Skills 标准的信息，请参阅 [agentskills.io](http://agentskills.io)。

# 技能 (Skills)

<p align="center">
  <a href="README.md">English</a> ·
  <strong>中文</strong>
</p>

技能是由一系列指令、脚本和资源组成的文件夹，Claude 可以动态加载它们以提高在特定专门任务上的表现。技能教会 Claude 如何以可重复的方式完成特定任务，无论是使用贵公司的品牌指南创建文档、使用您组织特定的工作流分析数据，还是自动化个人任务。

获取更多信息，请查阅：
- [什么是技能？](https://support.claude.com/en/articles/12512176-what-are-skills)
- [在 Claude 中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [如何创建自定义技能](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [使用 Agent Skills 为智能体装备真实世界的能力](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)

# 关于本仓库

本仓库包含了一系列技能示例，展示了 Claude 技能系统的潜力。这些技能涵盖了从创意应用（艺术、音乐、设计）到技术任务（测试 Web 应用、生成 MCP 服务器），再到企业工作流（内部沟通、品牌建设等）的各个方面。

每个技能都是自包含的，位于其独立的文件夹中，其中包含一个 `SKILL.md` 文件，里面记录了 Claude 所使用的指令和元数据。您可以浏览这些技能，为创建自己的技能获取灵感，或者了解不同的模式和方法。

本仓库中的许多技能都是开源的 (Apache 2.0 许可证)。我们还在 [`skills/docx`](./skills/docx)、[`skills/pdf`](./skills/pdf)、[`skills/pptx`](./skills/pptx) 和 [`skills/xlsx`](./skills/xlsx) 子文件夹中包含了用于驱动 [Claude 文件生成能力](https://www.anthropic.com/news/create-files)底层运作的文档创建和编辑技能。这些技能是“源码可用 (source-available)”的，虽然并非纯粹意义上的开源，但我们希望将其分享给开发者，作为参考资料，以展示在生产级 AI 应用程序中积极使用的复杂技能。

## 免责声明

**这些技能仅供演示和教育目的使用。** 虽然 Claude 中可能具备其中的某些能力，但您从 Claude 获得的实际实现和行为可能与这些技能中展示的内容有所不同。这些技能旨在说明使用模式和可能性。在依赖它们执行关键任务之前，请始终在您自己的环境中对技能进行全面测试。

# 技能集 (Skill Sets)
- [./skills](./skills): 创意与设计、开发与技术、企业与沟通以及文档处理的技能示例
- [./spec](./spec): Agent Skills 规范
- [./template](./template): 技能模板

# 在 Claude Code, Claude.ai 和 API 中体验

## Claude Code
您可以在 Claude Code 中运行以下命令，将此仓库注册为 Claude Code 插件市场 (Plugin marketplace)：
```
/plugin marketplace add anthropics/skills
```

然后，安装特定的一组技能：
1. 选择 `Browse and install plugins`
2. 选择 `anthropic-agent-skills`
3. 选择 `document-skills` 或 `example-skills`
4. 选择 `Install now`

或者，直接通过以下命令安装任一插件：
```
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

安装插件后，您只需提及它即可使用该技能。例如，如果您从市场安装了 `document-skills` 插件，您可以要求 Claude Code 执行类似这样的操作："Use the PDF skill to extract the form fields from `path/to/some-file.pdf`" (使用 PDF 技能从 `path/to/some-file.pdf` 提取表单字段)。

## Claude.ai

这些示例技能已经可供 Claude.ai 的付费计划用户使用。

要使用此仓库中的任何技能或上传自定义技能，请遵循 [在 Claude 中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude#h_a4222fa77b) 中的说明。

## Claude API

您可以通过 Claude API 使用 Anthropic 预构建的技能，并上传自定义技能。请参阅 [Skills API 快速入门](https://docs.claude.com/en/api/skills-guide#creating-a-skill) 了解更多信息。

# 创建一个基本技能

创建技能非常简单——只需一个包含 `SKILL.md` 文件的文件夹，文件中包含 YAML 前言元数据 (frontmatter) 和具体的指令。您可以使用此仓库中的 **template-skill** 作为起点：

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

YAML 前言仅需要两个字段：
- `name` - 技能的唯一标识符（小写，空格用连字符代替）
- `description` - 对技能功能和使用时机的完整描述

下方的 Markdown 内容包含了 Claude 将遵循的指令、示例和指南。如需更多详情，请参阅 [如何创建自定义技能](https://support.claude.com/en/articles/12512198-creating-custom-skills)。

# 合作伙伴技能 (Partner Skills)

技能是教会 Claude 如何更好地使用特定软件的绝佳方式。当我们看到来自合作伙伴的出色技能示例时，我们可能会在这里重点推荐它们：

- **Notion** - [适用于 Claude 的 Notion 技能](https://www.notion.so/notiondevs/Notion-Skills-for-Claude-28da4445d27180c7af1df7d8615723d0)

---

*本文档由 [@JasonYeYuhe](https://github.com/JasonYeYuhe) 翻译并维护。如果您发现任何翻译问题或需要补充内容，欢迎提交 Issue 或与我联系。*