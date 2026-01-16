> **说明：** 本仓库包含 Anthropic 对 Claude 技能（skills）的实现。关于 Agent Skills 标准，请参见 [agentskills.io](http://agentskills.io)。

# 技能
技能是由说明、脚本和资源组成的文件夹，Claude 会按需动态加载它们，以提升在特定任务上的表现。技能用于以可复用的方式教会 Claude 完成具体工作，例如：按你公司的品牌规范创建文档、用你组织的既定流程分析数据，或自动化个人任务。

更多信息：
- [什么是技能？](https://support.claude.com/en/articles/12512176-what-are-skills)
- [在 Claude 中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [如何创建自定义技能](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [用 Agent Skills 为现实世界装备智能体](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)

# 关于本仓库

本仓库包含一组技能，用于展示 Claude 的技能系统能够实现哪些能力。这些技能覆盖从创意应用（艺术、音乐、设计）到技术任务（测试 Web 应用、生成 MCP 服务器）再到企业工作流（沟通、品牌等）。

每个技能都自包含在单独的文件夹中，并包含一个 `SKILL.md` 文件，里面有 Claude 使用的说明和元数据。你可以浏览这些技能来获取灵感，或理解不同的模式与实现方式。

本仓库中的许多技能是开源的（Apache 2.0）。我们还在 [`skills/docx`](./skills/docx)、[`skills/pdf`](./skills/pdf)、[`skills/pptx`](./skills/pptx) 和 [`skills/xlsx`](./skills/xlsx) 子目录中包含了用于支撑 [Claude 文档能力](https://www.anthropic.com/news/create-files) 的文档创建与编辑技能。这些技能是“可查看源码”的（source-available），但并非开源；我们希望将其作为更复杂技能的参考示例，因为它们已在生产级 AI 应用中实际使用。

## 免责声明

**这些技能仅用于演示与教育用途。** 虽然其中部分能力可能在 Claude 中可用，但你从 Claude 获得的实现与行为可能与这些技能所展示的不同。这些技能旨在展示模式与可能性。在依赖它们处理关键任务之前，请务必在你自己的环境中充分测试。

# 技能集合
- [./skills](./skills)：创意与设计、开发与技术、企业与沟通，以及文档技能示例
- [./spec](./spec)：Agent Skills 规范
- [./template](./template)：技能模板

# 在 Claude Code、Claude.ai 和 API 中试用

## Claude Code
你可以通过在 Claude Code 中运行以下命令，将本仓库注册为 Claude Code 的插件市场（Plugin marketplace）：
```
/plugin marketplace add anthropics/skills
```

然后，安装一组特定技能：
1. 选择 `Browse and install plugins`
2. 选择 `anthropic-agent-skills`
3. 选择 `document-skills` 或 `example-skills`
4. 选择 `Install now`

或者，直接用下面命令安装任一插件：
```
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

安装插件后，你只需提到该技能即可使用。例如，如果你从市场安装了 `document-skills` 插件，你可以让 Claude Code 执行类似操作：“Use the PDF skill to extract the form fields from `path/to/some-file.pdf`”

## Claude.ai

这些示例技能在 Claude.ai 的付费套餐中已默认可用。

如需使用本仓库中的任意技能或上传自定义技能，请参考 [在 Claude 中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude#h_a4222fa77b) 的说明。

## Claude API

你可以通过 Claude API 使用 Anthropic 预置的技能并上传自定义技能。详情参见 [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill)。

# 创建一个基础技能

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

# 合作伙伴技能

技能是教会 Claude 更好使用特定软件的一种好方式。我们看到来自合作伙伴的优秀示例技能时，也可能会在这里进行展示：

- **Notion** - [Notion Skills for Claude](https://www.notion.so/notiondevs/Notion-Skills-for-Claude-28da4445d27180c7af1df7d8615723d0)

