> **注意：** 此仓库包含Anthropic为Claude实现的技能。如需了解Agent Skills标准，请访问[agentskills.io](http://agentskills.io)。

# 技能
技能是包含指令、脚本和资源的文件夹，Claude动态加载这些内容以提高在特定任务上的性能。技能以可重复的方式教Claude如何完成特定任务，无论是使用您公司品牌指南创建文档、使用您组织特定工作流程分析数据，还是自动化个人任务。

有关更多信息，请查看：
- [什么是技能？](https://support.claude.com/en/articles/12512176-what-are-skills)
- [在Claude中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude)
- [如何创建自定义技能](https://support.claude.com/en/articles/12512198-creating-custom-skills)
- [用Agent Skills为现实世界配备代理](https://anthropic.com/engineering/equipping-agents-for-the-real-world-with-agent-skills)

# 关于此仓库

此仓库包含展示Claude技能系统可能性的技能。这些技能涵盖从创意应用（艺术、音乐、设计）到技术任务（测试Web应用、MCP服务器生成）再到企业工作流程（通信、品牌等）的各个领域。

每个技能都自包含在其自己的文件夹中，包含一个`SKILL.md`文件，其中包含Claude使用的指令和元数据。浏览这些技能可以为您的技能创作提供灵感，或了解不同的模式和方法。

此仓库中的许多技能都是开源的（Apache 2.0）。我们还在[`skills/docx`](./skills/docx)、[`skills/pdf`](./skills/pdf)、[`skills/pptx`](./skills/pptx)和[`skills/xlsx`](./skills/xlsx)子文件夹中包含了为[Claude文档功能](https://www.anthropic.com/news/create-files)提供动力的文档创建和编辑技能。这些是源码可用而不是开源的，但我们希望将其作为复杂技能的参考分享给开发者，这些技能在生产AI应用中被积极使用。

## 免责声明

**这些技能仅供演示和教育目的提供。** 虽然Claude中可能提供其中的一些功能，但您从Claude获得的实现和行为可能与这些技能中显示的不同。这些技能旨在说明模式和可能性。在依赖它们执行关键任务之前，请务必在您自己的环境中彻底测试技能。

# 技能集
- [./skills](./skills)：创意与设计、开发与技术、企业与通信以及文档技能的示例
- [./spec](./spec)：Agent Skills规范
- [./template](./template)：技能模板

# 在Claude Code、Claude.ai和API中试用

## Claude Code
您可以通过在Claude Code中运行以下命令将此仓库注册为Claude Code插件市场：
```
/plugin marketplace add anthropics/skills
```

然后，安装特定的技能集：
1. 选择`浏览和安装插件`
2. 选择`anthropic-agent-skills`
3. 选择`document-skills`或`example-skills`
4. 选择`立即安装`

或者，直接安装任一插件：
```
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
```

安装插件后，您只需提及即可使用技能。例如，如果您从市场安装了`document-skills`插件，可以要求Claude Code执行类似的操作："使用PDF技能从`path/to/some-file.pdf`中提取表单字段"

## Claude.ai

这些示例技能在Claude.ai的付费计划中都已可用。

要使用此仓库中的任何技能或上传自定义技能，请按照[在Claude中使用技能](https://support.claude.com/en/articles/12512180-using-skills-in-claude#h_a4222fa77b)的说明操作。

## Claude API

您可以通过Claude API使用Anthropic的预构建技能并上传自定义技能。有关更多信息，请参阅[技能API快速入门](https://docs.claude.com/en/api/skills-guide#creating-a-skill)。

# 创建基本技能

技能创建非常简单 - 只需一个包含YAML前置数据和指令的`SKILL.md`文件的文件夹。您可以使用此仓库中的**template-skill**作为起点：

```markdown
---
name: my-skill-name
description: 清晰描述此技能的功能和使用时机
---

# 我的技能名称

[在此添加Claude激活此技能时将遵循的指令]

## 示例
- 示例用法1
- 示例用法2

## 指南
- 指南1
- 指南2
```

前置数据只需要两个字段：
- `name` - 您的技能的唯一标识符（小写，连字符代替空格）
- `description` - 完整描述技能的功能和使用时机

下面的Markdown内容包含Claude将遵循的指令、示例和指南。有关详细信息，请参阅[如何创建自定义技能](https://support.claude.com/en/articles/12512198-creating-custom-skills)。

# 合作伙伴技能

技能是教Claude更好地使用特定软件的好方法。随着我们看到来自合作伙伴的出色示例技能，我们可能会在这里突出显示其中一些：

- **Notion** - [Claude的Notion技能](https://www.notion.so/notiondevs/Notion-Skills-for-Claude-28da4445d27180c7af1df7d8615723d0)
