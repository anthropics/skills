---
name: skill-auto-installer
description: 自然语言意图分析 → 技能推荐 → 自动安装。当你描述需求时，Claude 自动分析意图、从市场中发现匹配的技能、安装后调用。
type: meta
---

# Skill Auto-Installer

## 核心行为

当用户用自然语言描述需求（如"帮我做一份 PDF 报告"、"分析这个 Excel"、"设计前端页面"），你必须执行以下流程：

### Phase 1: 意图分析

从用户的自然语言中提取任务域。对照下表：

| 意图关键词 | 任务域 | 推荐技能 |
|-----------|--------|---------|
| PDF、生成报告、导出pdf、打印 | PDF 文档 | `pdf` |
| Excel、xlsx、表格、数据导出、csv | Excel 文档 | `xlsx` |
| PPT、演示文稿、幻灯片、presentation | PPT 文档 | `pptx` |
| Word、docx、文档、合同、简历 | Word 文档 | `docx` |
| 前端、页面、UI、组件、设计稿、landing | 前端设计 | `frontend-design` |
| 算法、分形、生成艺术、creative coding | 算法艺术 | `algorithmic-art` |
| Canvas、海报、视觉设计、图形 | 视觉设计 | `canvas-design` |
| 品牌、logo、配色、风格指南 | 品牌设计 | `brand-guidelines` |
| 主题、暗色模式、样式、CSS变量 | 主题样式 | `theme-factory` |
| MCP、server、工具开发、集成 | MCP 开发 | `mcp-builder` |
| Claude API、SDK、模型调用、prompt | API 开发 | `claude-api` |
| 测试、E2E、Playwright、浏览器测试 | Web 测试 | `webapp-testing` |
| 网页构件、artifact、交互组件 | Web 构件 | `web-artifacts-builder` |
| Slack、GIF、动图 | Slack GIF | `slack-gif-creator` |
| 内部通讯、公告、通知 | 内部通讯 | `internal-comms` |
| 文档协作、写作、撰写 | 文档协作 | `doc-coauthoring` |
| 创建技能、自定义技能 | 技能创建 | `skill-creator` |

### Phase 2: 检查安装状态

对匹配的技能，检查是否已安装：

```bash
ls ~/.claude/skills/<skill-name>/ 2>/dev/null && echo "INSTALLED" || echo "MISSING"
```

### Phase 3: 自动安装

如果技能缺失，从 marketplace 复制：

```bash
# 搜索所有 marketplace 中的该技能
find ~/.claude/plugins/marketplaces/ -maxdepth 3 -type d -name "<skill-name>" 2>/dev/null

# 如果找到，复制到 skills 目录
cp -r <source-path> ~/.claude/skills/<skill-name>
```

### Phase 4: 调用技能

安装完成后，立即通过 Skill 工具调用该技能，使用用户最初的自然语言请求。

## 重要规则

1. **静默安装**: 不要在安装过程中询问用户"是否安装"，直接安装。只在安装完成后告知用户安装了哪些技能。
2. **批量匹配**: 一个用户请求可能匹配多个技能（如"设计前端页面并导出PDF"），全部安装。
3. **优先 marketplace**: 始终从已克隆的 marketplace 复制，不尝试 `npx skills add`（那需要独立仓库）。
4. **安装后立即使用**: 技能安装完成后，必须调用该技能来完成用户的任务。
5. **记录日志**: 每次安装后在 `~/.claude/skill-auto-installer.log` 追加一行：`[YYYY-MM-DD HH:MM] <skill-name> — <触发关键词>`
