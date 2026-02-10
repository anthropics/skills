# 🚀 Agent Skills 实战指南

完整指南，帮助开发者掌握 Anthropic Agent Skills 的使用、创建和高级技巧。

---

## 目录

- [第一部分：入门指南](#第一部分入门指南)
  - [1. Agent Skills 简介](#1-agent-skills-简介)
  - [2. 安装与配置](#2-安装与配置)
  - [3. 快速开始](#3-快速开始)
- [第二部分：创意设计类技能](#第二部分创意设计类技能)
  - [4. algorithmic-art - 算法艺术生成器](#4-algorithmic-art---算法艺术生成器)
  - [5. canvas-design - 画布设计](#5-canvas-design---画布设计)
  - [6. frontend-design - 前端界面设计](#6-frontend-design---前端界面设计)
  - [7. brand-guidelines - 品牌风格指南](#7-brand-guidelines---品牌风格指南)
- [第三部分：文档处理类技能](#第三部分文档处理类技能)
  - [8. docx - Word 文档处理](#8-docx---word-文档处理)
  - [9. pdf - PDF 文档处理](#9-pdf---pdf-文档处理)
  - [10. pptx - 演示文稿创建](#10-pptx---演示文稿创建)
  - [11. xlsx - 电子表格处理](#11-xlsx---电子表格处理)
- [第四部分：开发工具类技能](#第四部分开发工具类技能)
  - [12. mcp-builder - MCP 服务器构建](#12-mcp-builder---mcp-服务器构建)
  - [13. skill-creator - 技能创建器](#13-skill-creator---技能创建器)
  - [14. webapp-testing - Web 应用测试](#14-webapp-testing---web-应用测试)
  - [15. web-artifacts-builder - Web 工件构建](#15-web-artifacts-builder---web-工件构建)
- [第五部分：沟通与主题类技能](#第五部分沟通与主题类技能)
  - [16. doc-coauthoring - 文档协作工作流](#16-doc-coauthoring---文档协作工作流)
  - [17. internal-comms - 内部沟通](#17-internal-comms---内部沟通)
  - [18. theme-factory - 主题工厂](#18-theme-factory---主题工厂)
  - [19. slack-gif-creator - Slack GIF 创建器](#19-slack-gif-creator---slack-gif-创建器)
- [第六部分：高级用法](#第六部分高级用法)
  - [20. 技能组合使用案例](#20-技能组合使用案例)
  - [21. 创建自定义技能完整教程](#21-创建自定义技能完整教程)
  - [22. 最佳实践与技巧](#22-最佳实践与技巧)
- [第七部分：附录](#第七部分附录)
  - [23. 常见问题与故障排除](#23-常见问题与故障排除)
  - [24. 参考资源](#24-参考资源)

---

# 第一部分：入门指南

## 1. Agent Skills 简介

### 1.1 什么是 Agent Skills

**Agent Skills** 是 Anthropic 为 Claude AI 设计的模块化扩展系统，通过动态加载的专业知识、工作流程和工具资源，将通用 AI 助手转变为具备特定领域能力的专业代理。

可以将 Skills 理解为：
- **插件/扩展**：类似浏览器扩展，为 Claude 添加新功能
- **入职指南**：为 Claude 提供特定领域的专业知识
- **工作流模板**：封装复杂的多步骤任务流程
- **工具适配器**：让 Claude 能够使用特定文件格式、API 或服务

**与传统 AI 助手的区别**：

| 传统 AI 助手 | Agent Skills |
|-------------|--------------|
| 通用知识，需要反复提示 | 封装的专业知识 |
| 每次对话从零开始 | 可重复的工作流程 |
| 无法访问外部工具 | 集成特定工具和 API |
| 上下文浪费 | 高效的上下文管理 |

### 1.2 发展历程

**2024年**：Anthropic 发布 Agent Skills 规范，标志着 AI 从"通用助手"向"专业代理"的转变。

**演进历程**：
```
通用 AI (2023)
    ↓
上下文学习 (In-Context Learning)
    ↓
函数调用 (Function Calling)
    ↓
Agent Skills (2024) ← 当前阶段
    ↓
未来：自主代理生态系统
```

这一演进的核心思想是：**让 AI 不仅仅更聪明，而是更有用**。

### 1.3 技术架构

#### 技能文件结构

每个技能是一个自包含的文件夹，必须包含 `SKILL.md` 文件：

```
skill-name/
├── SKILL.md (必需)
├── scripts/ (可选)
├── references/ (可选)
└── assets/ (可选)
```

#### SKILL.md 文件格式

```markdown
---
name: skill-name
description: 清晰描述技能的作用和使用场景
---

# 技能指令

[Markdown 格式的详细指令]

## 示例
- 示例用法 1
- 示例用法 2
```

**YAML 元数据字段**：
- `name`：技能的唯一标识符（小写，连字符分隔）
- `description`：技能描述，Claude 用此判断何时使用该技能

**Markdown 正文**：包含技能触发后才加载的指令、示例和指南。

#### 技能加载机制

1. **触发判断**：Claude 根据用户请求和 `description` 匹配相关技能
2. **动态加载**：匹配的技能正文被加载到上下文
3. **资源访问**：可选的脚本、参考文档和资产按需加载
4. **上下文共享**：所有技能共享系统提示、对话历史和用户请求

#### 与 Claude API 的集成

```python
import anthropic

client = anthropic.Anthropic()

message = client.messages.create(
    model="claude-sonnet-4-20250514",
    max_tokens=1024,
    tools=[
        {
            "name": "my-custom-skill",
            "description": "My custom skill description",
            "input_schema": {
                "type": "object",
                "properties": {
                    "param": {"type": "string"}
                }
            }
        }
    ],
    messages=[{"role": "user", "content": "Help me with..."}]
)
```

### 1.4 核心价值

1. **专业知识封装**
   - 将领域知识、公司规范、业务逻辑打包
   - 减少重复提示，提高一致性

2. **可重复的工作流程**
   - 标准化复杂任务的处理流程
   - 确保每次执行的质量

3. **工具集成能力**
   - 连接外部 API 和服务
   - 处理特定文件格式
   - 自动化重复性操作

4. **高效的上下文管理**
   - 按需加载，节省 token
   - 模块化组织，易于维护

### 1.5 快速示例

**示例：创建一个简单的"代码审查"技能**

```markdown
---
name: code-reviewer
description: 执行 Python 代码审查，检查代码质量、安全问题和性能优化机会
---

# 代码审查技能

## 审查标准

1. **代码质量**
   - 遵循 PEP 8 规范
   - 有意义的变量和函数名
   - 适当的注释

2. **安全问题**
   - SQL 注入风险
   - 硬编码的密钥
   - 不安全的函数使用

3. **性能优化**
   - 算法复杂度
   - 资源使用效率
   - 可优化的代码模式

## 输出格式

```markdown
## 代码审查结果

### 整体评价
[评分：优秀/良好/需改进]

### 发现的问题
1. [问题描述]
   - 位置：[行号]
   - 建议：[改进建议]

### 亮点
[代码中的优秀实践]
```
```

**使用前后对比**：

```bash
# 使用技能前
"请帮我审查这段 Python 代码，检查代码质量、安全问题和性能"
[需要多次交互，经常遗漏检查项]

# 使用技能后
"使用 code-reviewer 技能审查这段代码"
[一次性输出完整的结构化审查结果]
```

### 1.6 适用场景

**✅ 应该使用技能的场景**：
- 重复性任务（文档生成、代码审查、数据分析）
- 需要特定领域知识的任务（品牌规范、法律合规）
- 需要与外部工具交互的任务（API 调用、文件处理）
- 需要标准化输出的任务（报告格式、沟通模板）

**❌ 不需要技能的场景**：
- 一次性探索性任务
- 简单问答
- 创意性写作（无需特定格式）
- 快速原型设计

### 1.7 技能生态系统

#### 官方技能库

Anthropic 维护着多个官方技能集合：

| 技能集 | 内容 | 许可证 |
|--------|------|--------|
| **example-skills** | 创意、开发、沟通示例 | Apache 2.0 |
| **document-skills** | Word/PDF/PPT/Excel 处理 | 专有（参考） |

#### 社区技能

- GitHub 上的开源技能项目
- 合作伙伴技能（如 Notion Skills for Claude）
- 用户贡献的自定义技能

#### 创建自定义技能

开发者可以：
1. 基于 template-skill 创建
2. 参考现有技能的模式
3. 使用 skill-creator 技能指导创建

### 1.8 与其他框架对比

| 特性 | Agent Skills | LangChain Tools | AutoGPT Plugins |
|------|--------------|-----------------|-----------------|
| **设计目标** | 专业代理任务 | 通用工具调用 | 自主任务执行 |
| **知识封装** | 强（Markdown 指令） | 弱（代码定义） | 中等 |
| **易用性** | 高（YAML+Markdown） | 中（需编码） | 中 |
| **集成难度** | 低 | 高 | 高 |
| **上下文管理** | 优化（按需加载） | 手动管理 | 手动管理 |
| **开源** | 开源协议 | 开源（MIT） | 开源（MIT） |

**Agent Skills 的独特优势**：
- **人类可读的格式**：用 Markdown 而非代码定义技能
- **与 Claude 深度集成**：专为 Claude 设计的加载机制
- **模板化工作流**：支持复杂的多步骤流程
- **资源打包**：可包含脚本、文档和资产

### 1.9 技术限制

**上下文窗口限制**：
- 所有技能共享上下文窗口
- 技能指令 + 对话历史 + 用户请求 + 其他技能元数据
- **最佳实践**：保持技能指令简洁，仅包含必要信息

**技能数量限制**：
- 过多技能可能导致触发冲突
- **建议**：专注于核心技能，避免功能重叠

**性能考虑**：
- 动态加载有轻微延迟
- 大型技能文件可能影响响应速度
- **优化**：使用 `scripts/` 存放可执行代码而非指令

### 1.10 未来展望

**技能标准的发展**：
- 更丰富的元数据字段
- 技能依赖管理
- 版本控制机制

**生态系统扩展**：
- 更多官方技能
- 第三方技能市场
- 企业级技能管理平台

**与代理框架的融合**：
- 与 LangChain、AutoGPT 等框架的互操作性
- 跨平台的技能标准
- 标准化的技能协议

## 2. 安装与配置

本指南专注于在 **Windows** 系统上安装和配置 **Claude Code** 及 Agent Skills。

### 2.1 系统要求

#### 硬件要求
- **处理器**：x64 架构处理器（Intel 或 AMD）
- **内存**：至少 8 GB RAM（推荐 16 GB）
- **存储**：至少 500 MB 可用磁盘空间

#### 软件要求
- **操作系统**：Windows 10 或 Windows 11（推荐最新版本）
- **必需软件**：
  - **Node.js** 18.0 或更高版本（[下载地址](https://nodejs.org/)）
  - **Python** 3.8 或更高版本（[下载地址](https://www.python.org/)）
  - **Git**（[下载地址](https://git-scm.com/downloads)）

#### 可选软件
- **Visual Studio Code**（推荐用于编辑技能文件）
- **Windows Terminal**（更好的命令行体验）

### 2.2 安装 Claude Code

#### 步骤 1：下载 Claude Code

1. 访问 Anthropic 官方下载页面：https://claude.ai/download
2. 选择 Windows 版本
3. 下载安装包（`.exe` 文件）

#### 步骤 2：运行安装程序

1. 双击下载的 `.exe` 文件
2. 在 Windows SmartScreen 提示时点击"更多信息"→"仍要运行"
3. 按照安装向导完成安装：
   - 选择安装位置（默认：`C:\Users\[用户名]\AppData\Local\Claude`）
   - 选择创建桌面快捷方式（推荐）
   - 选择添加到 PATH（推荐）

#### 步骤 3：验证安装

打开 **Windows Terminal** 或 **命令提示符**：

```bash
# 检查 Claude Code 版本
claude --version

# 预期输出：
# Claude Code v1.x.x
```

**安装完成！** 现在您可以从以下方式启动 Claude Code：
- 桌面快捷方式
- Windows 开始菜单
- 命令行输入 `claude`

### 2.3 配置技能目录

#### 步骤 1：创建自定义技能目录

```bash
# 在用户目录下创建技能目录
mkdir %USERPROFILE%\.claude\skills
cd %USERPROFILE%\.claude\skills

# 创建子目录用于组织
mkdir custom
mkdir community
```

目录结构：
```
%USERPROFILE%\.claude\skills\
├── custom/          # 您的自定义技能
├── community/       # 社区技能
└── temp/           # 临时测试技能
```

#### 步骤 2：配置 Claude Code 识别技能目录

创建配置文件 `%USERPROFILE%\.claude\config.json`：

```json
{
  "skills": {
    "directories": [
      "%USERPROFILE%\\.claude\\skills\\custom",
      "%USERPROFILE%\\.claude\\skills\\community"
    ],
    "enabled": true
  }
}
```

**PowerShell 命令创建配置文件**：

```powershell
# 创建配置目录
mkdir $env:USERPROFILE\.claude -ErrorAction SilentlyContinue

# 创建配置文件
@'
{
  "skills": {
    "directories": [
      "$env:USERPROFILE\\.claude\\skills\\custom",
      "$env:USERPROFILE\\.claude\\skills\\community"
    ],
    "enabled": true
  }
}
'@ | Out-File -FilePath "$env:USERPROFILE\.claude\config.json" -Encoding utf8
```

#### 步骤 3：验证配置

```bash
# 检查配置文件
type %USERPROFILE%\.claude\config.json

# 预期输出：您创建的 JSON 配置
```

### 2.4 安装官方技能库

Claude Code 通过插件系统提供官方技能库。有两种安装方式：

#### 方法 1：使用插件市场（推荐）

```bash
# 1. 浏览并添加插件市场
/plugin marketplace add anthropics/skills

# 2. 查看可用技能集
/plugin marketplace list anthropics/skills

# 3. 安装示例技能集
/plugin install example-skills@anthropic-agent-skills

# 或安装文档技能集
/plugin install document-skills@anthropic-agent-skills
```

#### 方法 2：直接安装

```bash
# 直接安装特定技能集
/plugin install example-skills@anthropic-agent-skills
/plugin install document-skills@anthropic-agent-skills
```

#### 步骤 5：验证技能安装

```bash
# 列出已安装的插件
/plugin list

# 预期输出：
# 已安装的插件：
# - example-skills (anthropic-agent-skills)
# - document-skills (anthropic-agent-skills)
```

#### 步骤 6：测试技能功能

```bash
# 启动 Claude Code 交互模式
claude

# 测试技能（在 Claude 中输入）：
# "使用 algorithmic-art 技能创建一个流场艺术作品"
```

### 2.5 环境变量配置

#### 配置自定义技能路径（可选）

如果您希望使用非标准路径存放技能：

**Windows 系统环境变量**：

1. 打开"系统属性"→"高级"→"环境变量"
2. 在"用户变量"中新建：
   - 变量名：`CLAUDE_SKILLS_PATH`
   - 变量值：`D:\MySkills\Custom`

**或使用 PowerShell 命令**：

```powershell
[System.Environment]::SetEnvironmentVariable(
    "CLAUDE_SKILLS_PATH",
    "D:\MySkills\Custom",
    "User"
)
```

#### 配置 API 密钥（如需要）

如果您使用 Claude API，需要配置 API 密钥：

```bash
# 设置环境变量
setx ANTHROPIC_API_KEY "your-api-key-here"

# 或在当前会话中设置
set ANTHROPIC_API_KEY=your-api-key-here
```

### 2.6 目录结构最佳实践

#### 推荐的组织方式

```
%USERPROFILE%\.claude\skills\
├── custom/
│   ├── company-standards/
│   │   ├── SKILL.md
│   │   ├── templates/
│   │   └── references/
│   ├── development-workflows/
│   │   ├── code-review/
│   │   ├── testing/
│   │   └── deployment/
│   └── personal-tools/
│       ├── writing/
│       └── research/
├── community/
│   ├── algorithmic-art/
│   ├── frontend-design/
│   └── mcp-builder/
└── temp/
    ├── test-skill/
    └── experiments/
```

#### 技能命名规范

- 使用小写字母和连字符：`my-custom-skill`
- 避免使用下划线：`my_custom_skill`（不推荐）
- 保持名称简洁且描述性：`code-reviewer` 而非 `automatic-code-review-system`

### 2.7 故障排除

#### 问题 1：Claude Code 命令未找到

**症状**：
```
'claude' 不是内部或外部命令
```

**解决方案**：
```bash
# 1. 检查安装路径
where claude

# 2. 手动添加到 PATH
# 系统属性 → 高级 → 环境变量 → 编辑 Path
# 添加：C:\Users\[用户名]\AppData\Local\Claude

# 3. 重启终端
```

#### 问题 2：技能未被识别

**症状**：
```
在 Claude 中请求技能时，Claude 说没有该技能
```

**解决方案**：
```bash
# 1. 检查技能目录
dir %USERPROFILE%\.claude\skills\custom

# 2. 验证 SKILL.md 文件存在
dir %USERPROFILE%\.claude\skills\custom\your-skill\SKILL.md

# 3. 检查 YAML 格式
# 确保文件开头是：---
# name: skill-name
# description: ...---

# 4. 重启 Claude Code
```

#### 问题 3：插件安装失败

**症状**：
```
Error: Failed to install plugin
```

**解决方案**：
```bash
# 1. 检查网络连接
ping claude.ai

# 2. 清理插件缓存
rmdir /s %USERPROFILE%\.claude\plugins\cache

# 3. 重新安装
/plugin install example-skills@anthropic-agent-skills
```

#### 问题 4：权限错误

**症状**：
```
Error: Permission denied
```

**解决方案**：
```bash
# 1. 以管理员身份运行终端
# 右键点击 Terminal/PowerShell → "以管理员身份运行"

# 2. 检查文件权限
icacls %USERPROFILE%\.claude\skills

# 3. 修复权限
icacls %USERPROFILE%\.claude\skills /grant %USERNAME%:F /T
```

### 2.8 卸载与更新

#### 更新 Claude Code

```bash
# 方法 1：使用自动更新
claude --update

# 方法 2：重新下载安装包
# 从 claude.ai 下载最新版本并安装（覆盖安装）
```

#### 移除技能

```bash
# 1. 列出已安装的插件
/plugin list

# 2. 卸载特定技能集
/plugin remove example-skills

# 3. 卸载所有插件
/plugin remove-all
```

#### 完全卸载 Claude Code

```bash
# 1. 卸载程序
# Windows 设置 → 应用 → Claude Code → 卸载

# 2. 删除配置和数据
rmdir /s %USERPROFILE%\.claude
rmdir /s %USERPROFILE%\AppData\Local\Claude
rmdir /s %USERPROFILE%\AppData\Roaming\Claude

# 3. 删除环境变量（如已配置）
# 系统属性 → 高级 → 环境变量 → 删除 CLAUDE_SKILLS_PATH 和 ANTHROPIC_API_KEY
```

### 2.9 安装验证清单

完成安装后，使用以下清单验证：

```bash
# ✅ 1. Claude Code 已安装
claude --version

# ✅ 2. 技能目录已创建
dir %USERPROFILE%\.claude\skills

# ✅ 3. 配置文件存在
type %USERPROFILE%\.claude\config.json

# ✅ 4. 官方技能已安装
/plugin list

# ✅ 5. 可以使用技能
claude
# > "使用 algorithmic-art 技能创建一个艺术作品"
```

**全部通过？** 恭喜！您已成功配置 Claude Code 和 Agent Skills。

**遇到问题？** 请参阅第 23 节"常见问题与故障排除"获取更多帮助。

## 3. 快速开始

欢迎来到 Agent Skills 实战指南的快速开始部分！本章节将通过两个完整的示例，带您从零开始使用 Agent Skills。

### 3.1 快速开始概述

**预计完成时间**：约 35 分钟
- 示例 1（Web 应用测试）：15 分钟
- 示例 2（Word 文档操作）：10 分钟
- 进阶组合示例：10 分钟

**前置要求检查**：

```bash
# ✅ 确认 Claude Code 已安装
claude --version

# ✅ 确认官方技能已安装
/plugin list

# ✅ 确认技能目录已配置
dir %USERPROFILE%\.claude\skills

# ✅ 确认 Python 已安装（示例 1 需要）
python --version

# ✅ 确认 Node.js 已安装（示例 2 需要）
node --version
```

**你将学到**：
- 如何在 Claude Code 中触发和使用技能
- 开发类技能的实际应用（Web 应用测试）
- 文档处理类技能的实际应用（Word 文档生成）
- 技能组合使用的技巧

---

### 3.2 示例 1：开发类 - Web 应用测试

**场景**：使用 `webapp-testing` 技能测试一个简单的待办事项 Web 应用

**时间预估**：15 分钟

**技能调用语法**：
```bash
# 方法 1：直接提及技能名称
"使用 webapp-testing 技能帮我测试这个应用"

# 方法 2：描述需求（Claude 自动识别相关技能）
"帮我测试这个 Web 应用的功能"

# 方法 3：使用命令
/webapp-testing
```

#### 步骤 1：创建测试应用 (5 分钟)

创建文件 `todo-app.html`：

```html
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <title>待办事项应用</title>
    <style>
        body { font-family: Arial; max-width: 600px; margin: 50px auto; padding: 20px; }
        .todo-item { padding: 10px; margin: 5px 0; background: #f0f0f0; border-radius: 4px; }
        button { padding: 8px 16px; margin: 5px; }
    </style>
</head>
<body>
    <h1>📝 我的待办事项</h1>

    <div>
        <input type="text" id="taskInput" placeholder="输入新任务...">
        <button onclick="addTask()">添加</button>
    </div>

    <div id="taskList"></div>

    <script>
        function addTask() {
            const input = document.getElementById('taskInput');
            const task = input.value.trim();

            if (task) {
                const div = document.createElement('div');
                div.className = 'todo-item';
                div.innerHTML = `
                    <input type="checkbox" onchange="toggleTask(this)">
                    <span>${task}</span>
                    <button onclick="deleteTask(this)">删除</button>
                `;
                document.getElementById('taskList').appendChild(div);
                input.value = '';
            }
        }

        function toggleTask(checkbox) {
            const span = checkbox.nextElementSibling;
            span.style.textDecoration = checkbox.checked ? 'line-through' : 'none';
        }

        function deleteTask(button) {
            button.parentElement.remove();
        }
    </script>
</body>
</html>
```

**验证应用**：双击 `todo-app.html` 在浏览器中打开测试。

#### 步骤 2：使用 Claude Code 和 webapp-testing 技能 (5 分钟)

启动 Claude Code：

```bash
claude
```

**在 Claude 中输入以下请求**：

```
使用 webapp-testing 技能帮我测试 todo-app.html 这个文件。

我需要你：
1. 测试添加任务功能
2. 测试完成任务功能
3. 测试删除任务功能
4. 生成测试报告
```

#### 步骤 3：查看测试结果 (3 分钟)

Claude 会自动：
1. 读取 `todo-app.html` 文件
2. 生成 Playwright 测试脚本
3. 运行测试并捕获截图
4. 生成测试报告

**预期输出文件**：
```
test-results/
├── test_add_task.py          # 添加任务测试
├── test_complete_task.py     # 完成任务测试
├── test_delete_task.py       # 删除任务测试
├── test_report.txt           # 测试报告
└── screenshots/              # 测试截图
    ├── 01_initial_state.png
    ├── 02_after_add.png
    ├── 03_after_complete.png
    └── 04_after_delete.png
```

#### 步骤 4：理解测试脚本 (2 分钟)

查看生成的测试脚本（例如 `test_add_task.py`）：

```python
from playwright.sync_api import sync_playwright

with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page()

    # 导航到应用
    page.goto('file:///D:/path/to/todo-app.html')

    # 测试添加任务
    page.fill('#taskInput', '学习 Agent Skills')
    page.click('button')
    page.wait_for_timeout(500)

    # 验证任务已添加
    task = page.locator('.todo-item').last
    assert '学习 Agent Skills' in task.inner_text()

    # 截图
    page.screenshot(path='test_add_result.png')

    browser.close()
```

**关键学习点**：
- `webapp-testing` 技能自动使用 Playwright
- 生成的脚本包含导航、操作、验证
- 自动截图用于视觉验证

#### 步骤 5：运行测试 (可选，2 分钟)

如果您想自己运行测试：

```bash
# 安装 Playwright（首次运行）
pip install playwright
playwright install chromium

# 运行测试脚本
python test_add_task.py
```

**预期结果**：测试通过，生成 `test_add_result.png` 截图。

---

### 3.3 示例 2：文档处理类 - Word 文档操作

**场景**：使用 `docx` 技能创建一个格式化的项目周报

**时间预估**：10 分钟

#### 步骤 1：准备数据 (2 分钟)

创建数据文件 `weekly_data.json`：

```json
{
  "title": "项目周报 - 第 12 周",
  "period": "2024年3月18日 - 3月22日",
  "author": "张三",
  "team": "前端开发组",
  "summary": "本周完成了用户认证模块的开发，并修复了 5 个高优先级 Bug。",
  "achievements": [
    {"item": "完成用户登录功能", "status": "已完成", "priority": "高"},
    {"item": "实现权限管理系统", "status": "进行中", "priority": "高"},
    {"item": "优化页面加载速度", "status": "已完成", "priority": "中"},
    {"item": "编写 API 文档", "status": "已完成", "priority": "低"}
  ],
  "metrics": {
    "bugs_fixed": 5,
    "features_completed": 3,
    "code_coverage": "85%",
    "deployment_success": "100%"
  },
  "next_week": [
    "完成权限管理系统",
    "开始支付模块开发",
    "优化数据库查询"
  ]
}
```

#### 步骤 2：使用 Claude Code 和 docx 技能 (3 分钟)

**在 Claude 中输入以下请求**：

```
使用 docx 技能帮我创建一个项目周报。

数据文件是 weekly_data.json。

我需要你：
1. 创建一个专业的 Word 文档
2. 包含标题、作者、团队信息
3. 本周成就用表格展示
4. 指标用图表展示
5. 保存为 "项目周报-第12周.docx"
```

#### 步骤 3：查看生成的文档 (3 分钟)

Claude 会生成 Python 脚本并执行，创建格式化的 Word 文档。

**预期输出**：`项目周报-第12周.docx`

**文档结构**：
```
项目周报 - 第 12 周
├── 标题页（标题、作者、团队、日期）
├── 执行摘要
├── 本周成就（表格）
│   ├── 任务 | 状态 | 优先级
│   └── ...
├── 项目指标（图表）
│   ├── Bug 修复数量
│   ├── 完成功能数
│   └── 代码覆盖率
└── 下周计划（列表）
```

#### 步骤 4：理解生成的代码 (2 分钟)

`docx` 技能会生成类似以下的 Python 代码：

```python
from docx import Document
from docx.shared import Pt, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.lib.enums import WD_ORIENTATION
import json

# 读取数据
with open('weekly_data.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

# 创建文档
doc = Document()

# 添加标题
title = doc.add_heading(data['title'], 0)
title.alignment = WD_ALIGN_PARAGRAPH.CENTER

# 添加元信息
info = doc.add_paragraph()
info.add_run('作者：').bold = True
info.add_run(f"{data['author']}\n")
info.add_run('团队：').bold = True
info.add_run(f"{data['team']}\n")
info.add_run('周期：').bold = True
info.add_run(f"{data['period']}")

# 添加摘要
doc.add_heading('执行摘要', 1)
doc.add_paragraph(data['summary'])

# 添加成就表格
doc.add_heading('本周成就', 1)
table = doc.add_table(rows=1, cols=3)
table.style = 'Light Grid Accent 1'

# 表头
headers = table.rows[0].cells
headers[0].text = '任务'
headers[1].text = '状态'
headers[2].text = '优先级'

# 添加数据行
for achievement in data['achievements']:
    row_cells = table.add_row().cells
    row_cells[0].text = achievement['item']
    row_cells[1].text = achievement['status']
    row_cells[2].text = achievement['priority']

# 保存文档
doc.save('项目周报-第12周.docx')
```

**关键学习点**：
- `docx` 技能使用 python-docx 库
- 支持复杂的格式化（表格、样式、图表）
- JSON 数据驱动的文档生成

---

### 3.4 示例 3：进阶 - 组合使用技能

**场景**：测试 Web 应用后，使用 `docx` 技能生成测试报告

**时间预估**：10 分钟

**在 Claude 中输入以下请求**：

```
我需要你帮我完成以下任务：

1. 首先使用 webapp-testing 技能测试 todo-app.html
2. 然后使用 docx 技能根据测试结果生成一份测试报告 Word 文档

测试报告需要包含：
- 测试概述
- 测试用例和结果（表格）
- 缺陷列表
- 测试截图
- 建议和结论
```

**组合使用的工作流程**：

```
步骤 1: webapp-testing 技能
    ↓
生成测试脚本和截图
    ↓
步骤 2: 收集测试结果
    ↓
步骤 3: docx 技能
    ↓
生成格式化测试报告
```

**预期输出**：
```
outputs/
├── test_scripts/           # 测试脚本
├── screenshots/            # 测试截图
└── 测试报告.docx          # 最终报告
```

---

### 3.5 常见问题快速解决

#### Q1: 技能未被识别

**症状**：Claude 说没有该技能

**快速解决**：
```bash
# 检查技能是否已安装
/plugin list

# 重新安装技能
/plugin install example-skills@anthropic-agent-skills
```

#### Q2: Python 依赖缺失

**症状**：`ModuleNotFoundError: No module named 'xxx'`

**快速解决**：
```bash
# 安装缺失的依赖
pip install playwright
pip install python-docx
pip install reportlab

# 或使用 requirements.txt
pip install -r requirements.txt
```

#### Q3: 文件路径问题

**症状**：`FileNotFoundError`

**快速解决**：
```bash
# 使用绝对路径
# 或在 Claude 中明确指定文件位置
"测试位于 D:\Projects\todo-app.html 的文件"
```

#### Q4: 权限问题

**症状**：`PermissionError`

**快速解决**：
```bash
# 以管理员身份运行
# 或更改文件夹权限
icacls "D:\Projects" /grant %USERNAME%:F /T
```

---

### 3.6 下一步学习路径

完成快速开始后，推荐按以下顺序深入学习：

**基础阶段**（1-2 周）：
1. 阅读第 1 部分：入门指南的其他章节
2. 学习每个技能类别的基础用法
3. 完成每个技能的简单示例

**进阶阶段**（2-4 周）：
1. 学习第 6 部分：高级用法
2. 实践技能组合使用
3. 创建第一个自定义技能

**专家阶段**（持续）：
1. 学习第 21 节：创建自定义技能完整教程
2. 贡献社区技能
3. 优化技能性能

**推荐章节顺序**：

```
┌─────────────────────────────────────────────┐
│ 第 1 阶段：基础                              │
├─────────────────────────────────────────────┤
│ • 第 1 部分：入门指南（已完成）             │
│ • 第 2 部分：创意设计类技能（了解即可）     │
│ • 第 3 部分：文档处理类技能（重点学习）     │
│ • 第 4 部分：开发工具类技能（重点学习）     │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│ 第 2 阶段：进阶                              │
├─────────────────────────────────────────────┤
│ • 第 6 部分：高级用法                       │
│   - 技能组合使用案例                        │
│   - 创建自定义技能                          │
│   - 最佳实践与技巧                          │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│ 第 3 阶段：专家                              │
├─────────────────────────────────────────────┤
│ • 第 7 部分：附录                           │
│   - 深入故障排除                            │
│   - 参考官方文档                             │
│ • 社区参与和贡献                            │
└─────────────────────────────────────────────┘
```

**下一步行动**：
1. 选择一个与您工作最相关的技能类别
2. 跳转到对应章节深入学习
3. 完成该类别的所有实战示例
4. 在实际项目中应用所学

---

**恭喜完成快速开始！** 🎉

您现在已经：
- ✅ 理解了 Agent Skills 的基本概念
- ✅ 完成了 Claude Code 的安装和配置
- ✅ 掌握了技能调用的基本语法
- ✅ 完成了开发类技能的实战示例
- ✅ 完成了文档处理类技能的实战示例
- ✅ 了解了技能组合使用的方法

准备好深入学习了吗？让我们继续探索 Agent Skills 的强大功能！

---

# 第二部分：创意设计类技能

## 4. algorithmic-art - 算法艺术生成器

**algorithmic-art** 是一个使用 p5.js 创建生成艺术的技能，强调算法表达、种子随机性和交互式参数探索。

### 4.1 技能概述

**什么是算法艺术？**

算法艺术（Algorithmic Art）是通过代码和数学算法创建的艺术作品。与传统艺术不同，算法艺术的美感从**计算过程**中涌现，而非手动绘制。

**核心特点**：
- **原创性**：每个作品都是独特的、不可预测的
- **可重复性**：相同种子产生相同结果（Art Blocks 模式）
- **交互性**：用户可通过参数实时探索艺术空间
- **过程导向**：美从算法执行中涌现，而非最终帧

**适用场景**：
- 用户请求创建生成艺术、算法艺术、流场、粒子系统
- 需要带有可调参数的交互式艺术作品
- 创建艺术画廊质量的可视化作品
- 探索数学之美和计算美学

### 4.2 p5.js 基础知识

#### 什么是 p5.js？

[p5.js](https://p5js.org/) 是一个专为创意编程设计的 JavaScript 库，使编程变得更加 accessible 和有趣。它的灵感来自 Processing 编程环境。

#### 基本结构

每个 p5.js 程序都包含两个核心函数：

```javascript
function setup() {
  // 初始化：只运行一次
  createCanvas(400, 400);
}

function draw() {
  // 绘图循环：持续运行（除非调用 noLoop()）
  background(220);
  ellipse(200, 200, 50);
}
```

#### 坐标系统

p5.js 使用标准笛卡尔坐标系统：

```
(0,0) ──────→ X 轴
  │
  │
  ↓
Y 轴

中心点: (200, 200) 在 400×400 画布上
```

#### 绘图基础

**形状**：
```javascript
ellipse(x, y, width, height)  // 椭圆/圆形
rect(x, y, width, height)     // 矩形
line(x1, y1, x2, y2)          // 线段
triangle(x1, y1, x2, y2, x3, y3)  // 三角形
```

**颜色**：
```javascript
background(220)                    // 灰色背景 (0-255)
fill(255, 0, 0)                    // 填充红色
stroke(0, 0, 255)                  // 描边蓝色
noFill()                           // 无填充
noStroke()                         // 无描边
```

### 4.3 核心概念

#### 4.3.1 算法哲学（两步创作流程）

**第一步：算法哲学创建**

先定义一个"计算美学运动"（4-6段），描述：
- 计算过程和数学关系
- 噪声函数和随机性模式
- 粒子行为和场动力学
- 时间演化和系统状态

**第二步：p5.js 代码实现**

通过代码表达这个哲学，创建交互式 HTML 制品。

#### 4.3.2 种子随机性

```javascript
// 设置种子
let seed = 12345;
randomSeed(seed);
noiseSeed(seed);

// 所有随机操作都是确定性的
let x = random(100);  // 总是返回相同的值
```

**重要性**：
- **可收藏性**：每个种子是独特的"版本"
- **可验证性**：相同输入 = 相同输出
- **可探索性**：用户可以浏览种子空间

#### 4.3.3 参数设计

| 参数类型 | 示例 | 用途 |
|---------|------|------|
| **数量** | 粒子数量、对象数量 | 控制复杂度 |
| **规模** | 大小、速度、间距 | 控制视觉规模 |
| **概率** | 出现几率、分支概率 | 控制随机行为 |

### 4.4 实战示例 1：简单 - 随机圆圈 (10分钟)

**场景**：创建随机分布的彩色圆圈艺术

**完整 HTML 代码**：

```html
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <title>随机圆圈艺术</title>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/p5.js/1.7.0/p5.min.js"></script>
    <style>
        body {
            font-family: 'Segoe UI', sans-serif;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            min-height: 100vh;
            display: flex;
            justify-content: center;
            align-items: center;
        }
        .container {
            background: rgba(255, 255, 255, 0.95);
            border-radius: 16px;
            padding: 24px;
            max-width: 600px;
        }
        #canvas-container { margin-top: 20px; }
    </style>
</head>
<body>
    <div class="container">
        <h1>🎨 随机圆圈艺术</h1>

        <label>圆圈数量: <span id="count-value">50</span></label>
        <input type="range" id="count" min="10" max="200" value="50" style="width:100%"
               oninput="updateParam('count', this.value)">

        <label>最大尺寸: <span id="size-value">50</span></label>
        <input type="range" id="size" min="10" max="100" value="50" style="width:100%"
               oninput="updateParam('size', this.value)">

        <label>种子: <span id="seed-value">12345</span></label>
        <input type="range" id="seed" min="1" max="99999" value="12345" style="width:100%"
               oninput="updateParam('seed', this.value)">

        <div style="display:flex;gap:8px;margin-top:16px;">
            <button onclick="previousSeed()" style="flex:1;padding:10px;">← 上一个</button>
            <button onclick="nextSeed()" style="flex:1;padding:10px;">下一个 →</button>
            <button onclick="randomSeed()" style="flex:1;padding:10px;">↻ 随机</button>
        </div>

        <div id="canvas-container"></div>
    </div>

    <script>
        let params = { count: 50, maxSize: 50, seed: 12345 };
        const colors = [[217, 119, 87], [106, 155, 204], [120, 140, 93]];

        function setup() {
            let canvas = createCanvas(500, 500);
            canvas.parent('canvas-container');
            initializeArt();
        }

        function initializeArt() {
            randomSeed(params.seed);
            background(250, 249, 245);

            for (let i = 0; i < params.count; i++) {
                fill(random(colors)[0], random(colors)[1], random(colors)[2], random(100, 200));
                noStroke();
                ellipse(random(width), random(height), random(5, params.maxSize));
            }
        }

        function updateParam(name, value) {
            params[name] = parseInt(value);
            document.getElementById(name + '-value').textContent = value;
            initializeArt();
        }

        function previousSeed() {
            params.seed = Math.max(1, params.seed - 1);
            updateSeedDisplay();
            initializeArt();
        }

        function nextSeed() {
            params.seed++;
            updateSeedDisplay();
            initializeArt();
        }

        function randomSeed() {
            params.seed = Math.floor(Math.random() * 99999) + 1;
            updateSeedDisplay();
            initializeArt();
        }

        function updateSeedDisplay() {
            document.getElementById('seed').value = params.seed;
            document.getElementById('seed-value').textContent = params.seed;
        }
    </script>
</body>
</html>
```

**预览方式**：保存为 `.html` 文件，直接在浏览器中打开。

### 4.5 实战示例 2：中等 - 流场粒子 (20分钟)

**场景**：Perlin 噪声驱动的流场效果

**关键代码片段**：

```javascript
// 流场粒子类
class Particle {
    constructor() {
        this.pos = createVector(random(width), random(height));
        this.vel = createVector(0, 0);
        this.acc = createVector(0, 0);
        this.maxSpeed = 2;
        this.prevPos = this.pos.copy();
    }

    follow(vectors) {
        let x = floor(this.pos.x / scale);
        let y = floor(this.pos.y / scale);
        let index = x + y * cols;

        let force = vectors[index];
        this.acc = force.copy();
    }

    update() {
        this.vel.add(this.acc);
        this.vel.limit(this.maxSpeed);
        this.prevPos = this.pos.copy();
        this.pos.add(this.vel);
        this.acc.mult(0);
    }

    show() {
        stroke(217, 119, 87, 100);
        line(this.prevPos.x, this.prevPos.y, this.pos.x, this.pos.y);
    }
}
```

**参数**：
- `particleCount`: 粒子数量 (100-2000)
- `noiseScale`: 噪声比例 (0.005-0.02)
- `flowSpeed`: 流动速度 (0.5-2.0)
- `trailLength`: 轨迹长度 (2-20)

### 4.6 实战示例 3：复杂 - 内心罗盘 (30分钟)

**场景**：在混沌中坚守内在方向（我们之前创建的示例）

**核心算法**：

```javascript
// 内在方向系统
class Particle {
    constructor() {
        this.pos = createVector(width/2, height/2);
        // 内在方向 - 粒子的"信念"
        this.innerDirection = p5.Vector.fromAngle(
            randomGaussian(0, params.innerDiversity) + HALF_PI
        );
        this.vel = this.innerDirection.copy();
        this.currentAngle = this.innerDirection.heading();
    }

    update() {
        // 计算与内在方向的偏离
        let currentDir = p5.Vector.fromAngle(this.currentAngle);
        let deviation = p5.Vector.angleBetween(currentDir, this.innerDirection);

        // 回归力 - 朝向内在方向
        let回归力 = deviation * params.beliefStrength;
        this.currentAngle +=回归力;

        // 外部噪声 - 世界的压力
        let noiseAngle = noise(
            this.pos.x * params.recoverySpeed,
            this.pos.y * params.recoverySpeed,
            frameCount * 0.01
        ) * TWO_PI * params.worldNoise;

        let finalAngle = this.currentAngle + sin(noiseAngle) * 0.3;
        this.vel = p5.Vector.fromAngle(finalAngle);
        this.pos.add(this.vel);
    }
}
```

**参数**：
- `beliefStrength`: 信念强度 (0.01-0.3)
- `worldNoise`: 世界嘈杂度 (0.5-3.0)
- `recoverySpeed`: 恢复速度 (0.001-0.02)
- `innerDiversity`: 内在多样性 (0.1-2.0)

### 4.7 参数设计详解

**数量类参数**：
```javascript
particleCount: 1000,    // 有多少元素
circleCount: 50,        // 有多少圆圈
```

**规模类参数**：
```javascript
scale: 0.01,            // 噪声缩放
speed: 0.5,              // 移动速度
size: 50,                // 元素大小
```

**概率类参数**：
```javascript
probability: 0.5,       // 出现几率
branchChance: 0.3,       // 分支概率
```

### 4.8 HTML 制品模板说明

**模板位置**：`skills/algorithmic-art/templates/viewer.html`

**固定部分**（保持不变）：
- Anthropic 品牌样式
- 种子导航控件
- 操作按钮

**可变部分**（为每个作品定制）：
- p5.js 算法代码
- 参数定义
- 参数 UI 控件

**修改模板步骤**：
1. 读取 `viewer.html`
2. 替换 p5.js 算法部分
3. 修改参数对象
4. 调整参数 UI 控件

### 4.9 最佳实践

**✅ 应该做的**：
- 创建原创算法艺术（避免版权问题）
- 设计有意义的参数（控制算法本质）
- 强调专家级工艺（精心调整每个参数）
- 保持代码简洁（便于理解和修改）
- 使用种子确保可重复性

**❌ 避免做的**：
- 复制现有艺术家的作品
- 创建"模式菜单"式作品
- 过度使用相同的视觉元素
- 忽略性能优化（大量粒子时）

### 4.10 性能优化

**粒子数量控制**：
```javascript
// 根据画布大小动态调整
let maxParticles = (width * height) / 1000;
params.particleCount = min(params.particleCount, maxParticles);
```

**轨迹长度限制**：
```javascript
// 限制轨迹历史长度
if (this.history.length > params.trailLength) {
    this.history.shift();
}
```

**条件渲染**：
```javascript
// 只绘制可见元素
if (this.isInBounds()) {
    this.show();
}
```

### 4.11 常见问题

**Q1: p5.js 无法加载**
```html
<!-- 确保 CDN 链接正确 -->
<script src="https://cdnjs.cloudflare.com/ajax/libs/p5.js/1.7.0/p5.min.js"></script>
```

**Q2: 种子不生效**
```javascript
// 必须在 setup() 开始时调用
function setup() {
    randomSeed(params.seed);  // ← 首先设置种子
    // ...
}
```

**Q3: 性能问题**
- 减少粒子数量
- 增大轨迹长度限制
- 使用 `noLoop()` 代替 `draw()`

**Q4: 颜色不显示**
```javascript
// 确保在绘制前设置颜色
fill(255, 0, 0);    // ← 先设置
ellipse(x, y, 50);   // ← 后绘制
```

### 4.12 与其他技能对比

| 特性 | algorithmic-art | canvas-design | frontend-design |
|------|---------------|---------------|----------------|
| **输出** | 交互式 HTML | 静态 PNG/PDF | 完整 Web 项目 |
| **交互性** | 有参数控件 | 无 | 根据需求 |
| **技术** | p5.js | Python/PIL | HTML/CSS/JS |
| **重点** | 算法过程 | 最终作品 | 用户界面 |
| **可重复性** | 种子控制 | 无 | 无 |

### 4.13 资源链接

- [p5.js 官方文档](https://p5js.org/reference/)
- [p5.js Web Editor](https://editor.p5js.org/)
- [The Coding Train / p5.js 教程](https://www.youtube.com/playlist?list=PLRqwWVAvAB16tlbAMlbulwQLKVdjk5s1)
- [Generative Design](https://generative-design.appspot.com/)
- [OpenProcessing](https://openprocessing.org/)

## 5. canvas-design - 画布设计

**canvas-design** 是一个创建专业静态视觉艺术的技能，使用 Python 的 PIL 和 reportlab 库生成高质量的 PNG 或 PDF 格式作品。

### 5.1 技能概述

**什么是画布设计？**

画布设计是通过计算方法创建静态视觉艺术作品的过程，强调**视觉优先**和**最少文本**原则。与 algorithmic-art 不同，canvas-design 生成的是静态图像，而非交互式 HTML。

**核心特点**：
- **静态输出**：PNG 或 PDF 格式，适合打印和分享
- **视觉优先**：90% 视觉设计，10% 基本文本
- **博物馆级质量**：适合画廊、展览或商业使用
- **设计哲学驱动**：每个作品都有独特的美学概念

**适用场景**：
- 创建海报、艺术品、设计作品
- 品牌宣传材料
- 杂志封面
- 展览作品
- 企业宣传材料

### 5.2 技术栈介绍

#### 5.2.1 PIL/Pillow 图像处理库

[Pillow](https://pillow.readthedocs.io/) 是 Python 最流行的图像处理库。

**基本操作**：
```python
from PIL import Image, ImageDraw, ImageFont

# 创建新图像
img = Image.new('RGB', (800, 600), color=(250, 249, 245))

# 绘图
draw = ImageDraw.Draw(img)
draw.ellipse([100, 100, 200, 200], fill=(217, 119, 87))

# 保存
img.save('artwork.png')
```

#### 5.2.2 reportlab PDF 生成库

[reportlab](https://reportlab.com/) 是强大的 PDF 生成库。

**基本操作**：
```python
from reportlab.lib.pagesizes import A4
from reportlab.pdfgen import canvas

# 创建 PDF
c = canvas.Canvas('output.pdf', pagesize=A4)

# 绘制
c.drawString("Hello, World!", 100, 750)
c.drawImage('image.png', 100, 600, width=400, height=300)

# 保存
c.save()
```

### 5.3 核心概念

#### 5.3.1 两步创作流程

**第一步：设计哲学创建**

创建一个美学运动的 4-6 段描述：
- 空间和形式
- 颜色和材质
- 规模和节奏
- 构图和平衡

**第二步：视觉表达**

通过代码将哲学转化为图像：
- 几何形状和布局
- 色彩和渐变
- 纹理和材质
- 排版（极少文本）

#### 5.3.2 设计原则

**视觉优先原则**：
- 90% 视觉，10% 文本
- 文本仅用于视觉强调
- 信息通过形状、颜色、构图传达

**最少文本原则**：
- 标题：单个词或短语
- 说明：极简短句
- 避免：段落、长句、解释性文本

#### 5.3.3 与 algorithmic-art 的核心区别

| 特性 | canvas-design | algorithmic-art |
|------|---------------|----------------|
| **输出** | 静态 PNG/PDF | 交互式 HTML |
| **代码语言** | Python | JavaScript (p5.js) |
| **交互性** | 无 | 有参数控件 |
| **预览方式** | 直接打开 | 浏览器中交互 |
| **用途** | 打印、展览 | Web 分享 |
| **重复性** | 无种子概念 | 有种子系统 |

### 5.4 设计风格参考

#### 混凝土诗歌

**特点**：宏伟形式、大胆几何、雕塑感

**视觉元素**：
- 巨大的色块
- 巨大的排版（单个词、微小标签）
- 野兽派空间划分
- 负空间作为设计元素

#### 色彩语言

**特点**：色彩作为主要信息系统

**视觉元素**：
- 色域创造意义的几何精度
- 排版极简（小型无衬线标签）
- 信息在空间和色彩上编码
- Josef Albers 互动 + 数据可视化

#### 模拟冥想

**特点**：纹理、呼吸空间、负空间

**视觉元素**：
- 纸张纹理、墨水渗透效果
- 巨大的负空间
- 日本摄影集美学
- 文本低语（小、克制）

#### 几何静默

**特点**：网格精度、大胆摄影、戏剧性负空间

**视觉元素**：
- 基于网格的布局
- 精确但极简的排版
- 瑞士形式主义 + 野兽派材料
- 结构沟通，而非文字

### 5.5 实战示例 1：中等 - 几何抽象艺术 (20分钟)

**场景**：创建几何形状的抽象艺术

**时间预估**：20 分钟

**完整代码**：

```python
from PIL import Image, ImageDraw
import random

# 参数
WIDTH, HEIGHT = 1200, 1600
NUM_SHAPES = 15
MIN_SIZE = 50
MAX_SIZE = 300
BG_COLOR = (20, 18, 19)
ACCENT_COLORS = [
    (217, 119, 87),   # 橙色
    (106, 155, 204), # 蓝色
    (120, 140, 93),  # 绿色
]

def create_geometric_art():
    """创建几何抽象艺术"""
    # 创建图像
    img = Image.new('RGB', (WIDTH, HEIGHT), BG_COLOR)
    draw = ImageDraw.Draw(img)

    # 添加背景纹理（微妙的噪声）
    for _ in range(5000):
        x = random.randint(0, WIDTH-1)
        y = random.randint(0, HEIGHT-1)
        draw.point((x, y), fill=(30, 28, 27))

    # 绘制几何形状
    for i in range(NUM_SHAPES):
        # 随机选择形状类型
        shape_type = random.choice(['circle', 'rectangle', 'triangle'])
        color = random.choice(ACCENT_COLORS)
        size = random.randint(MIN_SIZE, MAX_SIZE)
        x = random.randint(0, WIDTH - size)
        y = random.randint(0, HEIGHT - size)

        # 绘制形状
        if shape_type == 'circle':
            draw.ellipse([x, y, x + size, y + size], outline=color, width=3)
        elif shape_type == 'rectangle':
            draw.rectangle([x, y, x + size, y + size], outline=color, width=3)
        elif shape_type == 'triangle':
            points = [
                (x + size // 2, y),
                (x, y + size),
                (x + size, y + size)
            ]
            draw.polygon(points, outline=color, width=3)

    # 添加文本元素
    try:
        font = ImageFont.truetype('C:/Windows/Fonts/arial.ttf', 48)
        draw.text((100, HEIGHT - 100), "GEOMETRIC", font=font, fill=(250, 249, 245))
        draw.text((100, HEIGHT - 50), "ABSTRACTION", font=font, fill=(250, 249, 245))
    except:
        # 如果字体加载失败，使用默认字体
        pass

    # 保存
    img.save('geometric_art.png', quality=95)
    print("✅ 几何抽象艺术已保存为 geometric_art.png")

if __name__ == '__main__':
    create_geometric_art()
```

**运行结果**：生成 `geometric_art.png`，包含几何形状和极简文本。

### 5.6 实战示例 2：复杂 - 内在之光 (30分钟)

**场景**：多层光效的哲学艺术（我们之前创建的示例）

**核心代码**：

```python
from PIL import Image, ImageDraw, ImageFilter
import math
import random

# 参数
WIDTH, HEIGHT = 2400, 3600
DPI = 300

# 颜色定义
COLORS = {
    'core_light': (255, 253, 245),
    'inner_glow': (255, 245, 230),
    'warm_gold': (255, 215, 170),
    'peach': (255, 180, 140),
    'soft_orange': (255, 150, 120),
    'deep_blue': (25, 35, 55),
    'charcoal': (18, 20, 19),
    'spark': (255, 200, 120),
}

def create_glow_layer(center_x, center_y, radius, color):
    """创建发光层"""
    layer = Image.new('RGBA', (WIDTH, HEIGHT), (0, 0, 0, 0))
    draw = ImageDraw.Draw(layer)

    # 多层渐变实现柔和光晕
    steps = 100
    for i in range(steps):
        alpha = int(255 * (1 - (i / steps) ** 0.5))
        current_radius = radius * (1 - i / steps)
        draw.ellipse(
            [center_x - current_radius, center_y - current_radius,
             center_x + current_radius, center_y + current_radius],
            fill=(*color, alpha // 4)
        )

    return layer

def create_inner_light_art():
    """创建内在之光艺术作品"""
    # 创建基础画布
    canvas = Image.new('RGB', (WIDTH, HEIGHT), COLORS['dark_navy'])
    canvas = add_noise_texture(canvas, intensity=15)

    # 中心点
    center_x, center_y = WIDTH // 2, HEIGHT // 2

    # 外层光晕
    outer_glow = create_glow_layer(center_x, center_y, 700, COLORS['coral'])
    canvas = Image.alpha_composite(canvas.convert('RGBA'), outer_glow).convert('RGB')

    # 中间光晕
    mid_glow = create_glow_layer(center_x, center_y, 450, COLORS['peach'])
    canvas = Image.alpha_composite(canvas.convert('RGBA'), mid_glow).convert('RGB')

    # 内层光晕
    inner_glow = create_glow_layer(center_x, center_y, 250, COLORS['warm_gold'])
    canvas = Image.alpha_composite(canvas.convert('RGBA'), inner_glow).convert('RGB')

    # 核心光区
    core = create_glow_layer(center_x, center_y, 120, COLORS['core_light'])
    canvas = Image.alpha_composite(canvas.convert('RGBA'), core).convert('RGB')

    # 添加边缘小光点
    add_sparkles(canvas, center_x, center_y)

    # 保存
    canvas.save('inner_light_art.png', quality=95, DPI=(DPI, DPI))
    canvas.save('inner_light_art.pdf', quality=95, DPI=(DPI, DPI))

    print("✅ 内在之光艺术作品已生成")
    print("   PNG: inner_light_art.png")
    print("   PDF: inner_light_art.pdf")

def add_noise_texture(image, intensity=30):
    """添加微妙纹理"""
    pixels = image.load()
    for i in range(0, WIDTH, 2):
        for j in range(0, HEIGHT, 2):
            if random.random() < 0.3:
                noise = random.randint(-intensity, intensity)
                r, g, b = pixels[i, j]
                pixels[i, j] = (
                    max(0, min(255, r + noise)),
                    max(0, min(255, g + noise)),
                    max(0, min(255, b + noise))
                )
    return image

def add_sparkles(canvas, center_x, center_y):
    """添加边缘小光点"""
    draw = ImageDraw.Draw(canvas)

    for _ in range(80):
        angle = random.uniform(0, 2 * math.pi)
        distance = random.uniform(500, 1100)
        x = center_x + math.cos(angle) * distance
        y = center_y + math.sin(angle) * distance

        if 0 <= x < WIDTH and 0 <= y < HEIGHT:
            size = random.randint(2, 6)
            alpha = random.randint(100, 200)
            draw.ellipse([x - size, y - size, x + size, y + size],
                        fill=(*COLORS['spark'], alpha))

if __name__ == '__main__':
    create_inner_light_art()
```

**运行结果**：生成高分辨率 PNG 和 PDF 文件，适合打印。

### 5.7 PIL 基础教程

#### Image 对象

```python
from PIL import Image

# 创建新图像
img = Image.new('RGB', (800, 600), color=(255, 255, 255))
img = Image.new('RGB', (800, 600), color='white')  # 等效
img = Image.new('RGBA', (800, 600), (255, 255, 255, 0))  # 带透明度

# 打开现有图像
img = Image.open('input.jpg')

# 转换模式
rgb_img = img.convert('RGB')
rgba_img = img.convert('RGBA')
grayscale_img = img.convert('L')  # 灰度

# 调整大小
resized = img.resize((400, 300))
resized = img.resize((400, 300), Image.LANCZOS)  # 高质量
```

#### ImageDraw 绘图

```python
from PIL import Image, ImageDraw

img = Image.new('RGB', (800, 600))
draw = ImageDraw.Draw(img)

# 绘制形状
draw.rectangle([100, 100, 300, 200], fill=(255, 0, 0))
draw.ellipse([400, 300, 600, 500], outline=(0, 0, 255), width=3)

# 绘制线条
draw.line([(0, 0), (800, 600)], fill=(128, 128, 128), width=2)

# 绘制点
draw.point((400, 300), fill=(0, 0, 0))

# 绘制文本
draw.text((100, 50), "Hello World", fill=(0, 0, 0))
```

### 5.8 reportlab 基础教程

#### Canvas 设置

```python
from reportlab.lib.pagesizes import A4, A3, letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas

# 创建 PDF
c = canvas.Canvas('output.pdf', pagesize=A4)

# 获取页面尺寸
width, height = A4  # (595.28, 841.89)

# 设置背景
c.setFillColorRGB(0.95, 0.95, 0.95)
c.rect(0, 0, width, height, fill=True, stroke=False)
```

#### 文本绘制

```python
from reportlab.pdfbase import pdfmetrics
from reportlab.lib import colors

# 注册字体（Windows）
pdfmetrics.registerFont(TTFont('Arial', 'C:/Windows/Fonts/arial.ttf'))

# 设置字体
c.setFont("Arial", 24)
c.setFillColorRGB(0.2, 0.2, 0.2)

# 绘制文本
c.drawString("标题", inch(1), inch(10))
c.drawCentredString("居中文本", width / 2, height / 2)

# 文本对齐
c.drawString("左对齐", inch(1), inch(8), textLeading=24)
```

#### 图像嵌入

```python
# 嵌入图像
c.drawImage('image.png', inch(1), inch(2), width=4*inch, height=3*inch)

# 保持宽高比
c.drawImage('photo.jpg', inch(1), inch(2),
             width=6*inch, preserveAspectRatio=True)
```

### 5.9 字体处理

#### 字体目录位置

```
skills/canvas-design/canvas-fonts/
├── Poppins/             # 标题字体
│   ├── Poppins-Regular.ttf
│   └── Poppins-Bold.ttf
├── Lora/                # 正文字体
│   ├── Lora-Regular.ttf
│   └── Lora-BoldItalic.ttf
└── WorkSans/            # UI 字体
    ├── WorkSans-Regular.ttf
    └── WorkSans-Bold.ttf
```

#### 字体加载和使用

```python
from PIL import ImageFont

# 加载字体
font_path = "skills/canvas-design/canvas-fonts/Lora-Regular.ttf"
font = ImageFont.truetype(font_path, 36)

# 使用字体
draw.text((100, 100), "文本内容", font=font, fill=(0, 0, 0))

# 字体回退
try:
    title_font = ImageFont.truetype('Poppins-Bold.ttf', 48)
except:
    title_font = ImageFont.load_default()
```

### 5.10 预览和导出

#### 预览 PNG 文件

```bash
# Windows 默认打开方式
start geometric_art.png

# 或在 Python 中预览
from PIL import Image
img = Image.open('geometric_art.png')
img.show()
```

#### 预览 PDF 文件

**推荐工具**：
- Adobe Acrobat Reader
- Foxit Reader
- 浏览器内置 PDF 查看器

```bash
start inner_light_art.pdf
```

#### 导出设置

**打印优化设置**：

```python
# 高分辨率
img.save('print.png', dpi=(300, 300))

# PDF 打印优化
c = canvas.Canvas('output.pdf', pagesize=A4)
c.setTitle("Print Version")
c.setCreator("Artist Name")
c.setProducer("Python ReportLab")
```

### 5.11 与 algorithmic-art 的详细对比

| 维度 | canvas-design | algorithmic-art |
|------|---------------|----------------|
| **输出格式** | 静态 PNG/PDF | 交互式 HTML |
| **代码语言** | Python | JavaScript (p5.js) |
| **技术库** | PIL, reportlab | p5.js |
| **交互性** | 无 | 有参数控件 |
| **可重复性** | 无种子系统 | 有种子系统 |
| **预览方式** | 直接打开图像 | 浏览器中交互 |
| **主要用途** | 打印、展览 | Web 分享 |
| **文本内容** | 极少（10%） | 较少，主要是视觉 |
| **艺术重点** | 最终视觉作品 | 生成过程 |
| **学习曲线** | 需要 Python 基础 | 需要 JavaScript 基础 |

#### 如何选择

**选择 canvas-design 当**：
- 需要打印或物理展示
- 创建海报、展览作品
- 需要精确控制输出分辨率
- 艺术作品不涉及动画

**选择 algorithmic-art 当**：
- 创建可交互的艺术作品
- 需要参数探索功能
- 用户可以浏览不同版本
- 涉及动画或实时变化

### 5.12 最佳实践

#### ✅ 设计原则

**视觉层次**：
```
主元素：大尺寸、高对比度
次要元素：中等尺寸、中对比度
背景元素：小尺寸、低对比度
```

**色彩搭配**：
- 使用有限调色板（3-5 种颜色）
- 确保足够的对比度
- 考虑色彩心理学

**构图技巧**：
- 使用三分法
- 负空间的巧妙运用
- 视觉引导线
- 平衡与对称

#### ✅ 技术最佳实践

**代码组织**：
```python
# 使用常量定义配置
WIDTH, HEIGHT = 2400, 3600
BG_COLOR = (20, 18, 19)

# 使用函数组织代码
def draw_background():
    """绘制背景"""
    pass

def draw_main_element():
    """绘制主要元素"""
    pass
```

**性能优化**：
```python
# 使用图像合成代替重复绘制
# 而不是：
for i in range(100):
    draw.circle((50, 50), 10)

# 使用：
temp_img = Image.new('RGB', (100, 100))
for i in range(100):
    temp_img.circle((50, 50), 10)
main_img.paste(temp_img)
```

**质量保证**：
```python
# 使用高质量保存
img.save('output.png', quality=95, optimize=True)

# 使用抗锯齿
resize_image = img.resize((400, 300), Image.LANCZOS)
```

### 5.13 实际应用案例

#### 海报设计

```python
def create_event_poster(event_name, date, venue):
    """创建活动海报"""
    # 设计哲学：混凝土诗歌风格
    # 巨大标题 + 几何装饰 + 关键信息

    # 尺寸：A3 (297mm × 420mm)
    # 分辨率：300 DPI
    # 颜色：黑、白、橙

    # 输出：print_ready_poster.pdf
    pass
```

#### 品牌宣传材料

```python
def create_brand_handout():
    """创建品牌宣传材料"""
    # 设计哲学：几何静默风格
    # 品牌色块 + 极简信息

    # 输出：brand_handout.pdf
    pass
```

#### 展览作品

```python
def create_exhibition_print():
    """创建展览作品"""
    # 设计哲学：模拟冥想风格
    # 大量负空间 + 精致细节

    # 尺寸：自定义大尺寸
    # 输出：exhibition_print.pdf
    pass
```

## 6. frontend-design - 前端界面设计

**frontend-design** 是一个用于创建高设计质量、独特且生产级前端界面的技能，强调避免通用的"AI 草稿"美学。

### 6.1 技能概述

**什么是前端界面设计？**

前端界面设计是通过代码创建用户界面的过程，但与普通的前端设计不同，此技能强调**独特的美学方向**和**精致的细节**。

**核心特点**：
- **避免 AI 美学**：不使用紫色渐变、Inter 字体、可预测布局
- **独特字体选择**：使用富有特色的字体配对
- **大胆调色板**：一种主导颜色 + 1-2 种强调色
- **运动效果**：动画、微交互、滚动触发
- **生产级代码**：HTML/CSS/JS、React、Vue 等可运行代码

**适用场景**：
- 构建 Web 组件、页面、落地页、仪表板
- 创建 React 组件、HTML/CSS 布局
- 任何 Web UI 的样式/美化

### 6.2 设计思维

#### 设计前思考

在编码之前，明确以下要素：

| 要素 | 问题 | 示例答案 |
|------|------|----------|
| **目的** | 此界面解决了什么问题？谁使用它？ | 电商结账流程，用于手机用户 |
| **基调** | 选择一个美学方向 | 野兽派极简主义、复古未来主义 |
| **约束** | 技术要求是什么？ | React + Tailwind CSS，性能重要 |
| **差异化** | 令人难忘的一件事 | 独特的 3D 卡片翻转效果 |

**美学方向选项**：
- 野兽派极简主义：巨大对比度、大胆字体
- 极繁主义混乱：丰富的纹理、多层内容
- 复古古未来主义：霓虹色、科技感
- 有机/自然：柔和曲线、自然色调
- 奢华/精致：黄金比例、优雅渐变
- 好玩/玩具般：圆润形状、鲜艳色彩
- 编辑/杂志：杂志版式、精致排版
- 装饰艺术/几何：几何图案、Art Deco 风格
- 柔和/粉彩：柔和色调、精致细节
- 工业/实用主义：粗边框、实用字体

### 6.3 前端美学指南

#### 排版

**原则**：选择美丽、独特和有趣的字体。

**避免**：
- ❌ Arial（过于通用）
- ❌ Inter（AI 草稿的标志）
- ❌ Roboto（默认系统字体）
- ❌ 系统字体（过于平庸）

**推荐字体配对**：

| 标题字体 | 正文字体 | 适用场景 |
|---------|---------|---------|
| Poppins | Lora | 现代专业 |
| Georgia | Verdana | 传统优雅 |
| Playfair Display | Montserrat | 杂志风格 |
| Oswald | Open Sans | 大胆现代 |
| Merriweather | Roboto Slab | 可读性强 |
| Bebas Neue | Source Sans Pro | 强调标题 |

**实现方式**：
```css
/* 使用 Google Fonts */
@import url('https://fonts.googleapis.com/css2?family=Playfair+Display:wght@400;700&family=Montserrat:wght@300;400;600&display=swap');

:root {
  --font-title: 'Playfair Display', serif;
  --font-body: 'Montserrat', sans-serif;
}
```

#### 颜色和主题

**原则**：使用一致的美学，具有鲜明的强调色。

**推荐调色板**：

| 主题 | 主色 | 强调色 | 适用场景 |
|------|------|---------|---------|
| **日落峡谷** | `#2D3748` 深蓝灰 | `#E94560` 珊瑚橙 | 科技产品 |
| **森林秘境** | `#1B4332` 森林绿 | `#F5CC7C` 沙黄 | 自然产品 |
| **深海星光** | `#0A2342` 深海蓝 | `#FFD700` 金色 | 奢华品牌 |
| **紫罗兰梦境** | `#240046` 深紫 | `#F72585` 霓虹粉 | 创意产品 |

**CSS 变量设置**：
```css
:root {
  --color-primary: #2D3748;
  --color-accent: #E94560;
  --color-background: #F8F9FA;
  --color-text: #1A1A1A;
}
```

#### 运动

**原则**：使用动画进行效果和微交互。

**动画类型**：
- **页面加载**：错开的元素显示（使用 `animation-delay`）
- **悬停状态**：令人惊讶的变换效果
- **滚动触发**：元素进入视口时的动画
- **点击反馈**：按钮按压动画

**示例：错开的页面加载**：
```css
@keyframes fadeInUp {
  from {
    opacity: 0;
    transform: translateY(30px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.animate-item {
  animation: fadeInUp 0.6s ease-out forwards;
  opacity: 0; /* 初始隐藏 */
}

/* 使用 JavaScript 添加延迟 */
.animate-item:nth-child(1) { animation-delay: 0.1s; }
.animate-item:nth-child(2) { animation-delay: 0.2s; }
.animate-item:nth-child(3) { animation-delay: 0.3s; }
```

**示例：滚动触发动画**：
```javascript
// 使用 Intersection Observer
const observer = new IntersectionObserver((entries) => {
  entries.forEach(entry => {
    if (entry.isIntersecting) {
      entry.target.classList.add('visible');
    }
  });
}, { threshold: 0.1 });

document.querySelectorAll('.scroll-animate').forEach(el => {
  observer.observe(el);
});
```

```css
.scroll-animate {
  opacity: 0;
  transform: translateY(40px);
  transition: all 0.8s ease-out;
}

.scroll-animate.visible {
  opacity: 1;
  transform: translateY(0);
}
```

#### 空间构图

**原则**：使用意想不到的布局。

**布局技巧**：
- **不对称**：避免完全对称
- **重叠**：元素轻微重叠创造深度
- **对角线流动**：对角线引导视线
- **网格破坏元素**：打破完美网格

**示例：不对称网格**：
```css
.grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
  gap: 20px;
}

/* 让第一个项目跨两列 */
.grid-item:first-child {
  grid-column: span 2;
}

/* 响应式：移动端恢复单列 */
@media (max-width: 768px) {
  .grid-item:first-child {
    grid-column: span 1;
  }
}
```

#### 背景和视觉细节

**原则**：创建氛围和深度。

**效果类型**：
- 渐变网格
- 噪声纹理
- 几何图案
- 分层透明度
- 戏剧性阴影
- 装饰边框
- 自定义光标
- 颗粒叠加

**示例：渐变网格背景**：
```css
body {
  background:
    linear-gradient(rgba(45, 55, 72, 0.9) 1px, transparent 1px),
    linear-gradient(90deg, rgba(45, 55, 72, 0.9) 1px, transparent 1px),
    linear-gradient(rgba(45, 55, 72, 0.1) 1px, transparent 1px),
    linear-gradient(90deg, rgba(45, 55, 72, 0.1) 1px, transparent 1px),
    linear-gradient(135deg, #667eea 0%, #764ba2 100%);
  background-size: 50px 50px, 50px 50px, 10px 10px, 10px 10px, 100% 100%;
}
```

### 6.4 实战示例 1：卡片翻转效果 (15分钟)

**场景**：创建一个具有 3D 卡片翻转效果的产品展示页面

**完整代码**：

```html
<!DOCTYPE html>
<html lang="zh-CN">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>3D 卡片翻转效果</title>
  <link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700&family=Merriweather:wght@400;700&display=swap" rel="stylesheet">
  <style>
    * {
      margin: 0;
      padding: 0;
      box-sizing: border-box;
    }

    body {
      font-family: 'Merriweather', serif;
      background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%);
      min-height: 100vh;
      display: flex;
      flex-direction: column;
      align-items: center;
      padding: 40px 20px;
    }

    .title {
      font-family: 'Playfair Display', serif;
      font-size: 3rem;
      color: #E94560;
      margin-bottom: 40px;
      text-align: center;
    }

    .cards-container {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(280px, 1fr));
      gap: 30px;
      max-width: 1200px;
      width: 100%;
    }

    .card {
      perspective: 1000px;
      height: 400px;
    }

    .card-inner {
      position: relative;
      width: 100%;
      height: 100%;
      transition: transform 0.8s cubic-bezier(0.4, 0, 0.2, 1);
      transform-style: preserve-3d;
      cursor: pointer;
      border-radius: 16px;
    }

    .card:hover .card-inner {
      transform: rotateY(180deg);
    }

    .card-front, .card-back {
      position: absolute;
      width: 100%;
      height: 100%;
      backface-visibility: hidden;
      border-radius: 16px;
      display: flex;
      flex-direction: column;
      justify-content: center;
      align-items: center;
      padding: 20px;
      text-align: center;
    }

    .card-front {
      background: linear-gradient(135deg, #2D3748 0%, #3E5473 100%);
      box-shadow: 0 10px 30px rgba(0, 0, 0, 0.3);
    }

    .card-back {
      background: linear-gradient(135deg, #E94560 0%, #FF6B6B 100%);
      transform: rotateY(180deg);
      box-shadow: 0 10px 30px rgba(233, 69, 96, 0.3);
    }

    .card-icon {
      font-size: 4rem;
      margin-bottom: 20px;
    }

    .card-title {
      font-family: 'Playfair Display', serif;
      font-size: 1.5rem;
      color: #F8F9FA;
      margin-bottom: 10px;
    }

    .card-description {
      color: #ADB5BD;
      font-size: 0.95rem;
      line-height: 1.6;
    }

    .card-price {
      font-family: 'Playfair Display', serif;
      font-size: 2.5rem;
      color: #FFF;
      margin-bottom: 15px;
    }

    .card-features {
      color: #FFF;
      list-style: none;
      text-align: left;
      width: 100%;
    }

    .card-features li {
      padding: 8px 0;
      border-bottom: 1px solid rgba(255, 255, 255, 0.2);
    }

    .card-features li:last-child {
      border-bottom: none;
    }

    .cta-button {
      margin-top: 20px;
      padding: 12px 30px;
      background: #F8F9FA;
      color: #E94560;
      border: none;
      border-radius: 8px;
      font-family: 'Merriweather', serif;
      font-weight: 700;
      cursor: pointer;
      transition: all 0.3s ease;
    }

    .cta-button:hover {
      transform: translateY(-2px);
      box-shadow: 0 5px 15px rgba(0, 0, 0, 0.2);
    }
  </style>
</head>
<body>
  <h1 class="title">精选产品</h1>
  <div class="cards-container">
    <div class="card">
      <div class="card-inner">
        <div class="card-front">
          <div class="card-icon">🎨</div>
          <h2 class="card-title">设计服务</h2>
          <p class="card-description">专业的 UI/UX 设计，为您的品牌打造独特体验</p>
        </div>
        <div class="card-back">
          <div class="card-price">¥2999</div>
          <ul class="card-features">
            <li>✓ 响应式设计</li>
            <li>✓ 3 个页面设计</li>
            <li>✓ 源文件交付</li>
            <li>✓ 2 次修改</li>
          </ul>
          <button class="cta-button">立即购买</button>
        </div>
      </div>
    </div>

    <div class="card">
      <div class="card-inner">
        <div class="card-front">
          <div class="card-icon">💻</div>
          <h2 class="card-title">开发服务</h2>
          <p class="card-description">全栈开发，从原型到部署的一站式服务</p>
        </div>
        <div class="card-back">
          <div class="card-price">¥5999</div>
          <ul class="card-features">
            <li>✓ 前端开发（React）</li>
            <li>✓ 后端 API 开发</li>
            <li>✓ 数据库设计</li>
            <li>✓ 部署支持</li>
          </ul>
          <button class="cta-button">立即购买</button>
        </div>
      </div>
    </div>

    <div class="card">
      <div class="card-inner">
        <div class="card-front">
          <div class="card-icon">🚀</div>
          <h2 class="card-title">性能优化</h2>
          <p class="card-description">网站性能分析与优化，提升用户体验</p>
        </div>
        <div class="card-back">
          <div class="card-price">¥1999</div>
          <ul class="card-features">
            <li>✓ 性能分析报告</li>
            <li>✓ 代码优化</li>
            <li>✓ 图片优化</li>
            <li>✓ 加载速度提升</li>
          </ul>
          <button class="cta-button">立即购买</button>
        </div>
      </div>
    </div>
  </div>
</body>
</html>
```

### 6.5 实战示例 2：滚动视差效果 (20分钟)

**场景**：创建一个具有视差滚动效果的落地页

**关键代码**：

```css
/* 视差容器 */
.parallax-container {
  position: relative;
  height: 100vh;
  overflow-x: hidden;
  overflow-y: auto;
}

/* 视差背景 */
.parallax-bg {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 120%; /* 比容器稍高 */
  background: url('bg-image.jpg') center/cover no-repeat;
  transform: translateY(0);
  transition: transform 0.1s linear;
  z-index: -1;
}

/* 内容区域 */
.parallax-content {
  position: relative;
  z-index: 1;
}
```

```javascript
// 视差滚动效果
const parallaxBg = document.querySelector('.parallax-bg');
const parallaxContainer = document.querySelector('.parallax-container');

parallaxContainer.addEventListener('scroll', () => {
  const scrolled = parallaxContainer.scrollTop;
  const maxScroll = parallaxContainer.scrollHeight - parallaxContainer.clientHeight.clientHeight;
  const percentage = scrolled / maxScroll;

  // 背景以不同速度移动
  parallaxBg.style.transform = `translateY(${scrolled * 0.5}px)`;
});
```

### 6.6 React + Tailwind CSS 示例

**场景**：使用 React 和 Tailwind CSS 创建现代组件

**安装依赖**：
```bash
npm create-react-app my-app
cd my-app
npm install tailwindcss @tailwindcss/forms
npx tailwindcss init
```

**组件示例**：

```jsx
import React, { useState, useEffect } from 'react';

const FeatureCard = ({ icon, title, description, delay }) => {
  const [isVisible, setIsVisible] = useState(false);

  useEffect(() => {
    const timer = setTimeout(() => setIsVisible(true), delay);
    return () => clearTimeout(timer);
  }, [delay]);

  return (
    <div className={`
      bg-gradient-to-br from-gray-800 to-gray-900
      rounded-2xl p-6
      transform transition-all duration-700
      ${isVisible ? 'opacity-100 translate-y-0' : 'opacity-0 translate-y-8'}
      hover:scale-105 hover:shadow-2xl
    `}>
      <div className="text-4xl mb-4">{icon}</div>
      <h3 className="font-serif text-xl text-orange-400 mb-2">{title}</h3>
      <p className="text-gray-400 leading-relaxed">{description}</p>
    </div>
  );
};

const FeatureShowcase = () => {
  const features = [
    { icon: '🎨', title: '创意设计', description: '独特的视觉设计，让您的品牌脱颖而出' },
    { icon: '⚡', title: '性能优化', description: '极致的性能优化，提供流畅的用户体验' },
    { icon: '🎯', title: '跨平台兼容', description: '完美支持所有主流浏览器和设备'' },
    { icon: '🔒', title: '安全可靠', description: '企业级安全标准，保护您的数据安全' },
  ];

  return (
    <div className="min-h-screen bg-gradient-to-br from-slate-900 to-slate-800 p-8">
      <h1 className="text-5xl font-serif text-center text-orange-400 mb-12">
        为什么选择我们
      </h1>
      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-6 max-w-7xl mx-auto">
        {features.map((feature, index) => (
          <FeatureCard
            key={index}
            {...feature}
            delay={index * 150}
          />
        ))}
      </div>
    </div>
  );
};

export default FeatureShowcase;
```

### 6.7 最佳实践

#### ✅ 设计原则

1. **避免 AI 美学**
   - 不使用紫色渐变
   - 不使用 Inter 字体
   - 不使用可预测的居中布局
   - 不使用统一的圆角（8px, 12px）

2. **创造独特性**
   - 每个项目都应有不同的设计语言
   - 不要在多个设计中收敛于相同的选择
   - 使用大胆的、语境特定的调色板

3. **关注细节**
   - 微妙的悬停效果
   - 精致的阴影层次
   - 精确的间距控制
   - 流畅的过渡动画

4. **考虑可访问性**
   - 足够的颜色对比度
   - 清晰的焦点状态
   - 键盘导航支持
   - ARIA 标签

#### ❌ 常见错误

1. **过度动画**
   - 避免太多同时进行的动画
   - 提供动画的 `prefers-reduced-motion` 媒体查询支持

2. **性能问题**
   - 使用 `transform` 和 `opacity` 进行动画（GPU 加速）
   - 避免在动画中使用 `top`、`left`、`width`、`height`
   - 使用 `will-change` 谨慎提示浏览器

3. **响应式问题**
   - 始终使用相对单位（rem、em、%、vw、vh）
   - 测试移动端和平板设备
   - 使用 `clamp()` 处理字体大小

### 6.8 与其他技能对比

| 特性 | frontend-design | algorithmic-art | canvas-design |
|------|---------------|----------------|---------------|
| **输出** | Web 界面 | 交互式 HTML | 静态 PNG/PDF |
| **重点** | 用户体验 | 算法过程 | 最终视觉效果 |
| **技术** | HTML/CSS/JS/React | p5.js | Python/PIL |
| **交互性** | 完整交互 | 参数控件 | 无 |
| **应用场景** | Web 应用 | 生成艺术 | 打印/展览 |

---

## 7. brand-guidelines - 品牌风格指南

**brand-guidelines** 是应用 Anthropic 官方品牌颜色和排版的技能。

### 7.1 技能概述

**什么是品牌风格指南？**

品牌风格指南确保所有输出材料（演示文稿、文档、网站）与 Anthropic 品牌保持一致的视觉标识。

**核心功能**：
- **统一的颜色系统**：主色调和强调色
- **规范的排版**：Poppins 标题 + Lora 正文
- **智能回退**：自定义字体不可用时使用系统字体

### 7.2 品牌颜色规范

#### 主色调

| 颜色名称 | HEX 值 | RGB 值 | 用途 |
|---------|---------|---------|------|
| **深色** | `#141413` | (20, 20, 19) | 主要文本、深色背景 |
| **浅色** | `#faf9f5` | (250, 249, 245) | 浅色背景、深色背景上的文本 |

#### 中性色

| 颜色名称 | HEX 值 | RGB 值 | 用途 |
|---------|---------|---------|------|
| **中灰色** | `#b0aea5` | (176, 174, 165) | 次要元素、分隔线 |
| **浅灰色** | `#e8e6dc` | (232, 230, 220) | 微妙背景、边框 |

#### 强调色

| 颜色名称 | HEX 值 | RGB 值 | 用途 |
|---------|---------|---------|------|
| **橙色** | `#d97757` | (217, 119, 87) | 主要强调色、关键元素 |
| **蓝色** | `#6a9bcc` | (106, 155, 204) | 次要强调色、链接 |
| **绿色** | `#788c5d` | (120, 140, 93) | 第三强调色、成功提示 |

### 7.3 排版规范

#### 字体系统

| 用途 | 主字体 | 后备字体 |
|------|--------|---------|
| **标题** | Poppins | Arial |
| **正文** | Lora | Georgia |

#### 字体大小

```css
:root {
  /* 标题 */
  --font-size-h1: 48px;
  --font-size-h2: 36px;
  --font-size-h3: 28px;
  --font-size-h4: 22px;

  /* 正文 */
  --font-size-body: 16px;
  --font-size-small: 14px;
  --font-size-caption: 12px;
}
```

### 7.4 CSS 实现

```css
/* Anthropic 品牌变量 */
:root {
  --color-primary: #141413;
  --color-secondary: #faf9f5;
  --color-neutral: #b0aea5;
  --color-light: #e8e6dc;

  --color-accent-orange: #d97757;
  --color-accent-blue: #6a9bcc;
  --color-accent-green: #788c5d;

  --font-title: 'Poppins', Arial, sans-serif;
  --font-body: 'Lora', Georgia, serif;
}

/* 应用品牌样式 */
body {
  color: var(--color-primary);
  background-color: var(--color-secondary);
  font-family: var(--font-body);
  font-size: var(--font-size-body);
}

h1, h2, h3, h4, h5, h6 {
  font-family: var(--font-title);
  color: var(--color-primary);
}

h1 { font-size: var(--font-size-h1); }
h2 { font-size: var(--font-size-h2); }
h3 { font-size: var(--font-size-h3); }
h4 { font-size: var(--font-size-h4); }

/* 强调色类 */
.text-accent-orange { color: var(--color-accent-orange); }
.text-accent-blue { color: var(--color-accent-blue); }
.text-accent-green { color: var(--color-accent-green); }

.bg-accent-orange { background-color: var(--color-accent-orange); }
.bg-accent-blue { background-color: var(--color-accent-blue); }
.bg-accent-green { background-color: var(--color-accent-green); }
```

### 7.5 React 组件示例

```jsx
import React from 'react';

const BrandColors = {
  primary: '#141413',
  secondary: '#faf9f5',
  neutral: '#b0aea5',
  light: '#e8e6dc',
  accentOrange: '#d97757',
  accentBlue: '#6a9bcc',
  accentGreen: '#788c5d',
};

const BrandTypography = {
  title: 'Poppins, Arial, sans-serif',
  body: 'Lora, Georgia, serif',
};

const BrandButton = ({ variant = 'orange', children, ...props }) => {
  const colors = {
    orange: BrandColors.accentOrange,
    blue: BrandColors.accentBlue,
    green: BrandColors.accentGreen,
  };

  return (
    <button
      style={{
        backgroundColor: colors[variant],
        color: BrandColors.secondary,
        fontFamily: BrandTypography.title,
        padding: '12px 24px',
        borderRadius: '8px',
        border: 'none',
        cursor: 'pointer',
        transition: 'all 0.3s ease',
      }}
      {...props}
    >
      {children}
    </button>
  );
};

const BrandCard = ({ title, children }) => (
  <div
    style={{
      backgroundColor: BrandColors.secondary,
      border: `2px solid ${BrandColors.neutral}`,
      borderRadius: '12px',
      padding: '24px',
      fontFamily: BrandTypography.body,
    }}
  >
    <h2 style={{
      fontFamily: BrandTypography.title,
      color: BrandColors.accentOrange,
      marginBottom: '16px',
    }}>
      {title}
    </h2>
    {children}
  </div>
);
```

### 7.6 使用场景

#### 场景 1：应用品牌到网站

```html
<!DOCTYPE html>
<html lang="zh-CN">
<head>
  <link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;700&family=Lora:wght@400;700&display=swap" rel="stylesheet">
  <style>
    /* 品牌样式 */
    :root {
      --brand-primary: #141413;
      --brand-secondary: #faf9f5;
      --brand-accent: #d97757;
      --font-title: 'Poppins', Arial, sans-serif;
      --font-body: 'Lora', Georgia, serif;
    }

    body {
      font-family: var(--font-body);
      color: var(--brand-primary);
      background: var(--brand-secondary);
    }

    h1, h2, h3 {
      font-family: var(--font-title);
    }

    .cta-button {
      background: var(--brand-accent);
      color: var(--brand-secondary);
      font-family: var(--font-title);
    }
  </style>
</head>
<body>
  <h1>欢迎来到我们的网站</h1>
  <p class="text-body">这是符合 Anthropic 品牌风格的内容。</p>
  <button class="cta-button">了解更多</button>
</body>
</html>
```

#### 场景 2：品牌主题切换

```javascript
// 主题切换功能
const toggleBrandTheme = (isDark) => {
  const root = document.documentElement;

  if (isDark) {
    root.style.setProperty('--brand-primary', '#141413');
    root.style.setProperty('--brand-secondary', '#faf9f5');
  } else {
    // 浅色主题变体
    root.style.setProperty('--brand-primary', '#faf9f5');
    root.style.setProperty('--brand-secondary', '#141413');
  }
};
```

### 7.7 最佳实践

#### ✅ 使用建议

1. **始终使用 CSS 变量**
   - 便于全局主题更改
   - 保持颜色一致性

2. **提供字体回退**
   - 自定义字体可能未安装
   - 始终提供系统字体作为后备

3. **确保足够的对比度**
   - 文本与背景对比度至少 4.5:1
   - 大文本对比度至少 3:1

4. **保持品牌一致性**
   - 在所有材料上使用相同的颜色
   - 保持字体层级一致

#### ❌ 避免错误

1. **不要硬编码颜色值**
   - 使用语义化的变量名
   -   便于后续品牌更新

2. **不要违反品牌指南**
   - 避免使用品牌规范外的颜色
   - 保持视觉标识统一

3. **不要忽略可访问性**
   - 确保颜色对比度符合 WCAG
   - 提供适当的焦点状态

## 7. brand-guidelines - 品牌风格指南

[待写 - 详细教程和代码示例]

---

# 第三部分：文档处理类技能

## 8. docx - Word 文档处理

**docx** 是用于创建、读取、编辑和操作 Word 文档（.docx）的技能。

### 8.1 技能概述

**什么是 Word 文档处理？**

.docx 文件是一个包含 XML 文件的 ZIP 存档。docx 技能提供了完整的功能来：
- 创建新的格式化 Word 文档
- 读取和提取文档内容
- 编辑现有文档（包括修订和评论）
- 处理表格、图像、页眉页脚
- 生成专业报告和文档

**核心功能**：
- **创建新文档**：使用 docx-js（JavaScript）
- **编辑现有文档**：解包 → 编辑 XML → 重新打包
- **支持特性**：修订、评论、目录、表格、图像、页眉页脚

### 8.2 快速参考

| 任务 | 方法 |
|------|----------|
| 读取/分析内容 | `pandoc` 或解包以获取原始 XML |
| 创建新文档 | 使用 `docx-js` |
| 编辑现有文档 | 解包 → 编辑 XML → 重新打包 |

### 8.3 安装依赖

**JavaScript 依赖**：
```bash
npm install -g docx
```

**Python 依赖**（用于解析）：
```bash
pip install python-docx
```

**系统工具**：
```bash
# LibreOffice（用于转换）
# 已通过 scripts/office/soffice.py 自动配置

# Pandoc（用于文本提取）
# 需要单独安装
```

### 8.4 创建新文档

#### 基本结构

```javascript
const { Document, Packer, Paragraph, TextRun } = require('docx');

const doc = new Document({
  sections: [{
    properties: {
      page: {
        size: {
          width: 12240,   // 8.5 英寸，DXA 单位
          height: 15840   // 11 英寸，DXA 单位
        },
        margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 } // 1 英寸边距
      }
    },
    children: [
      new Paragraph({
        children: [
          new TextRun({
            text: "Hello World!",
            bold: true
          })
        ]
      })
    ]
  }]
});

Packer.toBuffer(doc).then(buffer => {
  const fs = require('fs');
  fs.writeFileSync('output.docx', buffer);
  console.log('✅ Word 文档已创建');
});
```

#### 常见页面尺寸（DXA 单位）

| 纸张 | 宽度 | 高度 | 内容宽度（1" 边距） |
|-------|-------|--------|---------------------------|
| US Letter | 12,240 | 15,840 | 9,360 |
| A4（默认） | 11,906 | 16,838 | 9,026 |

**注意**：1440 DXA = 1 英寸

### 8.5 添加样式和格式

#### 样式定义

```javascript
const { Document, Packer, Paragraph, TextRun, HeadingLevel } = require('docx');

const doc = new Document({
  styles: {
    default: {
      document: {
        run: { font: "Arial", size: 24 }  // 12pt 默认
      }
    },
    paragraphStyles: [
      // 覆盖内置标题样式
      {
        id: "Heading1",
        name: "Heading 1",
        basedOn: "Normal",
        next: "Normal",
        quickFormat: true,
        run: { size: 32, bold: true, font: "Arial" },
        paragraph: { spacing: { before: 240, after: 240 }, outlineLevel: 0 }
      },
      {
        id: "Heading2",
        name: "Heading 2",
        basedOn: "Normal",
        next: "Normal",
        quickFormat: true,
        run: { size: 28, bold: true, font: "Arial" },
        paragraph: { spacing: { before: 180, after: 180 }, outlineLevel: 1 }
      }
    ]
  },
  sections: [{
    children: [
      new Paragraph({
        heading: HeadingLevel.HEADING_1,
        children: [new TextRun("一级标题")]
      }),
      new Paragraph({
        heading: HeadingLevel.HEADING_2,
        children: [new TextRun("二级标题")]
      }),
    ]
  }]
});
```

#### 文本格式化

```javascript
const { TextRun, UnderlineType, convertInchesToPoint } = require('docx');

new Paragraph({
  children: [
    new TextRun({
      text: "粗体文本",
      bold: true,
      size: 28  // 14pt
    }),
    new TextRun(" "),
    new TextRun({
      text: "斜体文本",
      italics: true
    }),
    new TextRun(" "),
    new TextRun({
      text: "下划线文本",
      underline: {
        type: UnderlineType.SINGLE
      }
    }),
    new TextRun(" "),
    new TextRun({
      text: "彩色文本",
      color: "FF0000"  // RGB 红色
    }),
  ]
})
```

### 8.6 添加列表

**重要**：绝不使用 unicode 项目符号。使用`LevelFormat.BULLET`。

```javascript
const { Document, Packer, Paragraph, TextRun, LevelFormat, AlignmentType } = require('docx');

const doc = new Document({
  numbering: {
    config: [
      {
        reference: "my-bullets",
        levels: [
          {
            level: 0,
            format: LevelFormat.BULLET,
            text: "•",
            alignment: AlignmentType.LEFT,
            style: {
              paragraph: {
                indent: { left: 720, hanging: 360 }
              }
            }
          }
        ]
      },
      {
        reference: "my-numbers",
        levels: [
          {
            level: 0,
            format: LevelFormat.DECIMAL,
            text: "%1.",
            alignment: AlignmentType.LEFT,
            style: {
              paragraph: {
                indent: { left: 720, hanging: 360 }
              }
            }
          }
        ]
      }
    ]
  },
  sections: [{
    children: [
      new Paragraph({
        numbering: { reference: "my-bullets", level: 0 },
        children: [new TextRun("项目符号项目 1")]
      }),
      new Paragraph({
        numbering: { reference: "my-bullets", level: 0 },
        children: [new TextRun("项目符号项目 2")]
      }),
      new Paragraph({
        numbering: { reference: "my-numbers", level: 0 },
        children: [new TextRun("编号项目 1")]
      }),
      new Paragraph({
        numbering: { reference: "my-numbers", level: 0 },
        children: [new TextRun("编号项目 2")]
      }),
    ]
  }]
});
```

### 8.7 添加表格

**关键**：表格需要双重宽度 - 在表格上设置 `columnWidths`，在每个单元格上设置 `width`。

```javascript
const { Document, Packer, Table, TableRow, TableCell, WidthType, BorderStyle, ShadingType } = require('docx');

const border = { style: BorderStyle.SINGLE, size: 1, color: "CCCCCC" };
const borders = { top: border, bottom: border, left: border, right: border };

const doc = new Document({
  sections: [{
    children: [
      new Table({
        width: { size: 9360, type: WidthType.DXA },  // 始终使用 DXA
        columnWidths: [4680, 4680],  // 必须总和为表格宽度
        rows: [
          new TableRow({
            children: [
              new TableCell({
                borders,
                width: { size: 4680, type: WidthType.DXA },
                shading: { fill: "D5E8F0", type: ShadingType.CLEAR },
                margins: { top: 80, bottom: 80, left: 120, right: 120 },
                children: [
                  new Paragraph({
                    children: [new TextRun("列 1")]
                  })
                ]
              }),
              new TableCell({
                borders,
                width: { size: 4680, type: WidthType.DXA },
                shading: { fill: "D5E8F0", type: ShadingType.CLEAR },
                margins: { top: 80, bottom: 80, left: 120, right: 120 },
                children: [
                  new Paragraph({
                    children: [new TextRun("列 2")]
                  })
                ]
              }),
            ]
          }),
          new TableRow({
            children: [
              new TableCell({
                borders,
                width: { size: 4680, type: WidthType.DXA },
                children: [new Paragraph({ children: [new TextRun("数据 1")] })]
              }),
              new TableCell({
                borders,
                width: { size: 4680, type: WidthType.DXA },
                children: [new Paragraph({ children: [new TextRun("数据 2")] })]
              }),
            ]
          }),
        ]
      })
    ]
  }]
});
```

### 8.8 添加图像

```javascript
const { { Document, Packer, Paragraph, ImageRun } = require('docx');
const fs = require('fs');

const doc = new Document({
  sections: [{
    children: [
      new Paragraph({
        children: [
          new ImageRun({
            type: "png",  // 必需：png、jpg、jpeg、gif、bmp、svg
            data: fs.readFileSync("logo.png"),
            transformation: { width: 200, height: 150 },
            altText: {
              title: "Logo",
              description: "公司 Logo",
              name: "logo"
            }
          })
        ]
      })
    ]
  }]
});
```

### 8.9 添加页眉页脚

```javascript
const { Document, Packer, Paragraph, TextRun, Header, Footer, PageNumber } = require('docx');

const doc = new Document({
  sections: [{
    properties: {
      page: {
        margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 }
      }
    },
    headers: {
      default: new Header({
        children: [
          new Paragraph({
            children: [new TextRun("这是页眉")]
          })
        ]
      })
    },
    footers: {
      default: new Footer({
        children: [
          new Paragraph({
            alignment: "center",
            children: [
              new TextRun({
                children: [PageNumber.CURRENT]
              })
            ]
          })
        ]
      })
    },
    children: [
      // 文档内容
    ]
  }]
});
```

### 8.10 添加目录

```javascript
const { Document, Packer, TableOfContents } = require('docx');

const doc = new Document({
  sections: [{
    children: [
      new TableOfContents("目录", {
        hyperlink: true,
        headingStyleRange: "1-3"
      }),
      // 使用 HeadingLevel 创建的标题将自动出现在目录中
    ]
  }]
});
```

### 8.11 编辑现有文档

#### 步骤 1：解包

```bash
python scripts/office/unpack.py document.docx unpacked/
```

这将提取 XML 文件、美化打印、合并相邻运行。

#### 步骤 2：编辑 XML

编辑 `unpacked/word/` 中的文件。

**添加评论**：
```bash
python scripts/comment.py unpacked/ 0 "这是一个批注"
python scripts/comment.py unpacked/ 1 "回复批注" --parent 0
```

**使用智能引号**：
```xml
<!-- 使用 XML 实体以获得专业排版 -->
<w:t>Here&#x2019;s a quote: &#x201C;Hello&#x201D;</w:t>
```

| 实体 | 字符 |
|--------|-----------|
| `&#x2018;` | '（左单引号） |
| `&#x2019;` | '（右单引号/撇号） |
| `&#x201C;` | "（左双引号） |
| `&#x201D;` | "（右双引号） |

#### 步骤 3：打包

```bash
python scripts/office/pack.py unpacked/ output.docx --original document.docx
```

### 8.12 关键规则总结

| 规则 | 说明 |
|------|------|
| **显式设置页面大小** | docx-js 默认为 A4，需显式设置 |
| **绝不使用 `\n`** | 使用单独的 Paragraph 元素 |
| **绝不使用 unicode 项目符号** | 使用 LevelFormat.BULLET |
| **PageBreak 必须在 Paragraph 中** | 独立创建无效的 XML |
| **ImageRun 需要 `type`** | 始终指定 png/jpg/etc |
| **始终使用 DXA 设置表格宽度** | 永远不要使用 WidthType.PERCENTAGE |
| **表格需要双重宽度** | columnWidths 和单元格 width 都要设置 |
| **使用 ShadingType.CLEAR** | 永远不要使用 SOLID 进行表格着色 |
| **TOC 仅需要 HeadingLevel** | 标题段落上没有自定义样式 |
|）覆盖内置样式** | 使用确切的 ID："Heading1"、"Heading2" 等 |

### 8.13 实战示例：创建项目报告

```javascript
const { Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell,
        WidthType, BorderStyle, ShadingType, HeadingLevel, ImageRun } = require('docx');
const fs = require('fs');

// 数据
const reportData = {
  title: "项目周报 - 第 12 周",
  period: "2024年3月18日 - 3月22日",
  summary: "本周完成了用户认证模块的开发，并修复了 5 个高优先级 Bug。",
  achievements: [
    { item: "完成用户登录功能", status: "已完成", priority: "高" },
    { item: "实现权限管理系统", status: "进行中", priority: "高" },
    { item: "优化页面加载速度", status: "已完成", priority: "中" },
    { item: "编写 API 文档", status: "已完成", priority: "低" }
  ],
  metrics: {
    bugsFixed: 5,
    featuresCompleted: 3,
    codeCoverage: "85%"
  }
};

// 创建文档
const doc = new Document({
  styles: {
    default: {
      document: { run: { font: "Arial", size: 24 } }
    },
    paragraphStyles: [
      {
        id: "Heading1",
        name: "Heading 1",
        basedOn: "Normal",
        next: "Normal",
        quickFormat: true,
        run: { size: 32, bold: true, font: "Arial", color: "2D3748" },
        paragraph: { spacing: { before: 240, after: 240 } }
      },
      {
        id: "Heading2",
        name: "Heading 2",
        basedOn: "Normal",
        next: "Normal",
        quickFormat: true,
        run: { size: 28, bold: true, font: "Arial", color: "2D3748" },
        paragraph: { spacing: { before: 180, after: 180 } }
      }
    ]
  },
  sections: [{
    properties: {
      page: {
        size: { width: 12240, height: 15840 },
        margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 }
      }
    },
    children: [
      // 标题
      new Paragraph({
        heading: HeadingLevel.HEADING_1,
        alignment: "center",
        children: [new TextRun(reportData.title)]
      }),

      new Paragraph({
        children: [new TextRun(`周期：${reportData.period}`)]
      }),

      new Paragraph({ text: "" }),

      // 摘要
      new Paragraph({
        heading: HeadingLevel.HEADING_2,
        children: [new TextRun("执行摘要")]
      }),

      new Paragraph({
        children: [new TextRun(reportData.summary)]
      }),

      new Paragraph({ text: "" }),

      // 成就表格
      new Paragraph({
        heading: HeadingLevel.HEADING_2,
        children: [new TextRun("本周成就")]
      }),

      // 创建表格
      new Table({
        width: { size: 9360, type: WidthType.DXA },
        columnWidths: [4680, 2340, 2340],
        rows: [
          // 表头
          new TableRow({
            children: [
              new TableCell({
                width: { size: 4680, type: WidthType.DXA },
                shading: { fill: "2D3748", type: ShadingType.CLEAR },
                children: [new Paragraph({ children: [new TextRun({ text: "任务", bold: true, color: "FFFFFF" })] })]
              }),
              new TableCell({
                width: { size: 2340, type: WidthType.DXA },
                shading: { fill: "2D3748", type: ShadingType.CLEAR },
                children: [new Paragraph({ children: [new TextRun({ text: "状态", bold: true, color: "FFFFFF" })] })]
              }),
              new TableCell({
                width: { size: 2340, type: WidthType.DXA },
                shading: { fill: "2D3748", type: ShadingType.CLEAR },
                children: [new Paragraph({ children: [new TextRun({ text: "优先级", bold: true, color: "FFFFFF" })] })]
              }),
            ]
          }),
          // 数据行
          ...reportData.achievements.map(ach =>
            new TableRow({
              children: [
                new TableCell({
                  width: { size: 4680, type: WidthType.DXA },
                  children: [new Paragraph({ children: [new TextRun(ach.item)] })]
                }),
                new TableCell({
                  width: { size: 2340, type: WidthType.DXA },
                  children: [new Paragraph({ children: [new TextRun(ach.status)] })]
                }),
                new TableCell({
                  width: { size: 2340, type: WidthType.DXA },
                  children: [new Paragraph({ children: [new TextRun(ach.priority)] })]
                }),
              ]
            })
          )
        ]
      })
    ]
  }]
});

// 保存文档
Packer.toBuffer(doc).then(buffer => {
  fs.writeFileSync('项目周报.docx', buffer);
  console.log('✅ 项目周报已创建');
});
```

---

## 9. pdf - PDF 文档处理

**pdf** 是用于执行各种 PDF 操作的技能。

### 9.1 技能概述

**什么是 PDF 处理？**

PDF 处理包括读取、提取、操作和创建 PDF 文件的各种操作。

**核心功能**：
- **读取/提取**：文本提取（pypdf、pdfplumber）、表格提取
- **操作**：合并、拆分、旋转、添加水印
- **创建**：使用 reportlab 创建新 PDF
- **高级**：OCR（扫描 PDF）、密码保护、图像提取

### 9.2 安装依赖

```bash
# Python 库
pip install pypdf pdfplumber reportlab

# OCR 功能（可选）
pip install pytesseract pdf2image

# 命令行工具
# qpdf、pdftotext、pdfimages 需要单独安装
```

### 9.3 pypdf - 基本操作

#### 合并 PDF

```python
from pypdf import PdfWriter, PdfReader

writer = PdfWriter()

for pdf_file in ["doc1.pdf", "doc2.pdf", "doc3.pdf"]:
    reader = PdfReader(pdf_file)
    for page in reader.pages:
        writer.add_page(page)

with open("merged.pdf", "wb") as output:
    writer.write(output)
    print("✅ PDF 合并完成")
```

#### 拆分 PDF

```python
from pypdf import PdfReader, PdfWriter

reader = PdfReader("input.pdf")

# 拆分每一页
for i, page in enumerate(reader.pages):
    writer = PdfWriter()
    writer.add_page(page)
    with open(f"page_{i+1}.pdf", "wb") as output:
        writer.write(output)

print(f"✅ 已拆分 {len(reader.pages)} 页")
```

#### 旋转页面

```python
from pypdf import PdfReader, PdfWriter

reader = PdfReader("input.pdf")
writer = PdfWriter()

page = reader.pages[0]
page.rotate(90)  # 顺时针旋转 90 度
writer.add_page(page)

with open("rotated.pdf", "wb") as output:
    writer.write(output)
```

#### 提取元数据

```python
from pypdf import PdfReader

reader = PdfReader("document.pdf")
meta = reader.metadata

print(f"标题：{meta.get('/Title', 'N/A')}")
print(f"作者：{meta.get('/Author', 'N/A')}")
print(f"主题：{meta.get('/Subject', 'N/A')}")
print(f"创建者：{meta.get('/Creator', 'N/A')}")
```

### 9.4 pdfplumber - 文本和表格提取

#### 提取文本（带布局）

```python
import pdfplumber

with pdfplumber.open("document.pdf") as pdf:
    for i, page in enumerate(pdf.pages):
        text = page.extract_text()
        print(f"--- 第 {i+1} 页 ---")
        print(text)
```

#### 提取表格

```python
import pdfplumber
import pandas as pd

with pdfplumber.open("document.pdf") as pdf:
    all_tables = []

    for i, page in enumerate(pdf.pages):
        tables = page.extract_tables()

        for j, table in enumerate(tables):
            if table:  # 检查表格是否为空
                print(f"第 {i+1} 页的表格 {j+1}：")

                # 转换为 DataFrame
                df = pd.DataFrame(table[1:], columns=table[0])
                print(df.to_string())
                all_tables.append(df)

    # 保存所有表格到 Excel
    if all_tables:
        combined_df = pd.concat(all_tables, ignore_index=True)
        combined_df.to_excel("extracted_tables.xlsx", index=False)
        print("✅ 表格已提取到 Excel")
```

### 9.5 reportlab - 创建 PDF

#### 基本 PDF 创建

```python
from reportlab.lib.pagesizes import letter, A4
from reportlab.pdfgen import canvas

# 创建 PDF
c = canvas.Canvas("hello.pdf", pagesize=letter)
width, height = letter

# 添加文本
c.drawString(100, height - 100, "Hello World!")
c.drawString(100, height - 120, "这是使用 reportlab 创建的 PDF")

# 添加线条
c.line(100, height - 140, 400, height - 140)

# 保存
c.save()
print("✅ PDF 已创建")
```

#### 使用 Platypus 创建复杂文档

```python
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, PageBreak, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet
from reportlab.lib import colors

doc = SimpleDocTemplate("report.pdf", pagesize=letter)
styles = getSampleStyleSheet()
story = []

# 添加标题
title = Paragraph("报告标题", styles['Title'])
story.append(title)
story.append(Spacer(1, 12))

# 添加正文
body = Paragraph("这是报告的正文内容。" * 10, styles['Normal'])
story.append(body)
story.append(PageBreak())

# 第 2 页
story.append(Paragraph("第 2 页", styles['Heading1']))

# 添加表格
data = [
    ['列 1', '列 2', '列 3'],
    ['数据 1', '数据 2', '数据 3'],
    ['数据 4', '数据 5', '数据 6'],
]

table = Table(data, style=TableStyle([
    ('BACKGROUND', (0, 0), (-1, 0), colors.grey),
    ('TEXTCOLOR', (0, 0), (-1, 0), colors.whitesmoke),
    ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
    ('FONTSIZE', (0, 0), (-1, 0), 14),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 12),
    ('BACKGROUND', (0, 1), (-1, -1), colors.beige),
    ('GRID', (0, 0), (-1, -1), 1, colors.black),
]))

story.append(table)

# 构建 PDF
doc.build(story)
print("✅ 复杂 PDF 报告已创建")
```

####下标和上标

**重要**：永远不要在 ReportLab PDF 中使用 Unicode 下标/上标字符。

```python
from reportlab.platypus import Paragraph
from reportlab.lib.styles import getSampleStyleSheet

styles = getSampleStyleSheet()

# 下标：使用 <sub> 标签
chemical = Paragraph("H<sub>2</sub>O", styles['Normal'])

# 上标：使用 <super> 标签
squared = Paragraph("x<super>2</super> + y<super>2</super>", styles['Normal'])
```

### 9.6 常见任务

#### 从扫描的 PDF 中提取文本（OCR）

```python
import pytesseract
from pdf2image import convert_from_path

# 将 PDF 转换为图像
images = convert_from_path('scanned.pdf')

# 对每页进行 OCR
text = ""
for i, image in enumerate(images):
    text += f"第 {i+1} 页：\n"
    text += pytesseract.image_to_string(image)
    text += "\n\n"

with open("extracted_text.txt", "w", encoding="utf-8") as f:
    f.write(text)

print("✅ OCR 文本已提取")
```

#### 添加水印

```python
from pypdf import PdfReader, PdfWriter

# 创建水印
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import letter

c = canvas.Canvas("watermark.pdf", pagesize=letter)
c.setFillColorRGB(0.9, 0.9, 0.9, alpha=0.3)
c.setFont("Helvetica", 60)
c.drawString(100, 300, "机密文档")
c.save()

# 应用水印
watermark = PdfReader("watermark.pdf").pages[0]
reader = PdfReader("document.pdf")
writer = PdfWriter()

for page in reader.pages:
    page.merge_page(watermark)
    writer.add_page(page)

with open("watermarked.pdf", "wb") as output:
    writer.write(output)
```

#### 密码保护

```python
from pypdf import PdfReader, PdfWriter

reader = PdfReader("input.pdf")
writer = PdfWriter()

for page in reader.pages:
    writer.add_page(page)

# 添加密码
writer.encrypt("userpassword", "ownerpassword")

with open("encrypted.pdf", "wb") as output:
    writer.write(output)
```

### 9.7 命令行工具

#### qpdf（推荐用于合并和拆分）

```bash
# 合并 PDF
qpdf --empty --pages file1.pdf file2.pdf -- merged.pdf

# 拆分页面
qpdf input.pdf --pages . 1-5 -- pages1-5.pdf
qpdf input.pdf --pages . 6-10 -- pages6-10.pdf

# 旋转页面
qpdf input.pdf output.pdf --rotate=+90:1

# 删除密码
qpdf --password=mypassword --decrypt encrypted.pdf decrypted.pdf
```

#### pdftotext

```bash
# 提取文本
pdftotext input.pdf output.txt

# 保留布局提取文本
pdftotext -layout input.pdf output.txt

# 提取特定页面
pdftotext -f 1 -l 5 input.pdf output.txt  # 页面 1-5
```

### 9.8 实战示例：创建数据报告 PDF

```python
from reportlab.lib.pagesizes import A4
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib import colors
from reportlab.lib.units import cm
from reportlab.pdfgen import canvas

# 数据
report_data = {
    "title": "销售数据报告",
    "date": "2024年3月",
    "summary": "本月销售业绩超出预期，同比增长 15%。",
    "sales_data": [
        ["产品", "销量", "销售额 (万元)", "增长率"],
        ["产品 A", "1000", "50", "+15%"],
        ["产品 B", "800", "40", "+10%"],
        ["产品 C", "1200", "60", "+20%"],
        ["产品 D", "600", "30", "+5%"],
    ],
    "total": 180  # 万元
}

# 自定义样式
styles = getSampleStyleSheet()
styles.add(ParagraphStyle(
    name='CustomTitle',
    parent=styles['Heading1'],
    fontSize=24,
    textColor=colors.HexColor('#2D3748'),
    spaceAfter=20,
))

# 创建文档
doc = SimpleDocTemplate("sales_report.pdf", pagesize=A4)
story = []

# 标题页
story.append(Paragraph(report_data["title"], styles['CustomTitle']))
story.append(Paragraph(f"报告日期：{report_data['date']}", styles['Normal']))
story.append(Spacer(1, 30))
story.append(Paragraph("执行摘要", styles['Heading2']))
story.append(Paragraph(report_data["summary"], styles['Normal']))
story.append(PageBreak())

# 数据页
story.append(Paragraph("销售数据", styles['Heading2']))
story.append(Spacer(1, 20))

# 创建表格
table = Table(report_data["sales_data"], style=TableStyle([
    ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#2D3748')),
    ('TEXTCOLOR', (0, 0), (-1, 0), colors.whitesmoke),
    ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
    ('FONTSIZE', (0, 0), (-1, 0), 12),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 12),
    ('LEFTPADDING', (0, 0), (-1, -1), 12),
    ('RIGHTPADDING', (0, 0), (-1, -1), 12),
    ('BACKGROUND', (0, 1), (-1, -1), colors.beige),
    ('GRID', (0, 0), (-1, -1), 1, colors.black),
]))

story.append(table)
story.append(Spacer(1, 20))

# 总计
story.append(Paragraph(f"总销售额：{report_data['total']} 万元", styles['Heading2']))

# 添加图表（使用 canvas）
# 这里可以添加图片或绘制图表

# 构建 PDF
doc.build(story)
print("✅ 销售报告已生成")
```

### 9.9 快速参考

| 任务 | 最佳工具 | 命令/代码 |
|------|-----------|--------------|
| 合并 PDF | pypdf | `writer.add_page(page)` |
| 拆分 PDF | pypdf | 每个文件一个页面 |
| 提取文本 | pdfplumber | `page.extract_text()` |
| 提取表格 | pdfplumber | `page.extract_tables()` |
| 创建 PDF | reportlab | Canvas 或 Platypus |
| 命令行合并 | qpdf | `qpdf --empty --pages ...` |
| OCR 扫描 PDF | pytesseract | 首先转换为图像 |

---

## 10. pptx - 演示文稿创建

**pptx** 是用于创建、编辑、读取 PowerPoint 演示文稿的技能。

### 10.1 技能概述

**什么是 PowerPoint 处理？**

PowerPoint 处理包括创建、编辑和分析 .pptx 文件。

**核心功能**：
- **从头创建**：使用 PptxGenJS（JavaScript）
- **基于模板编辑**：解包 → 编辑 XML → 重新打包
- **设计理念**：避免单调布局，强调视觉元素

### 10.2 安装依赖

```bash
# JavaScript
npm install -g pptxgenjs

# Python（用于解析）
pip install "markitdown[pptx]"
```

### 10.3 设计理念

#### 设计原则

**不要创建无聊的幻灯片**。每张幻灯片都需要视觉元素。

**调色板选择**：

| 主题 | 主色 | 辅助色 | 强调色 |
|-------|---------|-----------|--------|
| **午夜行政** | `#1E2761` 海军蓝 | `#CADCFC` 冰蓝 | `#FFFFFF` 白色 |
| **森林与苔藓** | `#2C5F2D` 森林 | `#97BC62` 苔藓 | `#F5F5F5` 奶油色 |
| **珊瑚能量** | `#F96167` 珊瑚色 | `#F9E795` 金色 | `#2F3C7E` 海军蓝 |
| **暖赤陶** | `#B85042` 赤陶色 | `#E7E8D1` 沙色 | `#A7BEAE` 鼠尾草 |

#### 每张幻灯片的要求

1. **视觉元素**：图像、图表、图标或形状
2. **多样化布局**：双栏、网格、半出血图像
3. **大胆对比度**：足够的颜色对比
4. **恰当间距**：最小边距 0.5"

### 10.4 使用 PptxGenJS 创建

#### 基本结构

```javascript
const PptxGenJS = require("pptxgenjs");
const fs = require("fs");

const pres = new PptxGenJS();

// 添加幻灯片
pres.addSlide({
  title: "幻灯片标题",
  background: { color: "1E2761" }, // 深色背景
  objects: [
    {
      text: "Hello World!",
      options: {
        x: 1,
        y: 1,
        w: 8,
        h: 1,
        color: "FFFFFF",
        fontSize: 36,
        bold: true
      }
    }
  ]
});

// 保存
pres.writeFile({ fileName: "presentation.pptx" });
```

#### 添加不同类型的内容

```javascript
const PptxGenJS = require("pptxgenjs");

const pres = new PptxGenJS();

// 幻灯片 1：标题页
pres.addSlide({
  title: "产品发布会",
  subtitle: "2024年第一季度",
  background: { color: "2C5F2D" },
  objects: [
    {
      image: { path: "logo.png" },
      options: { x: 1, y: 1, w: 2, h: 2 }
    }
  ]
});

// 幻灯片 2：双栏布局
pres.addSlide({
  title: "产品特性",
  background: { color: "F5F5F5" },
  objects: [
    {
      text: "左侧内容\n\n- 特性 1\n- 特性 2\n- 特性 3",
      options: {
        x: 0.5,
        y: 1.5,
        w: 4,
        h: 4,
        color: "2C5F2D",
        fontSize: 18
      }
    },
    {
      image: { path: "product.png" },
      options: { x: 5, y: 1.5, w: 4.5, h: 4 }
    }
  ]
});

// 幻灯片 3：表格
pres.addSlide({
  title: "销售数据",
  objects: [
    {
      table: {
        rows: [
          ["产品", "Q1", "Q2", "Q3", "Q4"],
          ["A", "100", "150", "200", "250"],
          ["B", "80", "120", "160", "200"],
          ["C", "200", "250", "300", "350"],
        ],
        options: {
          x: 1,
          y: 1.5,
          w: 8,
          h: 4,
          border: { pt: 1, color: "CADCFC" },
          fill: { color: "FFFFFF" },
          colW: [2, 1.5, 1.5, 1.5, 1.5],
        }
      }
    }
  ]
});

// 幻灯片 4：图表
pres.addSlide({
  title: "增长趋势",
  objects: [
    {
      chart: {
        type: "BAR",
        data: [
          {
            name: "2022",
            labels: ["Q1", "Q2", "Q3", "Q4"],
            values: [100, 120, 140, 160]
          },
          {
            name: "2023",
            labels: ["Q1", "Q2", "Q3", "Q4"],
            values: [150, 170, 190, 210]
          }
        ],
        options: {
          x: 1,
          y: 1.5,
          w: 8,
          h: 4.5,
          chartColors: ["2C5F2D", "97BC62"]
        }
      }
    }
  ]
});

pres.writeFile({ fileName: "product-launch.pptx" });
```

### 10.5 编辑现有演示文稿

#### 步骤 1：分析模板

```bash
# 生成缩略图预览
python scripts/thumbnail.py template.pptx
```

#### 步骤 2：解包

```bash
python scripts/office/unpack.py presentation.pptx unpacked/
```

#### 步骤 3：编辑 XML

编辑 `unpacked/ppt/slides/slide1.xml` 等文件。

#### 步骤 4：打包

```bash
python scripts/office/pack.py unpacked/ output.pptx --original presentation.pptx
```

### 10.6 质量保证

#### 内容检查

```bash
# 提取内容检查
python -m markitdown presentation.pptx

# 检查占位符文本
python -m markitdown presentation.pptx | grep -iE "xxxx|lorem|ipsum"
```

#### 视觉检查

```bash
# 转换为图像检查
python scripts/office/soffice.py --headless --convert-to pdf presentation.pptx
pdftoppm -jpeg -r 150 presentation.pdf slide
```

### 10.7 实战示例：创建产品推介

```javascript
const PptxGenJS = require("pptxgenjs");

// 主题配色
const theme = {
  primary: "#1E2761",  // 深蓝
  secondary: "#CADCFC",  // 浅蓝
  accent: "#F96167",   // 珊瑚
  light: "#FFFFFF"     // 白色
};

const pres = new PptxGenJS();

// 定义幻灯片母版
pres.defineSlideMaster({
  title: "TITLE_SLIDE",
  background: { color: theme.primary },
  objects: [
    {
      rect: { x: 0, y: 0, w: 10, h: 0.5, fill: { color: theme.secondary } }
    },
    {
      text: "产品推介会",
      options: {
        x: 9,
        y: 0.1,
        w: 1,
        h: 0.3,
        color: theme.light,
        align: "right",
        fontSize: 14
      }
    }
  ]
});

// 幻灯片 1：标题
pres.addSlide({
  masterName: "TITLE_SLIDE",
  objects: [
    {
      text: "新产品发布\n2024 年版",
      options: {
        x: 1,
        y: 2,
        w: 8,
        h: 2,
        color: theme.light,
        fontSize: 54,
        bold: true,
        align: "center"
      }
    },
    {
      rect: {
        x: 3,
        y: 4.5,
        w: 4,
        h: 0.5,
        fill: { color: theme.accent }
      }
    },
    {
      text: "创新 · 智能 · 高效",
      options: {
        x: 1,
        y: 5.5,
        w: 8,
        h: 0.5,
        color: theme.light,
        fontSize: 24,
        align: "center"
      }
    }
  ]
});

// 幻灯片 2：产品特性
pres.addSlide({
  title: "核心特性",
  background: { color: theme.light },
  objects: [
    // 左侧文字
    {
      text: "1. 智能分析\n\n2. 实时同步\n\n3. 多端协作\n\n4. 安全可靠",
      options: {
        x: 0.5,
        y: 1.5,
        w: 4,
        h: 4,
        color: theme.primary,
        fontSize: 20,
        bullet: true
      }
    },
    // 右侧图标
    {
      shape: pres.ShapeType.ROUNDED_RECTANGLE,
      options: {
        x: 5.5,
        y: 2,
        w: 3,
        h: 3,
        fill: { color: theme.secondary },
        line: { color: theme.accent, width: 2 }
      }
    },
    {
      text: "图标",
      options: {
        x: 5.5,
        y: 3.2,
        w: 3,
        h: 0.5,
        color: theme.light,
        fontSize: 24,
        align: "center",
        bold: true
      }
    }
  ]
});

// 幻灯片 3：数据展示
pres.addSlide({
  title: "市场数据",
  background: { color: theme.light },
  objects: [
    {
      chart: {
        type: "PIE",
        data: [
          {
            name: "市场份额",
            labels: ["Q1", "Q2", "Q3", "Q4"],
            values: [25, 30, 25, 20]
          }
        ],
        options: {
          x: 1,
          y: 1.5,
          w: 8,
          h: 4.5,
          chartColors: [theme.primary, theme.secondary, theme.accent, "#2C5F2D"],
          showLegend: true
        }
      }
    }
  ]
});

// 幻灯片 4：结束页
pres.addSlide({
  masterName: "TITLE_SLIDE",
  objects: [
    {
      text: "谢谢！",
      options: {
        x: 1,
        y: 3,
        w: 8,
        h: 1,
        color: theme.light,
        fontSize: 72,
        bold: true,
        align: "center"
      }
    },
    {
      text: "contact@example.com\nwww.example.com",
      options: {
        x: 1,
        y: 4.5,
        w: 8,
        h: 0.5,
        color: theme.secondary,
        fontSize: 16,
        align: "center"
      }
    }
  ]
});

pres.writeFile({ fileName: "product-pitch.pptx" });
console.log("✅ 产品推介已创建");
```

---

## 11. xlsx - 电子表格处理

**xlsx** 是用于创建、编辑、分析 Excel 电子表格的技能。

### 11.1 技能概述

**什么是 Excel 电子表格处理？**

Excel 处理包括数据操作、公式计算、格式化和财务建模。

**核心功能**：
- **数据分析**：使用 pandas
- **公式/格式**：使用 openpyxl
- **财务模型**：行业标准颜色编码、数字格式
- **公式验证**：使用 scripts/recalc.py 重新计算

### 11.2 安装依赖

```bash
pip install openpyxl pandas
```

### 11.3 财务模型规范

#### 颜色编码标准

| 颜色 | RGB 值 | 用途 |
|------|--------|------|
| **蓝色文本** | (0, 0, 255) | 硬编码输入 |
| **黑色文本** | (0, 0, 0) | 公式 |
| **绿色文本** | (0, 128, 0) | 工作簿内链接 |
| **红色文本** | (255, 0, 0) | 外部链接 |
| **黄色背景** | (255, 255, 0) | 关键假设 |

#### 数字格式标准

```python
# 年份：格式化为文本字符串
"2024"  # 不是 "2,024"

# 货币：$#,##0 格式
"$1,000,000"

# 零：显示为 "-"
"-"

# 百分比：0.0% 格式
"15.0%"

# 负数：使用括号
"(123)"
```

### 11.4 使用 openpyxl

#### 创建新工作簿

```python
from openpyxl import Workbook
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side

wb = Workbook()
ws = wb.active
ws.title = "数据表"

# 设置标题
headers = ["产品", "销量", "单价", "总金额"]
for col, header in enumerate(headers, 1):
    cell = ws.cell(row=1, column=col)
    cell.value = header
    cell.font = Font(bold=True, color="FFFFFF")
    cell.fill = PatternFill(start_color="2D3748", end_color="2D3748", fill_type="solid")
    cell.alignment = Alignment(horizontal="center")

# 添加数据
data = [
    ["产品 A", 100, 50],
    ["产品 B", 80, 60],
    ["产品 C", 120, 45],
]

for row_idx, row_data in enumerate(data, 2):
    for col_idx, value in enumerate(row_data, 1):
        cell = ws.cell(row=row_idx, column=col_idx)
        cell.value = value
        cell.alignment = Alignment(horizontal="center")

# 添加公式
for row_idx in range(2, len(data) + 2):
    ws.cell(row=row_idx, column=4).value = f"=B{row_idx}*C{row_idx}"
    ws.cell(row=row_idx, column=4).font = Font(color="000000")  # 黑色=公式

# 添加总计
ws.cell(row=len(data) + 2, column=1).value = "总计"
ws.cell(row=len(data) + 2, column=1).font = Font(bold=True)
ws.cell(row=len(data) + 2, column=2).value = f"=SUM(B2:B{len(data)+1})"
ws.cell(row=len(data) + 2, column=3).value = f"=AVERAGE(C2:C{len(data)+1})"
ws.cell(row=len(data) + 2, column=4).value = f"=SUM(D2:D{len(data)+1})"

# 设置列宽
ws.column_dimensions['A'].width = 15
ws.column_dimensions['B'].width = 10
ws.column_dimensions['C'].width = 12
ws.column_dimensions['D'].width = 15

# 保存
wb.save("sales_report.xlsx")
print("✅ 销售报告已创建")
```

#### 编辑现有工作簿

```python
from openpyxl import load_workbook

wb = load_workbook("existing.xlsx")
ws = wb.active

# 修改单元格
ws['A1'] = "新标题"

# 添加新行
ws.append(["新数据", 100, 50])

# 保存
wb.save("modified.xlsx")
```

### 11.5 使用 pandas

#### 数据分析

```python
import pandas as pd

# 读取 Excel
df = pd.read_excel('data.xlsx')

# 数据分析
print(f"总行数：{len(df)}")
print(f"平均值：\n{df.mean()}")
print(f"统计信息：\n{df.describe()}")

# 筛选数据
filtered = df[df['销量'] > 100]

# 添加新列
df['总金额'] = df['销量'] * df['单价']

# 分组统计
grouped = df.groupby('类别').agg({
    '销量': 'sum',
    '总金额': 'sum'
})

# 保存
df.to_excel('processed_data.xlsx', index=False)
grouped.to_excel('summary.xlsx', index=False)
```

### 11.6 实战示例：财务模型

```python
from openpyxl import Workbook
from openpyxl.styles import Font, PatternFill, Alignment, NamedStyle
from openpyxl.utils import get_column_letter

wb = Workbook()
ws = wb.active
ws.title = "财务模型"

# 样式定义
blue_text = Font(color="0000FF")  # 硬编码输入
black_text = Font(color="000000")  # 公式
green_text = Font(color="008000")  # 工作簿链接
red_text = Font(color="FF0000")    # 外部链接
yellow_fill = PatternFill(start_color="FFFF00", end_color="FFFF00", fill_type="solid")
bold = Font(bold=True)
center = Alignment(horizontal="center", vertical="center")

# 标题
ws.merge_cells('A1:D1')
ws['A1'].value = "三年度财务模型"
ws['A1'].font = Font(bold=True, size=16)
ws['A1'].alignment = center

# 假设部分
ws['A3'] = "假设"
ws['A3'].font = bold
A_range = ["销售增长率", "毛利率", "运营费用率"]
B_range = ["15%", "60%", "40%"]

for i, (assumption, value) in enumerate(zip(A_range, B_range), 4):
    ws[f'A{i}'] = assumption
    ws[f'A{i}'].font = bold
    ws[f'B{i}'] = value
    ws[f'B{i}'].font = blue_text
    ws[f'B{i}'].alignment = Alignment(horizontal="right")

# 年度数据
years = [2024, 2025, 2026]
revenue_start = 1000  # 起始收入

ws['A7'] = "收入"
ws['A7'].font = bold

# 第一年的收入
ws[f'B7'] = revenue_start
ws[f'B7'].font = blue_text

# 后续年份的收入公式
for i, year in enumerate(years[1:], 2):
    col = get_column_letter(i + 1)  # B, C, D
    prev_col = get_column_letter(i)
    ws[f'{col}7'] = f"={prev_col}7*(1+B{3})"  # 应用增长率
    ws[f'{col}7'].font = black_text

# 其他财务指标
ws['A8'] = "毛利润"
ws['A8'].font = bold
for i in range(1, len(years) + 1):
    col = get_column_letter(i)
    ws[f'{col}8'] = f"={col}7*B$4"  # 收入 * 毛利率
    ws[f'{col}8'].font = black_text

ws['A9'] = "运营费用"
ws['A9'].font = bold
for i in range(1, len(years) + 1):
    col = get_column_letter(i)
    ws[f'{col}9'] = f"={col}7*B$5"  # 收入 * 运营费用率
    ws[f'{col}9'].font = black_text

ws['A10'] = "净利润"
ws['A10'].font = bold
for i in range(1, len(years) + 1):
    col = get_column_letter(i)
    ws[f'{col}10'] = f"={col}8-{col}9"  # 毛利润 - 运营费用
    ws[f'{col}10'].font = black_text

# 设置列宽和格式
ws.column_dimensions['A'].width = 15
for i in range(1, 5):
    col = get_column_letter(i)
    ws.column_dimensions[col].width = 12
    # 设置数字格式
    for row in range(7, 11):
        ws[f'{col}{row}'].number_format = '#,##0'

# 添加边框
thin_border = Border(
    left=Side(style='thin'),
    right=Side(style='thin'),
    top=Side(style='thin'),
    bottom=Side(style='thin')
)

for row in range(7, 11):
    for col in range(1, 5):
        cell = ws[get_column_letter(col) + str(row)]
        cell.border = thin_border

wb.save("financial_model.xlsx")
print("✅ 财务模型已创建")
```

### 11.7 公式验证

使用 `scripts/recalc.py` 重新计算公式：

```bash
python scripts/recalc.py output.xlsx
```

该脚本返回包含错误详细信息的 JSON：

```json
{
  "status": "success",           // 或 "errors_found"
  "total_errors": 0,              // 总错误计数
  "total_formulas": 42,           // 文件中的公式数量
  "error_summary": {              // { 发现错误时存在
    "#REF!": {
      "count": 2,
      "locations": ["Sheet1!B5", "Sheet1!C10"]
    }
  }
}
```

### 11.8 最佳实践

| 原则 | 说明 |
|------|------|
| **始终使用公式** | 不要硬编码计算值 |
| **使用颜色编码** | 遵循行业标准 |
| **假设单独存放** | 便于修改和追踪 |
| **公式验证** | 使用 recalc.py 检查错误 |
| **格式化统一** | 一致的数字格式和样式 |

---

# 第四部分：开发工具类技能

## 12. mcp-builder - MCP 服务器构建

**mcp-builder** 是用于创建高质量 MCP（模型上下文协议）服务器的技能。

### 12.1 技能概述

**什么是 MCP 服务器？**

MCP（Model Context Protocol，模型上下文协议）是一种标准化协议，使 LLM 能够通过精心设计的工具与外部服务交互。

**核心功能**：
- 深入研究和规划
- TypeScript 或 Python 实现
- 代码质量审查和测试
- 创建评估（10 个 QA 对问题）

### 12.2 工作流程

#### 第 1 阶段：深入研究和规划

**了解现代 MCP 设计**：

| 设计决策 | 说明 |
|---------|------|
| **API 覆盖范围** | 全面覆盖 vs 工作流工具 |
| **工具命名** | 清晰、描述性的名称（如 `github_create_issue`） |
| **上下文管理** | 简洁的工具描述、过滤/分页结果 |
| **错误消息** | 可操作的错误消息，提供解决建议 |

**研究 MCP 协议文档**：
```
站点地图：https://modelcontextprotocol.io/sitemap.xml
规范页面：https://modelcontextprotocol.io/specification/draft.md
```

**规划您的实现**：
1. 了解 API 的关键端点
2. 确定身份验证要求
3. 列出要实现的端点

#### 第 2 阶段：实现

**推荐堆栈**：
- **语言**：TypeScript（推荐）或 Python
- **传输**：可流式 HTTP（远程）或 stdio（本地）
- **验证**：Zod（TypeScript）或 Pydantic（Python）

#### TypeScript 实现

```typescript
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio/index.js";
import { CallToolRequestSchema, ListToolsRequestSchema } from "@modelcontextprotocol/sdk/types.js";
import { z } from "zod";

// 定义工具输入模式
const WeatherInputSchema = z.object({
  city: z.string().describe("城市名称"),
  country: z.string().optional().describe("国家代码（可选）")
});

// 创建服务器
const server = new Server({
  name: "weather-server",
  version: "1.0.0",
}, {
  capabilities: {
    tools: {},
  },
  tools: {
    get_weather: {
      description: "获取指定城市的当前天气",
      inputSchema: WeatherInputSchema,
    },
  },
});

// 注册工具处理器
server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;

  if (name === "get_weather") {
    const { city, country } = WeatherInputSchema.parse(args);

    // 调用天气 API
    const weather = await fetchWeather(city, country);

    return {
      content: [{
        type: "text",
        text: JSON.stringify(weather, null, 2)
      }]
    };
  }

  throw new Error(`未知工具：${name}`);
});

// 启动服务器
const transport = new StdioServerTransport();
await server.connect(transport);
```

**工具示例**：

```typescript
// 列出仓库
list_repositories: {
  description: "列出指定组织的所有 GitHub 仓库",
  inputSchema: z.object({
    org: z.string().describe("GitHub 组织名称"),
    limit: z.number().optional().default(30).describe("返回的最大仓库数")
  }),
},

// 获取仓库详情
get_repository: {
  description: "获取指定仓库的详细信息",
  inputSchema: z.object({
    owner: z.string().describe("仓库所有者"),
    repo: z.string().describe("仓库名称")
  }),
},

// 创建 Issue
create_issue: {
  description: "在指定仓库创建新的 issue",
  inputSchema: z.object({
    owner: z.string().describe("仓库所有者"),
    repo: z.string().describe("仓库名称"),
    title: z.string().describe("Issue 标题"),
    body: z.string().optional().describe("Issue 内容")
  }),
},
```

#### Python 实现

```python
from mcp.server.fastmcp import FastMCP
from mcp.server.stdio import stdio_server
from pydantic import BaseModel

# 定义输入模型
class WeatherInput(BaseModel):
    city: str
    country: str | None = None

# 创建服务器
mcp = FastMCP("weather-server", "1.0.0")

@mcp.tool()
async def get_weather(city: str, country: str | None = None) -> str:
    """获取指定城市的当前天气"""
    # 调用天气 API
    weather = await fetch_weather(city, country)
    return str(weather)

# 启动服务器
async def main():
    async with stdio_server() as (read_stream, write_stream):
        await mcp.run(
            read_stream,
            write_stream,
            mcp.create_initialization_options()
        )

if __name__ == "__main__":
    import asyncio
    asyncio.run(main())
```

#### 第 3 阶段：审查和测试

**代码质量检查**：
- [ ] 无重复代码（DRY 原则）
- [ ] 一致的错误处理
- [ ] 完整的类型覆盖
- [ ] 清晰的工具描述

**构建和测试**：

```bash
# TypeScript
npm run build
npx @modelcontextprotocol/inspector

# Python
python -m py_compile your_server.py
npx @modelcontextprotocol/inspector
```

#### 第 4 阶段：创建评估

**评估文件格式**：

```xml
<evaluation>
  <qa_pair>
    <question>查找关于具有动物代号的 AI 模型发布的讨论。一个模型需要使用 ASL-X 格式的特定安全指定。以斑纹野生猫命名的模型正在确定的数字 X 是多少？</question>
    <answer>3</answer>
  </qa_pair>
  <qa_pair>
    <question>列出所有可用的 GitHub 仓库，按星数降序排列。</question>
    <answer>claude-code, anthropic/anthropic-quickstart, ...</answer>
  </qa_pair>
  <!-- 更多问题... -->
</evaluation>
```

**评估要求**：
- **独立**：不依赖于其他问题
- **只读**：仅需要非破坏性操作
- **复杂**：需要多个工具调用
- **现实**：基于真实用例
- **可验证**：单一、清晰的答案

### 12.3 最佳实践

| 原则 | 说明 |
|------|------|
| **简洁工具描述** | 清晰的功能摘要 |
| **输入验证** | 使用 Zod/Pydantic 验证输入 |
| **错误处理** | 可操作的错误消息 |
| **分页支持** | 支持过滤和分页 |
| **工具注释** | readOnlyHint, destructiveHint |

---

## 13. skill-creator - 技能创建器

**skill-creator** 是用于创建有效技能的指南。

### 13.1 技能概述

**什么是技能？**

技能是模块化、自包含的软件包，通过提供专业知识、工作流程和工具来扩展 Claude 的能力。

**核心原则**：
- **简洁是关键**：上下文窗口是公共资源
- **适当的自由度**：高/中/低，取决于任务类型
- **渐进式披露**：元数据 → SKILL.md 正文 → 打包资源

### 13.2 技能结构

```
skill-name/
├── SKILL.md (必需)
│   ├── YAML 前置元数据
│   │   ├── name: (必需)
│   │   └── description: (必需)
│   └── Markdown 说明 (必需)
├── scripts/ (可选)
├── references/ (可选)
└── assets/ (可选)
```

### 13.3 技能剖析

#### SKILL.md（必需）

**YAML 前置元数据**：

```markdown
---
name: my-custom-skill
description: 清晰描述技能的作用和使用场景
---
```

- `name`：技能的唯一标识符（小写，连字符分隔）
- `description`：技能描述，Claude 用此判断何时使用该技能

**Markdown 正文**：
- 使用该技能的说明和指导
- 仅在技能触发后加载

#### scripts/（可选）

可执行代码（Python/Bash/等）：
- **何时包含**：当同一代码被反复重写时
- **好处**：节省 token、确定性
- **注意**：脚本可能需要由 Claude 读取进行补丁

#### references/（可选）

文档和参考资料：
- **何时包含**：Claude 工作时应该参考的文档
- **示例**：API 文档、领域知识、公司政策
- **好处**：保持 SKILL.md 精简

#### assets/（可选）

输出中使用的文件：
- **何时包含**：技能需要在最终输出中使用的文件
- **示例**：模板、图像、图标、字体
- **好处**：将输出资源与文档分离

### 13.4 自由度设置

**高自由度（基于文本的指令）**：
- 多种方法都有效
- 决策取决于上下文
- 启发式方法指导

**中等自由度（伪代码或带参数的脚本）**：
- 存在首选模式
- 某些变体可接受
- 配置影响行为

**低自由度（特定脚本、少量参数）**：
- 操作脆弱且容易出错
- 一致性至关重要
- 必须遵循特定顺序

### 13.5 创建技能流程

**步骤 1：通过具体示例理解技能**

问自己：
- "这个技能应该支持什么功能？"
- "你能举一些如何使用这个技能的例子吗？"
- "用户会说什么来触发这个技能？"

**步骤 2：规划可重用的技能内容**

分析每个示例：
1. 考虑如何从头开始执行
2. 确定可重用的脚本、参考资料、资产

**步骤 3：初始化技能**

```bash
scripts/init_skill.py <skill-name> --path <output-directory>
```

**步骤 4：编辑技能**

- 从可重用资源开始
- 测试脚本（必须实际运行）
- 更新 SKILL.md

**步骤 5：打包技能**

```bash
scripts/package_skill.py <path/to/skill-folder>
```

### 13.6 示例技能

```markdown
---
name: code-reviewer
description: 执行 Python 代码审查，检查代码质量、安全问题和性能优化机会
---

# 代码审查技能

## 审查标准

1. **代码质量**
   - 遵循 PEP 8 规范
   - 有意义的变量和函数名
   - 适当的注释

2. **安全问题**
   - SQL 注入风险
   - 硬编码的密钥
   - 不安全的函数使用

3. **性能优化**
   - 算法复杂度
   - 资源使用效率
   - 可优化的代码模式

## 输出格式

```markdown
## 代码审查结果

### 整体评价
[评分：优秀/良好/需改进]

### 发现的问题
1. [问题描述]
   - 位置：[行号]
   - 建议：[改进建议]

### 亮点
[代码中的优秀实践]
```
```

---

## 14. webapp-testing - Web 应用测试

**webapp-testing** 是使用 Playwright 测试本地 Web 应用的工具包。

### 14.1 技能概述

**什么是 Web 应用测试？**

使用 Playwright 编写原生 Python 测试脚本来验证前端功能、调试 UI 行为、捕获浏览器截图和查看浏览器日志。

**核心功能**：
- 侦察-然后-行动模式
- 服务器生命周期管理
- DOM 检查、元素发现
- 控制台日志捕获

### 14.2 决策树

```
用户任务 → 是静态 HTML 吗？
    ├─ 是 → 直接读取 HTML 文件以识别选择器
    │         ├─ 成功 → 使用选择器编写 Playwright 脚本
    │         └─ 失败/不完整 → 视为动态（见下文）
    │
    └─ 否（动态 webapp）→ 服务器是否已在运行？
        ├─ 否 → 运行：python scripts/with_server.py --help
        │         然后使用辅助程序 + 编写简化的 Playwright 脚本
        │
        └─ 是 → 侦察然后行动：
            1. 导航并等待 networkidle
            2. 截图或检查 DOM
            3. 从渲染状态识别选择器
            4. 使用发现的选择器执行操作
```

### 14.3 使用 with_server.py

**单个服务器**：

```bash
python scripts/with_server.py \
  --server "npm run dev" \
  --port 5173 \
  -- python your_automation.py
```

**多个服务器（后端 + 前端）**：

```bash
python scripts/with_server.py \
  --server "cd backend && python server.py" --port 3000 \
  --server "cd frontend && npm run dev" --port 5173 \
  -- python your_automation.py
```

**测试脚本**：

```python
from playwright.sync_api import sync_playwright

with sync_playwright() as p:
    # 始终在无头模式下启动 chromium
    browser = p.chromium.launch(headless=True)
    page = browser.new_page()

    # 服务器已在运行并就绪
    page.goto('http://localhost:5173')

    # 关键：等待 JS 执行
    page.wait_for_load_state('networkidle')

    # 测试逻辑
    title = page.title()
    print(f"页面标题：{title}")

    # 截图
    page.screenshot(path='screenshot.png')

    browser.close()
```

### 14.4 侦察然后行动模式

**步骤 1：检查渲染的 DOM**

```python
page.screenshot(path='/tmp/inspect.png', full_page=True)
content = page.content()
elements = page.locator('button').all()

print(f"找到 {len(elements)} 个按钮")
```

**步骤 2：从检查结果中识别选择器**

**步骤 3：使用发现的选择器执行操作**

```python
# 使用描述性选择器
page.locator('text="提交"]').click()
page.locator('role="button", name="登录"]').click()
page.locator('#username-input').fill('testuser')
```

### 14.5 最佳实践

| 最佳实践 | 说明 |
|---------|------|
| **sync_playwright()** | 使用同步函数编写脚本 |
| **关闭浏览器** | 完成后始终关闭浏览器 |
| **等待 networkidle** | 等待 JS 执行完成 |
| **描述性选择器** | 使用 text=、role=、CSS 选择器或 ID |
| **适当等待** | 添加 page.wait_for_selector() 或 wait_for_timeout() |

### 14.6 实战示例

```python
from playwright.sync_api import sync_playwright

def test_todo_app():
    """测试待办事项应用"""
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        page = browser.new_page()

        # 导航到应用
        page.goto('file:///D:/path/to/todo-app.html')
        page.wait_for_load_state('networkidle')

        # 测试添加任务
        print("测试添加任务功能...")
        page.fill('#taskInput', '学习 Agent Skills')
        page.click('button')
        page.wait_for_timeout(500)

        # 验证任务已添加
        task = page.locator('.todo-item').last
        text = task.inner_text()
        assert '学习 Agent Skills' in text
        print("✅ 任务添加成功")

        # 测试完成任务
        print("测试完成任务功能...")
        checkbox = task.locator('input[type="checkbox"]')
        checkbox.check()
        page.wait_for_timeout(200)

        span = task.locator('span')
        style = span.get_attribute('style')
        assert 'line-through' in style
        print("✅ 任务完成成功")

        # 截图
        page.screenshot(path='test_result.png')
        print("✅ 截图已保存")

        browser.close()

if __name__ == '__main__':
    test_todo_app()
```

---

## 15. web-artifacts-builder - Web 工件构建

**web-artifacts-builder** 是使用现代前端技术创建复杂 HTML 工件的技能。

### 15.1 技能概述

**什么是 Web 工件构建？**

使用 React + TypeScript + Vite + Tailwind CSS + shadcn/ui 创建复杂的 claude.ai HTML 工件。

**技术栈**：
- React 18
- TypeScript
- Vite
- Tailwind CSS 3.4.1
- shadcn/ui
- Parcel（打包）

### 15.2 快速开始

**步骤 1：初始化项目**

```bash
bash scripts/init-artifact.sh <project-name>
cd <project-name>
```

这将创建：
- ✅ React + TypeScript（通过 Vite）
- ✅ Tailwind CSS 和 shadcn/ui
- ✅ 配置的路径别名（`@/`）
- ✅ 预装 40+ 个 shadcn/ui 组件
- ✅ 配置的 Parcel（用于打包）

**步骤 2：开发工件**

编辑生成的文件 `src/App.tsx`：

```tsx
import React, { useState, useEffect } from 'react';
import { Button } from '@/components/ui/button';
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from '@/components/ui/card';

function App() {
  const [count, setCount] = useState(0);

  return (
    <div className="min-h-screen bg-gradient-to-br from-slate-900 to-slate-800 p-8">
      <Card className="max-w-md mx-auto">
        <CardHeader>
          <CardTitle>计数器</CardTitle>
          <CardDescription>点击按钮增加计数</CardDescription>
        </CardHeader>
        <CardContent>
          <div className="text-4xl font-bold text-center mb-4 text-orange-400">
            {count}
          </div>
          <Button
            onClick={() => setCount(c => c + 1)}
            className="w-full"
          >
            增加
          </Button>
        </CardContent>
      </Card>
    </div>
  );
}

export default App;
```

**步骤 3：打包为单个 HTML 文件**

```bash
bash scripts/bundle-artifact.sh
```

这将创建 `bundle.html`，一个自包含的工件。

**步骤 4：与用户共享工件**

在对话中分享打包的 HTML 文件。

### 15.3 设计指南

**避免"AI 渣滓"**：
- ❌ 过度使用的居中布局
- ❌ 紫色渐变
- ❌ 统一的圆角
- ❌ Inter 字体

**推荐做法**：
- ✅ 独特的字体配对
- ✅ 大胆的调色板
- ✅ 不对称布局
- ✅ 有趣的动画效果

### 15.4 实战示例

```tsx
import React, { useState } from 'react';
import { Button } from '@/components/ui/button';
import { Card, CardContent, CardHeader, CardTitle } from '@/components/ui/card';
import { Tabs, TabsContent, TabsList, TabsTrigger } from '@/components/ui/tabs';

interface Feature {
  id: string;
  title: string;
  description: string;
  icon: string;
}

const features: Feature[] = [
  { id: '1', title: '智能分析', description: '自动分析数据并提供洞察', icon: '🎯' },
  { id: '2', title: '实时同步', description: '多设备实时数据同步', icon: '⚡' },
  { id: '3', title: '安全可靠', description: '企业级安全保障',', icon: '🔒' },
  { id: '4', title: '易于集成', description: '简单的 API 集成', icon: '🔗' },
];

function Dashboard() {
  const [activeTab, setActiveTab] = useState('features');

  return (
    <div className="min-h-screen bg-gradient-to-br from-indigo-900 via-purple-900 to-pink-800 p-8">
      <div className="max-w-5xl mx-auto">
        {/* 标题 */}
        <div className="text-center mb-12">
          <h1 className="text-6xl font-bold text-white mb-4">
            产品仪表板
          </h1>
          <p className="text-xl text-purple-200">
            查看关键指标和功能概览
          </p>
        </div>

        {/* 标签页 */}
        <Tabs value={activeTab} onValueChange={setActiveTab}>
          <TabsList className="grid w-full grid-cols-2 gap-4 mb-8">
            <TabsTrigger value="features" className="text-lg">
              功能概览
            </TabsTrigger>
            <TabsTrigger value="metrics" className="text-lg">
              数据指标
            </TabsTrigger>
          </TabsList>

          <TabsContent value="features" className="mt-4">
            <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
              {features.map((feature) => (
                <Card key={feature.id} className="bg-white/10 backdrop-blur">
                  <CardHeader>
                    <div className="text-4xl mb-2">{feature.icon}</div>
                    <CardTitle className="text-2xl">{feature.title}</CardTitle>
                    <CardDescription>{feature.description}</CardDescription>
                  </CardHeader>
                  <CardContent>
                    <Button variant="outline" className="w-full">
                      了解更多
                    </Button>
                  </CardContent>
                </Card>
              ))}
            </div>
          </TabsContent>

          <TabsContent value="metrics" className="mt-4">
            <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
              <Card className="bg-white/10 backdrop-blur">
                <CardHeader>
                  <CardTitle className="text-3xl text-blue-400">1,234</CardTitle>
                  <CardDescription>总用户数</CardDescription>
                </CardHeader>
              </Card>
              <Card className="bg-white/10 backdrop-blur">
                <CardHeader>
                  <CardTitle className="text-3xl text-green-400">89%</CardTitle>
                  <CardDescription>活跃用户</CardDescription>
                </CardHeader>
              </Card>
              <Card className="bg-white/10 backdrop-blur">
                <CardHeader>
                  <CardTitle className="text-3xl text-orange-400">456</CardTitle>
                  <CardDescription>今日访问</CardDescription>
                </CardHeader>
              </Card>
            </div>
          </TabsContent>
        </Tabs>
      </div>
    </div>
  );
}

export default Dashboard;
```

### 15.5 shadcn/ui 组件

**可用组件**（40+ 个预装）：

- Button
- Card
- Dialog/Modal
- Form 输入组件
- Table
- Tabs
- Select/Dropdown
- Checkbox
- Radio
- Switch
- Slider
- Toast
- Tooltip
- Badge
- Avatar
- Progress
- Skeleton
- Separator
- Scroll Area
- ... 等等

**使用参考**：https://ui.shadcn.com/docs/components

---

# 第五部分：沟通与主题类技能

## 16. doc-coauthoring - 文档协作工作流

**doc-coauthoring** 是一个引导用户通过文档协作创作的结构化工作流程的技能。

### 16.1 技能概述

**什么是文档协作工作流程？**

一个结构化的工作流程，通过三个阶段引导用户：
1. **上下文收集**：用户提供所有相关上下文
2. **完善与结构**：逐节头脑风暴、策展、并起草
3. **读者测试**：使用全新的 Claude 验证文档有效性

**触发条件**：
- 用户提到编写文档、提案、技术规范
- 用户提到创建决策文档、RFC
- 用户似乎在开始一项实质性的写作任务

### 16.2 工作流程详解

#### 第 1 阶段：上下文收集

**目标**：缩小用户知道的内容和 Claude 知道的内容之间的差距

**初始问题**：
1. 这是什么类型的文档？（例如，技术规范、决策文档、提案）
2. 主要受众是谁？
3. 人们在阅读时期望产生什么影响？
4. 是否有要遵循的模板或特定格式？
5. 还有哪些其他约束或上下文需要了解？

**信息倾倒提示**：
- 项目/问题的背景
- 相关的团队讨论或共享文档
- 为什么不使用替代解决方案
- 组织背景（团队动态、过去的事件、政治）
- 时间线压力或约束
- 技术架构或依赖关系
- 利益相关者的关注点

**提出澄清问题**：

根据上下文中的差距生成 5-10 个编号的问题：

```
让我基于您提供的信息提出一些澄清问题：

1. 关于技术架构，您是否需要我了解更多细节？
2. 有哪些替代方案被考虑过但最终被拒绝了？
3. 目标读者的技术背景如何？
4. 此文档的决策时间线是什么？
5. 有哪些利益相关者需要特别关注？
6. 有哪些约束或限制需要考虑？
7. 成功的标准是什么？
8. 有哪些风险需要识别和缓解？
9. 此文档的后续步骤是什么？
10. 有哪些参考资料或链接需要包含？

您可以用简写回答（如 "1: 是, 2: 见频道 X"），或者继续提供更多信息。
```

#### 第 2 阶段：完善与结构

**目标**：通过头脑风暴、策展和迭代完善逐节构建文档

**部分排序**：

如果文档结构清晰，建议从具有最多未知数的部分开始。对于决策文档，这通常是核心提案。

**如果有权访问 artifact**：

```
我将为所有部分创建一个初始文档结构。
```

使用 `create_file` 创建包含所有部分标题和占位符文本的制品。

**对于每个部分**：

**步骤 1：澄清问题**

```
现在我将开始处理 [部分名称] 部分。

请回答以下问题以帮助我理解应该包含什么：

1. 这个部分的主要目标是什么？
2. 有哪些关键点需要覆盖？
3. 有哪些数据或指标需要包括？
4. 有哪些图表或可视化会有帮助？
5. 这个部分的长度应该控制在什么范围内？
```

**步骤 2：头脑风暴**

```
对于 [部分名称] 部分，这里是可能包含的内容选项：

1. [选项 1]
2. [选项 2]
3. [选项 3]
...
10. [选项 10]

请告诉我哪些项目应该保留、删除或合并（如 "保留 1,4,7,9"）。
```

**步骤 3：差距检查**

```
根据您的选择，[部分名称] 部分是否缺少任何重要的内容？

例如：
- 是否缺少技术细节？
- 是否缺少示例？
- 是否缺少参考链接？
```

**步骤 4：起草**

使用 `str_replace` 将该部分的占位符文本替换为实际起草的内容。

**步骤 5：迭代完善**

当用户提供反馈时，使用 `str_replace` 进行编辑。

#### 第 3 阶段：读者测试

**目标**：使用全新的 Claude（无上下文泄漏）测试文档

**测试方法**：

**步骤 1：预测读者问题**

```
让我预测读者在尝试发现此文档时可能提出的问题：

1. [问题 1]
2. [问题 2]
...
5. [问题 5]
```

**步骤 2：使用子代理测试**

调用仅包含文档内容和问题的子代理。

**步骤 3：运行额外检查**

调用子代理检查歧义、错误假设、矛盾。

**步骤 4：报告和修复**

如果发现问题，报告并循环回到有问题的部分进行完善。

### 16.3 实战示例

**场景**：创建技术决策文档

**工作流程示例**：

```
用户: 我需要创建一个关于选择技术栈的决策文档

Claude: 好的，我可以帮您通过一个结构化的文档工作流程来创建这个决策文档。

这个工作流程包括三个阶段：
1. 上下文收集 - 您提供所有相关背景信息
2. 完善与结构 - 我们逐节构建文档
3. 读者测试 - 使用全新的视角验证文档有效性

您想尝试这个工作流程吗？

用户: 是的

Claude: 好的，让我们从上下文收集开始。

请告诉我：
1. 这是什么类型的决策文档？
2. 谁会是谁？
3. 有哪些技术选项需要评估？
4. 有哪些约束或限制？
5. 有哪些评估标准？

[用户回答...]

Claude: 好的，基于您的回答，让我提出一些澄清问题：

1. 当前的技术栈是什么？
2. 新的候选技术栈是什么？
3. 主要考虑因素是什么（性能、成本、团队熟悉度等）？
4. 这个决策的期望时间线是什么？

[用户提供更多信息...]

Claude: 我注意到您提到了团队的技术背景。这很重要。

我还有几个问题：
1. 团队目前最熟悉哪些技术？
2. 有哪些培训或迁移成本需要考虑？
3. 有哪些风险评估需要包含？

[用户回答...]

Claude: 很好，看起来我已经收集了足够的上下文。

现在进入第二阶段：完善与结构。

我建议文档包含以下部分：
1. 执行摘要
2. 背景
3. 技术选项评估
4. 决策依据
5. 实施计划
6. 风险和缓解

这个结构合适吗？还是您想调整？

用户: 合适，开始吧

Claude: 好的，我将创建一个初始文档结构。

[创建 artifact]

现在让我们逐部分完善。

首先，让我为"执行摘要"部分提出一些问题：

1. 这个决策的总体目标是什么？
2. 主要结论是什么？
3. 建议的下一步是什么？

[用户回答...]

[起草执行摘要部分]

继续其他部分...

[完成所有部分]

Claude: 文档已起草完成。现在进入第三阶段：读者测试。

我将预测读者可能会提出的问题：

1. 为什么选择这个技术栈而不是选项 X？
2. 这个决策如何影响现有项目？
3. 有哪些迁移计划？
4. 团队需要哪些培训？
5. 成本影响是什么？

让我使用一个全新的 Claude 实例来测试文档...

[测试并修复发现的问题]

Claude: 文档已通过读者测试！

最后建议：
1. 请自己通读一遍文档
2. 检查事实、链接和技术细节
3. 验证它是否实现了您想要的影响

文档已完成！
```

---

## 17. internal-comms - 内部沟通

**internal-comms** 是一个帮助使用公司喜欢的格式编写各种内部沟通的技能。

### 17.1 技能概述

**什么是内部沟通？**

一组资源，帮助使用公司喜欢的格式编写各种内部沟通。

**支持的沟通类型**：

| 类型 | 用途 |
|------|------|
| **3P 更新** | 进度、计划、问题团队更新 |
| **公司通讯** | 全公司公告 |
| **常见问题解答** | 回答常见问题 |
| **状态报告** | 定期状态汇报 |
| **领导更新** | 向领导汇报 |
| **项目更新** | 项目进展更新 |
| **事件报告** | 事件或事故报告 |

### 17.2 如何使用

**使用流程**：

1. 从请求中识别沟通类型
2. 从 `examples/` 目录加载适当的指南文件
3. 遵循该文件中的具体说明进行格式化、语气和内容收集

### 17.3 示例模板

#### 3P 更新模板

```
3P 团队更新 - [项目名称]

日期：[日期]

计划
-----
[接下来要完成的工作]
[时间线]

进展
-----
[已完成的工作]
[关键里程碑]

问题
-----
[当前遇到的障碍]
[需要帮助的地方]
```

#### 公司通讯模板

```
[公司名称] 通讯
[日期]

📢 重要公告
-------------------
[标题]

[主要内容]

📅 部门信息
-------------------
[联系人和方式]
```

#### 常见问题解答模板

```
常见问题解答

Q: [问题 1]
A: [答案 1]

Q: [问题 2]
A: [答案 2]
...
```

#### 状态报告模板

```
[周期] 状态报告
[负责人]

📊 亮点
-----
- [成就 1]
- [成就 2]

📊 指标
-----
| 指标 | 目标 | 当前 | 状态 |
|-------|------|------|------|
| [指标 1] | [值] | [值] | ✅/⚠️ |
| [指标 2] | [值] | [值] | ✅/⚠️ |

📊 风险和问题
-----
- [风险 1]
- [问题 1]
```

### 17.4 实战示例

**示例 1：3P 更新**

```
Claude: 我注意到您想要提供团队更新。让我帮您创建一个结构化的 3P 更新。

请提供以下信息：
1. 项目名称是什么？
2. 本周期的计划是什么？
3. 进展如何？
4. 有哪些问题或障碍？

用户输入:

3P 团队更新 - 用户管理系统重构

日期：2024年3月18日

计划
-----
• 完成后端 API 重构
• 实现前端状态管理
• 集成新的认证系统
• 执行性能优化

时间线：预计 4 周内完成

进展
-----
✅ 后端 API 重构已完成 80%
✅ 前端状态管理已实现
✅ 认证系统集成测试中
⏳ 性能优化待开始

关键里程碑：后端 API v2 已上线

问题
-----
⚠️ 第三方 API 响应不稳定，影响集成测试
⚠️ 需要额外的测试服务器资源
```

**示例 2：公司通讯**

```
Claude: 我可以帮您创建一份公司通讯。

请提供：
1. 通讯的标题是什么？
2. 主要内容是什么？
3. 有哪些行动项需要大家注意？

用户输入:

🚀 ABC 公司重要公告 🚀

日期：2024年3月15日

📢 新产品发布通知
-------------------
我们很高兴地宣布，经过 6 个月的开发，我们的新产品 "AI Assistant Pro" 将于下周正式发布！

这是一个重大的里程碑，它将极大地提升我们客户的工作效率。

📢 主要功能
-------------------------
• 智能对话理解
• 多语言支持
• 企业级安全
• API 集成

📢 下一步行动
-------------------------
1. 产品团队：准备发布材料
2. 销售团队：完成客户培训
3. 客服团队的：熟悉新功能

📢 联系方式
-------------------------
如有任何问题，请联系：
产品团队负责人：张三
邮箱：zhangsan@example.com
```

---

## 18. theme-factory - 主题工厂

**theme-factory** 是一个为工件设置样式的工具包。

### 18.1 技能概述

**什么是主题工厂？**

提供 10 个精心策划的专业字体和颜色主题，可以应用于幻灯片、文档、报告、HTML 落陆页等任何工件。

**10 个预设主题**：

| 主题名称 | 风格描述 | 主色 | 适用场景 |
|---------|---------|------|---------|
| **Ocean Depths** | 专业海洋 | 深海海军蓝 | 企业演示、财务报告 |
| **Sunset Boulevard** | 温暖日落 | 焦橙色、珊瑚色 | 创意推介、营销演示 |
| **Forest Canopy** | 自然大地 | 森林绿、鼠尾草绿 | 环境演示、可持续发展 |
| **Modern Minimalist** | 干净灰度 | 炭灰、石板灰 | 技术演示、建筑作品集 |
| **Golden Hour** | 秋季温暖 | 芥末黄、赤陶色 | 餐厅演示、酒店品牌 |
| **Arctic Frost** | 冬季凉爽 | 冰蓝、钢蓝 | 医疗保健、技术解决方案 |
| **Desert Rose** | 柔和精致 | 尘土玫瑰、粘土色 | 时尚演示、美容品牌 |
| **Tech Innovation** | 大胆技术 | 电光蓝、霓虹青 | 科技初创公司、软件发布 |
| **Botanical Garden** | 新鲜花园 | 蕨类绿、万寿菊 | 花园中心、天然产品 |
| **Midnight Galaxy** | 宇宙戏剧 | 深紫、宇宙蓝 | 娱乐行业、游戏演示 |

### 18.2 使用流程

**步骤 1：显示主题展示**

显示 `theme-showcase.pdf` 文件，让用户直观地查看所有可用主题。

**步骤 2：询问选择**

询问用户想要应用哪个主题。

**步骤 3：等待确认**

获得对所选主题的明确确认。

**步骤 4：应用主题**

选择主题后，将所选主题的颜色和字体应用于幻灯片组/工件。

### 18.3 主题详细规范

#### Ocean Depths

```
主色：#1A2D4E（深海海军蓝）
辅助色：#2C5F70（海洋绿）
强调色：#E9F4A6（海洋蓝）
标题字体：Poppins
正文字体：Lora
```

#### Sunset Boulevard

```
主色：#D35400（焦橙色）
辅助色：#E96B54（珊瑚色）
强调色：#FFB74D（橙黄色）
标题字体：Playfair Display
正文字体：Montserrat
```

#### Forest Canopy

```
主色：#2C5F2D（森林绿）
辅助色：#97BC62（苔藓绿）
强调色：#F5F5F5（奶油色）
标题字体：Merriweather
正文字体：Open Sans
```

#### Modern Minimalist

```
主色：#36454F（炭黑）
辅助色：#F2F2F2（灰白色）
强调色：#212121（黑色）
标题字体：Inter
正文字体：IBM Plex Sans
```

#### Golden Hour

```
主色：#D4A017（芥末黄）
辅助色：#C99550（赤陶色）
强调色：#F4D03F（赭石色）
标题字体：Cormorant Garamond
正文字体：Source Sans Pro
```

#### Arctic Frost

```
主色：#1E4A6E（冰蓝）
辅助色：#6A9CBD（钢蓝）
强调色：#2196F3（天蓝色）
标题字体：Montserrat
正文字体：Lato
```

#### Desert Rose

```
主色：#B85042（尘土玫瑰）
辅助色：#E7E8D1（沙色）
强调色：#A7BEAE（鼠尾草）
标题字体：Georgia
正文字体：Verdana
```

#### Tech Innovation

```
主色：#0052D4（深蓝）
辅助色：#00A896（青色）
强调色：#02C39A（薄荷色）
标题字体：Oswald
正文字体：Roboto
```

#### Botanical Garden

```
主色：#3A6B44（蕨类绿）
辅助色：#8FBC8F（万寿菊）
强调色：#50808E（板岩色）
标题字体：Palatino
正文字体：Helvetica Neue
```

#### Midnight Galaxy

```
主色：#1A1A2E（深紫）
辅助色：#4A4A75（A2 紫）
强调色：#6B4A7E（星云紫）
标题字体：Raleway
正文字体：Ubuntu
```

### 18.4 应用示例

#### PowerPoint 应用

```javascript
const pptxgenjs = require('pptxgenjs');

// 选择 Ocean Depths 主题
const oceanDepths = {
  primary: '#1A2D4E',
  secondary: '#2C5F70',
  accent: '#E9F4A6',
  titleFont: 'Poppins',
  bodyFont: 'Lora'
};

const pres = new pptxgenjs();

pres.addSlide({
  title: '项目报告',
  background: { color: oceanDepths.primary },
  objects: [
    {
      text: '项目进展',
      options: {
        color: '#FFFFFF',
        fontSize: 36,
        fontFace: oceanDepths.titleFont
      }
    }
  ]
});

pres.writeFile({ fileName: 'themed-presentation.pptx' });
```

#### CSS 应用

```css
:root {
  --theme-primary: #1A2D4E;
  --theme-secondary: #2C5F70;
  --theme-accent: #E9F4A6;
  --theme-font-title: 'Poppins', Arial, sans-serif;
  --theme-font-body: 'Lora', Georgia, serif;
}

body {
  color: var(--theme-primary);
  background-color: var(--theme-secondary);
  font-family: var(--theme-font-body);
}

h1, h2, h3 {
  font-family: var(--theme-font-title);
}
```

---

## 19. slack-gif-creator - Slack GIF 创建器

**slack-gif-creator** 是一个创建为 Slack 优化的动画 GIF 的技能。

### 19.1 技能概述

**什么是 Slack GIF 创建器？**

一个工具包，提供创建为 Slack 优化的动画 GIF 的实用程序和知识。

**Slack 要求**：

| 参数 | 值值 |
|------|------|
| **尺寸** | 表情符号 GIF：128x128<br>消息 GIF：480x480 |
| **FPS** | 10-30（越低文件越小） |
| **颜色** | 48-128（越少文件越小） |
| **持续时间** | 表情符号 GIF：<3 秒 |

### 19.2 核心工作流程

```python
from core.gif_builder import GIFBuilder
from PIL import Image, ImageDraw

# 1. 创建构建器
builder = GIFBuilder(width=128, height=128, fps=10)

# 2. 生成帧
for i in range(12):
    frame = Image.new('RGB', (128, 128), (240, 248, 255))
    draw = ImageDraw.Draw(frame)

    # 绘制动画内容
    # ...

    builder.add_frame(frame)

# 3. 保存并优化
builder.save('output.gif', num_colors=48, optimize_for_emoji=True)
```

### 19.3 动画概念

#### 摇动/振动

```python
import math

t = i / (num_frames - 1)
offset_x = math.sin(t * 2 * math.pi) * 10
offset_y = math.cos(t * 2 * math.pi) * 5
```

#### 脉冲/心跳

```python
import math

t = i / (num_frames - 1)
# 两次快速脉冲然后暂停
pulse = math.sin(t * 4 * math.pi) if t < 0.5 else 0
scale = base_scale * (1 + pulse * 0.3)
```

#### 弹跳

```python
from core.easing import interpolate

# 下落：加速
y_down = interpolate(start=0, end=height, t=t_drop, easing='ease_in')

# 着陆：弹跳
y_bounce = interpolate(start=height, end=0, t=t_bounce, easing='bounce_out')
```

#### 旋转/自转

```python
angle = i * 360 / num_frames
rotated_image = image.rotate(angle, resample=Image.BICUBIC)
```

#### 淡入/淡出

```python
alpha = int(255 * (i / (num_frames - 1)))
image_with_alpha = image.copy()
image_with_alpha.putalpha(alpha_channel)
```

### 19.4 优化策略

**当需要小文件时**：

```python
# 表情符号最大优化
builder.save(
    'emoji.gif',
    num_colors=48,        # 更少的颜色
    optimize_for_emoji=True, # 自动优化
    remove_duplicates=True  # 删除重复帧
)
```

| 策略 | 效果 |
|------|------|
| 更少的帧 | 降低 FPS 或缩短持续时间 |
| 更少的颜色 | 48 vs 128 |
| 更小的尺寸 | 128x128 vs 480x480 |
| 删除重复帧 | 移除相同帧 |

### 19.5 实战示例

#### 示例 1：摇动对勾标记

```python
from PIL import Image, ImageDraw
from core.gif_builder import GIFBuilder

def create_checkmark():
    """创建摇动的对勾标记 GIF"""
    width, height = 128, 128
    builder = GIFBuilder(width=width, height=height, fps=15)

    for i in range(20):
        frame = Image.new('RGBA', (width, height), (0, 0, 0, 0))
        draw = ImageDraw.Draw(frame)

        # 计算摇动角度
        angle = math.sin(i / 19 * math.pi * 2) * 15

        # 绘制对勾
        check_x = width // 2
        check_y = height // 2 + int(angle)

        # 对勾标记
        draw.polygon([
            (check_x - 20, check_y),
            (check_x, check_y + 20),
            (check_x - 15, check_y + 20),
            (check_x - 15, check_y + 40),
            (check_x - 25, check_y + 40),
            (check_x - 25, check_y + 20),
        ], fill=(46, 204, 113, 255))

        builder.add_frame(frame)

    builder.save('checkmark.gif', num_colors=32, optimize_for_emoji=True)
    print("✅ 对勾标记 GIF 已创建")

if __name__ == '__main__':
    create_checkmark()
```

#### 示例 2：脉动爱心

```python
from PIL import Image, ImageDraw
from core.gif_builder import GIFBuilder
import math

def create_heart():
    """创建脉动爱心 GIF"""
    width, height = 128, 128
    builder = GIFBuilder(width=width, height=height, fps=20)

    # 心形绘制函数
    def draw_heart(draw, x, y, size):
        draw.ellipse([x-size, y-size, x+size, y+size*1.2], fill=(255, 107, 107))
        draw.ellipse([x+size, y-size, x+size*2, y+size*1.2], fill=(255, 107, 107))
        draw.polygon([
            (x-size*2, y),
            (x, y+size*3),
            (x+size*2, y)
        ], fill=(255, 255, 255))
        draw.ellipse([x-size*2, y-size*1.5, x+size*2, y+size*1.5], fill=(255, 107, 107))
        draw.ellipse([x, y+size*1.5, x+size*2, y+size*1.5], fill=(255, 107, 107))

    for i in range(20):
        frame = Image.new('RGBA', (width, height), (0, 0, 0, 0))
        draw = ImageDraw.Draw(frame)

        # 脉冲效果：两次快速脉冲
        t = i / 19
        if t < 0.5:
            pulse = math.sin(t * 4 * math.pi)
        else:
            pulse = 0

        scale = 40 + pulse * 15

        # 绘制脉动爱心
        draw_heart(draw, width//2, height//2, scale)

        builder.add_frame(frame)

    builder.save('heart.gif', num_colors=48, optimize_for_emoji=True)
    print("✅ 爱心 GIF 已创建")

if __name__ == '__main__':
    create_heart()
```

#### 示例 3：旋转箭头

```python
from PIL import Image, ImageDraw
from core.gif_builder import GIFBuilder

def create_arrow():
    """创建旋转箭头 GIF"""
    width, height = 128, 128
    builder = GIFBuilder(width=width, height=height, fps=20)

    for i in range(24):
        frame = Image.new('RGBA', (width, height), (0, 0, 0, 0))
        draw = ImageDraw.Draw(frame)

        # 计算旋转角度
        angle = i * 360 / 24

        # 绘制箭头
        center_x, center_y = width // 2, height // 2

        # 箭身
        arrow_length = 40
        end_x = center_x + arrow_length * math.cos(math.radians(angle))
        end_y = center_y - arrow_length * math.sin(math.radians(angle))

        draw.line([center_x, center_y, end_x, end_y], fill=(79, 172, 135), width=8)

        # 箭头
        head_size = 20
        angle1 = angle + 150
        angle2 = angle - 150
        head_x1 = end_x + head_size * math.cos(math.radians(angle1))
        head_y1 = end_y - head_size * math.sin(math.radians(angle1))
        head_x2 = end_x + head_size * math.cos(math.radians(angle2))
        head_y2 = end_y - head_size * math.sin(math.radians(angle2))

        draw.polygon([end_x, end_y, head_x1, head_y1, head_x2, head_y2], fill=(79, 172, 135))

        builder.add_frame(frame)

    builder.save('arrow.gif', num_colors=48, optimize_for_emoji=True)
    print("✅ 箭头 GIF 已创建")

if __name__ == '__main__':
    import math
    create_arrow()
```

---

# 第六部分：高级用法

## 20. 技能组合使用案例

### 20.1 概述

多个技能可以组合使用来完成复杂任务。以下是一些常见的组合模式：

| 组合 | 使用场景 | 技能 |
|------|---------|------|
| **pptx + theme-factory** | 创建主题化演示文稿 | 应用品牌样式 |
| **docx + brand-guidelines** | 创建品牌化文档 | 应用品牌样式 |
| **webapp-testing + docx** | 测试应用并生成报告 | 测试 + 文档输出 |
| **algorithmic-art + frontend-design** | 创建交互式艺术网站 | 生成艺术 + Web 封装 |
| **mcp-builder + skill-creator** | 创建技能的 MCP 集成 | 开发工具 |

### 20.2 案例 1：测试 Web 应用并生成报告

**场景**：测试待办事项应用并生成测试报告 Word 文档

**工作流程**：

```
步骤 1: webapp-testing 技能
    ↓
生成测试脚本并执行测试
    ↓
步骤 2: 收集测试结果
    ↓
步骤 3: docx 技能
    ↓
生成格式化测试报告 Word 文档
```

**实施示例**：

```bash
# 在 Claude 中请求
使用 webapp-testing 技能测试 todo-app.html，然后使用 docx 技能根据测试结果生成一份测试报告 Word 文档。

测试报告需要包含：
- 测试概述
- 测试用例和结果（表格）
- 缺陷列表
- 测试截图
- 建议和结论
```

**预期输出**：

```
outputs/
├── test_scripts/           # 测试脚本
├── screenshots/            # 测试截图
└── 测试报告.docx          # 最终报告
```

### 20.3 案例 2：创建主题化演示文稿

**场景**：使用 Ocean Depths 主题创建产品推介演示

**工作流程**：

```
步骤 1: pptx 技能
    ↓
创建演示文稿内容
    ↓
步骤 2: theme-factory 技能
    ↓
应用 Ocean Depths 主题
    ↓
步骤 3: 保存主题化演示
```

**实施示例**：

```bash
# 在 Claude 中请求
使用 pptx 技能创建产品推介演示，然后使用 theme-factory 技能应用 Ocean Depths 主题。

演示内容：
- 标题页：产品名称 + 副标
- 产品特性页：4-5 个核心特性
- 市场数据页：图表和统计
- 定价页：价格方案
- 结束页：联系方式
```

### 20.4 案例 3：文档协作与品牌样式

**场景**：使用 doc-coauthoring 工作流创建决策文档，应用 brand-guidelines 样式

**工作流程**：

```
步骤 1: doc-coauthoring 工作流
    ↓
上下文收集 → 完善与结构 → 读者测试
    ↓
步骤 2: brand-guidelines 技能
    ↓
应用 Anthropic 品牌样式
    ↓
步骤 3: 保存品牌化文档
```

### 20.5 技能组合技巧

#### 串行调用

```bash
# 明确串行调用多个技能
使用 webapp-testing 技能测试应用，然后使用 pptx 技能创建演示，最后使用 theme-factory 技能应用主题。
```

#### 数据传递

```bash
# 第一个技能的输出传递给下一个技能
使用 webapp-testing 技能测试应用并将结果保存到 test_results.json，然后使用 pptx 技能读取 test_results.json 并创建报告。
```

#### 上下文保持

```bash
# 在单次请求中保持上下文
我需要完成以下任务：
1. 使用 algorithmic-art 创建一个生成艺术作品
2. 使用 frontend-design 为它创建展示页面
3. 将两者整合为一个完整的 Web 应用

请从算法艺术开始，然后我将创建前端界面。
```

---

## 21. 创建自定义技能完整教程

### 21.1 概述

本教程将指导您从零开始创建一个完整的自定义技能。

### 21.2 创建技能流程

**步骤 1：规划技能**

确定以下要素：

| 要素 | 问题 | 示例答案 |
|------|------|---------|
| **技能名称** | 技能叫什么？ | `expense-tracker` |
| **目的** | 技能解决什么问题？ | 追踪和报告费用 |
| **触发条件** | 用户何时使用？ | 提到"费用"、"报销"时 |
| **输出格式** | 输出什么格式？ | Excel 电子表格 |

**步骤 2：使用 skill-creator 初始化**

```bash
# 使用 skill-creator 技能初始化
使用 skill-creator 技能帮我创建一个费用跟踪技能。

这个技能应该：
- 帮助用户记录日常费用
- 生成月度费用报告
- 支持费用分类（交通、餐饮、办公等）
- 输出 Excel 格式的报告
```

**步骤 3：完善技能结构**

```
expense-tracker/
├── SKILL.md
├── scripts/
│   └── generate_report.py
└── references/
    └── expense_categories.md
```

**SKILL.md 内容**：

```markdown
---
name: expense-tracker
description: 帮助用户记录和跟踪费用，生成月度费用报告。当用户提到"费用"、"报销"、"记账"时使用。
---

# 费用跟踪技能

此技能帮助您：
1. 记录日常费用
2. 按类别组织费用
3. 生成月度费用报告
4. 导出 Excel 格式

## 快速开始

### 记录新费用

请提供以下信息：
- 日期
- 费用金额
- 费用类别
- 描述（可选）

### 生成报告

生成报告需要以下信息：
- 报告月份
- 报告标题
- 是否需要图表

## 费用分类

参见 [费用分类参考](scripts/expense_categories.md) 了解完整的分类系统。

## 生成报告

使用 `scripts/generate_report.py` 生成 Excel 格式的报告。
```

**scripts/generate_report.py 内容**：

```python
import openpyxl
from openpyxl.styles import Font, PatternFill, Alignment
from openpyxl.utils import get_column_letter
from datetime import datetime
import pandas as pd

def generate_report(data, output_file="expense_report.xlsx"):
    """
    生成费用报告 Excel 文件

    Args:
        data: 费用数据列表
        output_file: 输出文件名
    """
    # 创建工作簿
    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = "费用报告"

    # 标题
    ws.merge_cells('A1:E1')
    ws['A1'] = "费用报告"
    ws['A1'].font = Font(bold=True, size=16, color="2D3748")
    ws['A1'].alignment = Alignment(horizontal='center')

    ws['A2'] = "报告日期"
    ws['A2'].font = Font(size=12)
    ws['B2'] = datetime.now().strftime("%Y年%m月%d日")
    ws['B2'].font = Font(size=12)

    # 表头
    headers = ["日期", "类别", "金额", "描述", "备注"]
    for col, header in enumerate(headers, 1):
        cell = ws.cell(row=4, column=col)
        cell.value = header
        cell.font = Font(bold=True, color="FFFFFF")
        cell.fill = PatternFill(start_color="2D3748", fill_type="solid")
        cell.alignment = Alignment(horizontal='center')

    # 数据行
    for row_idx, expense in enumerate(data, 5):
        ws[f'A{row_idx}'] = expense['date']
        ws[f'B{row_idx}'] = expense['category']
        ws[f'C{row_idx}'] = expense['amount']
        ws[f'D{row_idx}'] = expense['description']
        ws[f'E{row_idx}'] = expense.get('notes', '')

    # 总计行
    total_row = len(data) + 5
    ws.merge_cells(f'A{total_row}:D{total_row}')
    ws[f'A{total_row}'] = "总计"
    ws[f'A{total_row}'].font = Font(bold=True)
    ws[f'C{total_row}'] = f"=SUM(C5:C{total_row-1})"
    ws[f'C{total_row}'].font = Font(color="FF0000")

    # 列宽
    ws.column_dimensions['A'].width = 15
    ws.column_dimensions['B'].width = 15
    ws.column_dimensions['C'].width = 15
    ws.column_dimensions['D'].width = 30
    ws.column_dimensions['E'].width = 20

    # 保存
    wb.save(output_file)
    return output_file

# 示例数据
if __name__ == '__main__':
    example_data = [
        {
            "date": "2024-03-15",
            "category": "交通",
            "amount": 50,
            "description": "出租车",
            "notes": "客户会议"
        },
        {
            "date": "2024-03-15",
            "category": "餐饮",
            "amount": 120,
            "description": "商务午餐",
            "notes": ""
        }
    ]

    generate_report(example_data)
```

**步骤 4：打包技能**

```bash
# 使用 skill-creator 打包脚本
scripts/package_skill.py expense-tracker/
```

**步骤 5：测试技能**

```bash
# 安装技能
cp expense-tracker.skill ~/.claude/skills/custom/

# 测试
claude

# 在 Claude 中输入
使用 expense-tracker 技能生成一份 3 月份的费用报告
```

### 21.3 技能最佳实践

| 最佳实践 | 说明 |
|---------|------|
| **简洁的 SKILL.md** | 保持在 500 行以下 |
| **使用 scripts/** | 可重复的代码放在脚本中 |
| **使用 references/** | 详细文档放在参考资料中 |
| **清晰的描述** | description 准确描述何时使用 |
| **渐进式披露** | 元数据 → 正文 → 打包资源 |
| **适当自由度** | 根据任务类型设置自由度级别 |

---

## 22. 最佳实践与技巧

### 22.1 技能使用最佳实践

#### 技能选择

**选择正确的技能**：

| 需求 | 推荐技能 | 替代方案 |
|------|---------|---------|
| 创建 PDF | `pdf` | `docx`（转换为 PDF） |
| 编辑 Word | `docx` | 禁用（直接编辑 XML） |
| 创建演示文稿 | `pptx` | `canvas-design`（静态幻灯片） |
| 数据分析 | `xlsx` + `pandas` | 手动处理 |
| Web 测试 | `webapp-testing` | 手动测试 |

#### 技能调用技巧

```bash
# 明确指定技能
使用 pptx 技能创建演示

# 自然描述让 Claude 选择
帮我创建一个关于产品发布的演示文稿

# 组合技能调用
使用 docx 技能创建文档，然后使用 pptx 技能创建演示文稿
```

### 22.2 性能优化

#### 减少上下文消耗

**方法 1：使用 scripts/**

```bash
# ❌ 不好：将大量代码放在 SKILL.md
# SKILL.md 可能会达到数千行

# ✅ 好：代码放在 scripts/ 中
# SKILL.md 保持精简，只在需要时读取脚本
```

**方法 2：使用 references/**

```bash
# ❌ 不好：所有文档都在 SKILL.md

# ✅ 好：详细文档在 references/ 中
# SKILL.md 中只包含基本说明和引用链接
```

**方法 3：条件性加载**

```markdown
# 在 SKILL.md 中

## 基本信息
[基本信息内容]

## 高级用法
[高级用法内容，仅在需要时加载详细信息]

## 参考文档
- [详细信息](references/advanced.md)
- [API 文档](references/api.md)
```

### 22.3 错误处理

#### 预见常见错误

| 错误类型 | 原因 | 解决方案 |
|---------|------|---------|
| **技能未触发** | description 不够清晰 | 改进 description 字段 |
| **脚本失败** | 依赖缺失 | 检查依赖安装 |
| **文件路径错误** | 相对路径问题 | 使用绝对路径 |
| **格式错误** | 输出格式不支持 | 检查支持的格式 |

#### 调试技巧

```bash
# 1. 检查技能是否被加载
# 在 Claude 中询问：当前可用的技能有哪些？

# 2. 查看错误信息
# 仔细阅读错误消息，找出根本原因

# 3. 逐步调试
# 将复杂任务分解为简单步骤逐步执行

# 4. 验证输出
# 检查输出文件是否符合预期
```

### 22.4 版本控制

#### 技能版本管理

```markdown
---
name: my-skill
version: "1.2.0"
description: ...
---
```

**更新日志**：

```markdown
## 更新日志

### v1.2.0 (2024-03-15)
- 添加 Excel 导出功能
- 修复类别筛选问题

### v1.1.0 (2024-02-20)
- 初始版本发布
```

### 22.5 技能维护

**定期维护任务**：

- [ ] 更新依赖项
- [ ] 修复已知问题
- [ ] 添加新功能
- [ ] 更新文档
- [ ] 测试兼容性

---

# 第七部分：附录

## 23. 常见问题与故障排除

### 23.1 安装问题

#### Q1: Claude Code 命令未找到

**症状**：
```
'claude' 不是内部或外部命令
```

**解决方案**：
```bash
# 1. 检查安装路径
where claude

# 2. 手动添加到 PATH
# 系统属性 → 高级 → 环境变量 → 编辑 Path
# 添加：C:\Users\[用户名]\AppData\Local\Claude

# 3. 重启终端
```

#### Q2: 技能未被识别

**症状**：Claude 说没有该技能

**解决方案**：
```bash
# 1. 检查技能是否已安装
/plugin list

# 2. 重新安装技能
/plugin install example-skills@anthropic-agent-skills

# 3. 检查技能目录
dir %USERPROFILE%\.claude\kills\custom

# 4. 验证 SKILL.md 文件存在
dir %USERPROFILE%\.claude\kills\custom\your-sill\SKILL.md

# 5. 检查 YAML 格式
# 确保文件开头是：---
# name: skill-name
# description: ...
```

#### Q3: 插件安装失败

**症状**：
```
Error: Failed to install plugin
```

**解决方案**：
```bash
# 1. 检查网络连接
ping claude.ai

# 2. 清理插件缓存
rmdir /s %USERPROFILE%\.claude\plugins\cache

# 3. 重新安装
/plugin install example-skills@anthropic-agent-skills
```

#### Q4: 权限错误

**症状**：
```
Error: Permission denied
```

**解决方案**：
```bash
# 1. 以管理员身份运行终端
# 右键点击 Terminal/PowerShell → "以管理员身份运行"

# 2. 检查文件权限
icacls %USERPROFILE%\.claude\skills

# 3. 修复权限
icacls %USERPROFILE%\.claude\skills /grant %USERNAME%:F /T
```

### 23.2 技能使用问题

#### Q5: Python 依赖缺失

**症状**：
```
ModuleNotFoundError: No module named 'xxx'
```

**解决方案**：
```bash
# 安装缺失的依赖
pip install playwright
pip install python-docx
pip install reportlab

# 或使用 requirements.txt
pip install -r requirements.txt
```

#### Q6: Node.js 依赖缺失

**症状**：
```
Error: Cannot find module 'docx'
```

**解决方案**：
```bash
# 全局安装推荐
npm install -g docx

# 或本地安装
npm install docx
```

#### Q7: 文件路径问题

**症状**：
```
FileNotFoundError
```

**解决方案**：
```bash
# 使用绝对路径
# 或在 Claude 中明确指定文件位置
"测试位于 D:\Projects\todo-app.html 的文件"
```

#### Q8: 内存不足错误

**症状**：
```
MemoryError
```

**解决方案**：
```bash
# 对于 pdfplumber
import pdfplumber

# 使用简单提取模式
with pdfplumber.open("large.pdf") as pdf:
    for page in pdf.pages[:10]:  # 只处理前 10 页
        text = page.extract_text_simple()

# 对于 openpyxl
wb = load_workbook('large.xlsx', read_only=True)
```

### 23.3 文档处理问题

#### Q9: Word 文档公式错误

**症状**：
```
#REF! #DIV/0! #VALUE! #N/A #NAME?
```

**解决方案**：
```python
# 1. 检查单元格引用
# 确保所有单元格引用都正确

# 2. 检查分母
# 在公式中使用 IFERROR 处理除以零
# =IFERROR(AVERAGE(D2:D10), 0, AVERAGE(D2:D10))

# 3. 使用 scripts/recalc.py 验证
python scripts/recalc.py output.xlsx

# 4. 添加错误检查
# 在复杂公式中添加 TRY...CATCH
```

#### Q10: PDF 提取问题

**症状**：提取的文本不完整或有乱码

**解决方案**：
```python
# 方法 1：使用 pdfplumber（推荐）
import pdfplumber

with pdfplumber.open("document.pdf") as pdf:
    text = pdf.extract_text()

# 方法 2：使用 OCR（扫描 PDF）
from pdf2image import convert_from_path
import pytesseract

images = convert_from_path('scanned.pdf')
for image in images:
    text += pytesseract.image_to_string(image)
```

#### Q11: PowerPoint 模板问题

**症状**：修改模板后显示占位符文本

**解决方案**：
```bash
# 1. 检查占位符
python -m markitdown presentation.pptx | grep -iE "xxxx|lorem|ipsum"

# 2. 替换所有占位符
# 使用文本替换找到并替换

# 3. 验证模板
python scripts/thumbnail.py presentation.pptx
```

#### Q12: Excel 公式不更新

**症状**：修改数据后公式显示旧值

**解决方案**：
```python
from openpyxl import load_workbook

# 1. 使用 data_only=True 读取计算值
wb = load_workbook('file.xlsx', data_only=True)

# 2. 保存并重新计算
wb.save('new_file.xlsx')

# 3. 使用 LibreOffice 重新计算
python scripts/recalc.py new_file.xlsx
```

### 23.4 Web 应用测试问题

#### Q13: Playwright 浏试失败

**症状**：
```
Error: Target closed
```

**解决方案**：
```python
from playwright.sync_api import sync_playwright

# 1. 添加适当的等待
with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page()

    page.goto('http://localhost:5173')
    page.wait_for_load_state('networkidle')  # 等待 JS 执行

    # 添加元素等待
    page.wait_for_selector('#button', state='visible')

    browser.close()
```

#### Q14: 找不到页面元素

**症状**：
```
TimeoutError: Element not found
```

**解决方案**：
```python
# 1. 使用不同的选择器策略
page.locator('text="提交").click()  # 文本选择器
page.locator('#submit-button').click()  # ID 选择器
page.locator('[type="submit"]').click()  # 属性选择器

# 2. 使用更宽松的等待
page.wait_for_timeout(10000)  # 增加超时时间

# 3. 使用 try-except
try:
    element = page.locator('#my-element')
    element.click()
except:
    print("元素未找到，使用备用选择器")
    page.locator('.alternate-selector').click()
```

### 23.5 MCP 开发问题

#### Q15: MCP 服务器无法连接

**症状**：
```
Error: Failed to connect to MCP server
```

**解决方案**：
```python
# 1. 检查服务器是否运行
# 对于 stdio 传输，确保服务器正在运行

# 2. 检查传输配置
# 确保 client 和 server 使用相同的传输方式

# 3. 查看日志
# 检查服务器日志中的错误信息

# 4. 验证工具定义
# 确保所有工具都有正确的 inputSchema
```

#### Q16: 工具调用失败

**症状**：工具调用后没有返回预期结果

**解决方案**：
```typescript
// 1. 验证输入模式
import { z } from "zod";

const ToolSchemaInput = z.object({
  param: z.string().describe("参数描述")
});

// 2. 添加错误处理
try {
  const result = await apiCall(params);
  return result;
} catch (error) {
  console.error("API 调用失败:", error);
  throw new Error(`API 错误: ${error.message}`);
}

// 3. 返回结构化内容
return {
  content: [{
    type: "text",
    text: JSON.stringify(result, null, 2)
  }]
};
```

### 23.6 性能优化

#### Q17: 响应速度慢

**解决方案**：
```python
# 1. 使用缓存
import functools

@functools.lru_cache(maxsize=128)
def expensive_function(param):
    # 缓存计算结果
    pass

# 2. 并行处理
import asyncio

async def fetch_multiple(urls):
    tasks = [fetch_url(url) for url in urls]
    return await asyncio.gather(*tasks)

# 3. 分页处理
def process_large_data(data, batch_size=100):
    for i in range(0, len(data), batch_size):
        batch = data[i:i+batch_size]
        process_batch(batch)
```

#### Q18: 上下文窗口不足

**解决方案**：
```markdown
# 1. 保持 SKILL.md 精简
# 将详细内容移到 references/

# 2. 使用条件加载
## 基础用法
[基础说明]

## 高级用法
详细信息请参阅 [高级指南](references/advanced.md)

# 3. 使用 scripts/ 减少 token
# 复杂操作放在脚本中，不需要加载到上下文
```

### 23.7 获取帮助

#### 在线资源

- [Claude Code 文档](https://claude.ai/code)
- [Agent Skills 仓库](https://github.com/anthropics/anthropic-agent-skills)
- [MCP 协议文档](https://modelcontextprotocol.io/)

#### 社区支持

- [GitHub Discussions](https://github.com/anthropics/anthropic-agent-skills/discussions)
- [Stack Overflow](https://stackoverflow.com/questions/tagged/anthropic-agent-skills)

#### 反馈渠道

- [Bug 报告](https://github.com/anthropics/anthropic-agent-skills/issues)
- [功能请求](https://github.com/anthropics/anthropic-agent-skills/issues)

---

## 24. 参考资源

### 24.1 官方文档

#### Agent Skills 核心文档

| 资源 | 链接 | 描述 |
|------|------|------|
| **技能规范** | [Agent Skills 规范](https://github.com/anthropics/anthropic-agent-skills/blob/main/spec/agent-skills-spec.md) | 技能文件结构和规范 |
| **技能创建指南** | 本文档第 21 节 | 从零创建技能的完整教程 |
| **示例技能集合** | [example-skills](https://github.com/anthropics/anthropic-agent-skills) | 官方提供的示例技能 |

#### Claude Code 文档

| 资源 | 链接 | 描述 |
|------|------|------|
| **Claude Code 用户指南** | [用户指南](https://claude.ai/code) | 完整使用文档 |
| **更新日志** | [更新日志](https://claude.ai/code/changelog) | 版本更新记录 |
| **已知问题** | [已知问题](https://claude.ai/code/known-issues) | 常见问题和解决方案 |

### 24.2 技术库文档

#### 文档处理库

| 库 | 链接 | 用途 |
|----|------|------|
| **docx-js** | [docx-js 文档](https://docx.js.org/) | 创建 Word 文档 |
| **python-docx** | [python-docx 文档](https://python-docx.readthedocs.io/) | 读取/编辑 Word 文档 |
| **pypdf** | [pypdf 文档](https://pypdf.readthedocs.io/) | PDF 基本操作 |
| **pdfplumber** | [pdfplumber 文档](https://pdfplumber.readthedocs.io/) | PDF 文本/表格提取 |
| **reportlab** | [reportlab 文档](https://reportlab.readthedocs.io/) | 创建 PDF |
| **openpyxl** | [openpyxl 文档](https://openpyxl.readthedocs.io/) | Excel 操作 |
| **pandas** | [pandas 文档](https://pandas.pydata.org/) | 数据分析 |

#### Web 开发库

| 库 | 链接 | 用途 |
|----|------|------|
| **pptxgenjs** | [pptxgenjs 文档](https://gitbrent.github.io/gitbrent-pptxgenjs/) | 创建 PowerPoint |
| **p5.js** | [p5.js 文档](https://p5js.org/) | 生成艺术 |
| **Playwright** | [Playwright 文档](https://playwright.dev/) | Web 应用测试 |
| **React** | [React 文档](https://react.dev/) | 前端框架 |

#### MCP 开发库

| 库 | 链接 | 用途 |
|----|------|------|
| **MCP TypeScript SDK** | [TypeScript SDK](https://github.com/modelcontextprotocol/typescript-sdk) | TypeScript MCP 开发 |
| **MCP Python SDK** | [Python SDK](https://github.com/modelcontextprotocol/python-sdk) | Python MCP 开发 |
| **FastMCP** | [FastMCP 文档](https://github.com/jlowens/fastmcp) | Python MCP 框架 |

### 24.3 学习资源

#### 在线教程

| 资源 | 链接 | 难度 |
|------|------|------|
| **p5.js 基础** | [The Coding Train](https://www.youtube.com/playlist?list=PLRqwWVAvAB16tlbAMlbulwQLKVdjk5s1) | 初级到高级 |
| **Web 开发** | [MDN Web Docs](https://developer.mozilla.org/) | 全面文档 |
| **Python 编程** | [Python 官方指南](https://docs.python.org/zh-cn/) | 官方指南 |
| **TypeScript** | [TypeScript 手册](https://www.typescriptlang.org/zh/) | 语言手册 |

#### 视频教程

- [Agent Skills 入门](https://www.youtube.com/results?search_query=Agent+Skills)
- [Claude Code 教程](https://www.youtube.com/results?search_query=Claude+Code)

### 24.4 社区资源

#### GitHub 仓库

| 仓库 | 链接 | 描述 |
|------|------|------|
| **Agent Skills 官方** | [anthropic-agent-skills](https://github.com/anthropics/anthropic-agent-skills) | 官方技能仓库 |
| **示例项目** | [examples](https://github.com/anthropics/anthropic-agent-skills/tree/main/examples) | 示例用法 |
| **测试项目** | [test-projects](https://github.com/anthropics/anthropic-agent-skills/tree/main/test-projects) | 测试项目 |

#### 社区贡献

- [贡献指南](https://github.com/anthropics/anthropic-agent-skills/blob/main/CONTRIBUTING.md) | 如何贡献代码
- [文档改进](https://github.com/anthropics/anthropic-agent-skills/issues) | 报告文档问题

### 24.5 相关工具

#### 命令行工具

| 工具 | 用途 |
|------|------|
| **claude** | Claude Code CLI |
| **/plugin** | 插件管理 |
| **git** | 版本控制 |

#### IDE 集成

| IDE | 集成方式 |
|-----|---------|
| **VS Code** | [Claude Code 扩展](https://marketplace.visualstudio.com/items?itemName=anthropic.claude-dev) |
| **Cursor** | 原生集成 |
| **IntelliJ IDEA** | 原生集成 |

### 24.6 最佳实践总结

#### 技能开发最佳实践

1. **简洁至上**
   - 保持 SKILL.md 在 500 行以下
   - 使用 scripts/ 存放可执行代码
   - 使用 references/ 存放详细文档

2. **清晰的描述**
   - description 字段应该明确何时使用技能
   - 包含使用场景和示例

3. **渐进式披露**
   - 元数据（name + description）始终加载
   - SKILL.md 正文在触发时加载
   - 打包资源按需加载

4. **适当的自由度**
   - 高自由度：基于文本的指令
   - 中等自由度：伪代码或带参数的脚本
   - 低自由度：特定脚本

#### 技能使用最佳实践

1. **明确指定技能**
   - 使用技能名称：`使用 docx 技能创建文档`
   - 避免模糊的请求

2. **组合使用技能**
   - 可以在单次请求中组合多个技能
   - 一个技能的输出可以是另一个的输入

3. **验证输出**
   - 检查生成的文件是否符合预期
   - 阅读输出文件确认内容正确

4. **提供反馈**
   - 如果技能输出不满足需求，提供具体反馈
   - 帮助技能学习和改进

---

**文档版本**：v2.0
**更新日期**：2026年2月10日
**维护者**：Claude Code

---

**感谢阅读 Agent Skills 实战指南！**

现在您已经：
- ✅ 理解了 Agent Skills 的核心概念
- ✅ 学会了所有 16 个官方技能的使用方法
- ✅ 掌握了创建自定义技能的完整流程
- ✅ 了解了技能组合使用的高级技巧
- ✅ 获得了故障排除和问题解决的实用指南

**开始构建您的 Agent Skills 之旅！**

如有任何问题或建议，请通过以下方式反馈：
- GitHub Issues: https://github.com/anthropics/anthropic-agent-skills/issues
- Claude Code 文档: https://claude.ai/code
