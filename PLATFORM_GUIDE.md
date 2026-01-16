# 跨平台使用指南

本指南说明如何将 Teaching AI Skills 在不同平台上使用，包括 Trae、Cursor、Qoder、CodeBuddy 等。

## ⚠️ 重要说明

**本指南中的适配方法为理论性指导，尚未经过实际验证。** 

- 这些方法基于平台的一般特性和常见的适配模式
- 不同平台的 API 和配置格式可能会有所不同
- **建议在实际使用前：**
  1. 查阅目标平台的官方文档
  2. 在小范围内测试适配方案
  3. 根据实际平台特性调整配置
  4. 如有问题，欢迎通过 GitHub Issues 反馈

## 概述

Teaching AI Skills 遵循 [Agent Skills 标准](https://agentskills.io/)，这是一个开放的技能格式规范。虽然不同平台对 skills 的支持程度不同，但通过适当的适配，这些 skills 可以在多个平台上使用。

## 平台支持情况

### 1. Claude Code（原生支持）

Claude Code 完全支持 Agent Skills 标准，可以直接使用 marketplace 方式安装。

**安装方式：**
```bash
/plugin marketplace add teaching-ai/skills
/plugin install teaching-skills@teaching-ai-skills
```

### 2. Claude.ai（原生支持）

Claude.ai 的付费套餐支持直接上传和使用 skills。

**使用方式：**
1. 访问 Claude.ai 设置
2. 上传 `SKILL.md` 文件或整个技能目录
3. 在对话中直接使用技能

### 3. Claude API（原生支持）

通过 Claude API 可以上传和使用自定义 skills。

**使用方式：**
参考 [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill)

### 4. Cursor（部分支持）

Cursor 是一个基于 AI 的代码编辑器，支持通过自定义指令和上下文文件来扩展 AI 能力。

#### 适配方法

**方法一：作为自定义指令使用**

1. 将 `SKILL.md` 的内容转换为 Cursor 的自定义指令格式
2. 在 Cursor 设置中添加为 `.cursorrules` 或自定义指令

**步骤：**
```bash
# 1. 复制技能内容
cp skills/course-designer/SKILL.md ~/.cursor/rules/course-designer.md

# 2. 在 Cursor 设置中引用
# Settings > Rules > Add Rule
# 指向 ~/.cursor/rules/course-designer.md
```

**方法二：作为项目上下文使用**

1. 将技能目录添加到项目根目录
2. 在 `.cursorignore` 中排除不需要的文件
3. Cursor 会自动读取项目中的 `SKILL.md` 文件

**示例项目结构：**
```
my-project/
├── .cursor/
│   └── rules/
│       └── teaching-skills.md
├── skills/
│   ├── course-designer/
│   │   └── SKILL.md
│   └── code-generator/
│       └── SKILL.md
└── .cursorignore
```

**方法三：转换为 Cursor Composer 指令**

将技能的核心功能转换为 Cursor 的 Composer 指令模板：

```markdown
# Course Designer Skill for Cursor

When the user asks about course design, curriculum planning, or educational content:

1. Analyze the requirements
2. Design course structure
3. Create learning objectives
4. Plan assessment methods

[原 SKILL.md 的内容...]
```

### 5. Trae（需要适配）

> **注意：** 以下适配方案为理论性建议，需要根据 Trae 平台的实际插件系统进行验证和调整。建议先查阅 Trae 的官方文档了解其插件机制。

Trae 如果支持插件或扩展系统，可以通过以下方式适配：

#### 适配步骤

1. **检查平台插件格式**
   - 查看 Trae 是否支持插件系统
   - 了解插件 manifest 格式要求

2. **转换技能格式**
   - 将 `SKILL.md` 转换为 Trae 支持的格式
   - 可能需要创建 `trae-plugin.json` 配置文件

3. **处理依赖**
   - 确保技能所需的脚本和资源可以被 Trae 访问
   - 调整文件路径引用

**示例适配：**
```json
// trae-plugin.json
{
  "name": "teaching-skills",
  "version": "1.0.0",
  "description": "Teaching and education skills",
  "skills": [
    {
      "name": "course-designer",
      "description": "Course design skill",
      "instructions": "./skills/course-designer/SKILL.md"
    }
  ]
}
```

### 6. Qoder（需要适配）

[Qoder](https://qoder.com/) 是一个 **agentic coding platform**（代理式编程平台），支持端到端的编码流程，包括代码生成、调试、部署等阶段。Qoder 支持以 agent 的形式自动化编程任务。

> **注意：** 以下适配方案基于 Qoder 作为 agentic platform 的一般特性，具体的 agent 配置格式、API 接口等需要查阅 Qoder 官方文档进行验证。示例配置格式仅供参考，实际格式可能有所不同。

#### 适配方法

由于 Qoder 是一个 agentic 平台，可以将 skills 适配为 Qoder 的 agent 模块：

1. **转换为 Agent 模块**
   - 将 `SKILL.md` 中的指令转换为 Qoder agent 的工作流程
   - 定义 agent 的输入、输出和执行步骤
   - 将技能的工作流程映射为 Qoder 的 agent 任务

2. **创建 Agent 配置文件**
   - 为每个技能创建 Qoder agent 配置文件
   - 定义 agent 的能力和触发条件

3. **部署到 Qoder 环境**
   - 将技能代码和配置部署到 Qoder 可访问的位置
   - 配置 agent 的权限和依赖

**示例 Agent 配置：**
```json
// qoder-agent-config.json
{
  "name": "course-designer-agent",
  "description": "Agent for designing courses and curricula",
  "version": "1.0.0",
  "capabilities": [
    "course-design",
    "curriculum-planning",
    "learning-objective-creation"
  ],
  "workflow": [
    {
      "step": "analyze-requirements",
      "description": "Analyze course requirements and constraints"
    },
    {
      "step": "design-structure",
      "description": "Design course structure and modules"
    },
    {
      "step": "create-objectives",
      "description": "Create learning objectives"
    },
    {
      "step": "plan-assessments",
      "description": "Plan assessment methods"
    }
  ],
  "instructions": "./skills/course-designer/SKILL.md"
}
```

**示例 Python Agent 模块：**
```python
# qoder_agent_module.py
"""
Course Designer Agent for Qoder
"""
class CourseDesignerAgent:
    """
    Agent for designing courses and educational content
    """
    def __init__(self):
        self.name = "course-designer"
        self.description = "Designs courses and curricula"
    
    def execute(self, task, context):
        """
        Execute course design task
        """
        # 读取 SKILL.md 中的指令
        # 执行课程设计工作流
        # 返回设计结果
        pass
    
    def analyze_requirements(self, topic, duration, level):
        """Analyze course requirements"""
        pass
    
    def design_structure(self, requirements):
        """Design course structure"""
        pass
```

**适配步骤：**
1. 检查 Qoder 的 agent 配置格式要求
2. 将 `SKILL.md` 转换为 Qoder agent 指令
3. 创建 agent 配置文件（JSON 或 YAML）
4. 将技能资源部署到 Qoder 可访问的位置
5. 在 Qoder 中注册和激活 agent

### 7. Windsurf（需要适配）

[Windsurf](https://windsurf.com/) 是一个 AI 驱动的代码编辑器，支持 Cascade Skills 系统。Windsurf 使用与 Agent Skills 相同的 SKILL.md 格式，转换相对简单。

#### 适配方法

由于 Windsurf 使用与 Agent Skills 相同的格式，转换主要是复制文件结构：

1. **复制 SKILL.md**
   - Windsurf 使用相同的 YAML frontmatter + Markdown 格式
   - 可以直接使用原始的 SKILL.md 文件

2. **复制资源文件**
   - 自动复制 scripts、templates、references 等目录
   - 保留技能的所有辅助资源

3. **部署到 Windsurf**
   - 项目级：放在 `.windsurf/skills/` 目录
   - 全局级：放在 `~/.windsurf/skills/` 目录

**适配步骤：**
1. 将技能目录复制到 Windsurf skills 目录
2. 确保 SKILL.md 文件格式正确
3. 在 Windsurf 中激活技能

**示例结构：**
```
.windsurf/
└── skills/
    └── course-designer/
        ├── SKILL.md
        ├── scripts/          # 如果原技能有脚本
        └── templates/        # 如果原技能有模板
```

### 8. CodeBuddy（需要适配）

> **注意：** 以下适配方案为理论性建议，需要根据 CodeBuddy 平台的实际功能进行验证。建议先查阅 CodeBuddy 的官方文档了解其支持的插件或 workflow 格式。

CodeBuddy 如果支持 workflows 或 tips 插件，可以这样适配：

#### 适配步骤

1. **创建插件包**
   - 将技能打包为 CodeBuddy 支持的格式
   - 包含 manifest 文件和技能内容

2. **转换为 Workflow 格式**
   - 将技能的工作流程转换为 CodeBuddy 的 workflow 格式
   - 定义输入、输出和步骤

**示例结构：**
```
codebuddy-plugin/
├── manifest.json
├── workflows/
│   ├── course-design.json
│   └── code-generation.json
└── skills/
    └── course-designer/
        └── SKILL.md
```

## 通用适配方案

### 方案一：作为文档/上下文使用

大多数 AI 平台都支持读取项目中的文档文件，可以将 skills 作为上下文文档使用。

**步骤：**
1. 将技能目录复制到项目根目录
2. 在平台设置中配置读取这些文件
3. AI 会自动参考这些文档内容

**优点：**
- 简单直接
- 不需要特殊配置
- 跨平台兼容性好

**缺点：**
- 不会自动触发
- 需要用户明确引用

### 方案二：转换为自定义指令

将技能内容转换为平台的自定义指令格式。

**步骤：**
1. 提取 `SKILL.md` 的核心指令部分
2. 转换为目标平台的自定义指令格式
3. 在平台设置中配置

**示例（通用格式）：**
```markdown
# Custom Instruction: Course Designer

When the user asks about course design:
- Analyze requirements
- Design course structure
- Create learning objectives
- Plan assessments

[详细指令内容...]
```

### 方案三：创建适配层

为不同平台创建适配层，将 Agent Skills 标准转换为平台特定格式。

**项目结构：**
```
adapters/
├── cursor/
│   └── convert_to_cursor.py
├── trae/
│   └── convert_to_trae.py
├── qoder/
│   └── convert_to_qoder.py
├── codebuddy/
│   └── convert_to_codebuddy.py
└── windsurf/
    └── convert_to_windsurf.py
```

**转换脚本示例：**
```python
# adapters/cursor/convert_to_cursor.py
def convert_skill_to_cursor(skill_path):
    """
    Convert Agent Skill to Cursor custom instruction format
    """
    with open(f"{skill_path}/SKILL.md", "r") as f:
        content = f.read()
    
    # 提取 frontmatter
    frontmatter = extract_frontmatter(content)
    
    # 转换为 Cursor 格式
    cursor_rule = f"""
# {frontmatter['name']}

{frontmatter['description']}

{content}
"""
    return cursor_rule
```

## 技能结构说明

每个技能包含以下结构，了解这些有助于适配：

```
skill-name/
├── SKILL.md              # 核心技能定义（必需）
├── scripts/              # 可执行脚本（可选）
│   └── script.py
├── references/           # 参考文档（可选）
│   └── reference.md
└── assets/               # 资源文件（可选）
    └── template.html
```

### SKILL.md 结构

```markdown
---
name: skill-name
description: Skill description
---

# Skill Title

## Overview
...

## Usage
...

## Examples
...
```

**适配要点：**
- Frontmatter 中的 `name` 和 `description` 是关键信息
- Markdown 内容可以直接作为指令使用
- 脚本和资源需要根据平台能力调整

## 平台特定建议

### Cursor

**推荐方式：**
1. 使用 `.cursorrules` 文件
2. 将常用技能添加到项目根目录
3. 使用 Cursor 的 Composer 功能

**示例 `.cursorrules`：**
```markdown
# Teaching AI Skills

When working with course design, use the course-designer skill.
When generating code, use the code-generator skill.

[技能内容...]
```

### Trae

**推荐方式：**
1. 检查 Trae 的插件系统文档
2. 创建符合 Trae 格式的插件 manifest
3. 将技能内容作为插件资源

### Qoder

**推荐方式：**
1. 将技能转换为 Qoder agent 模块
2. 创建 agent 配置文件（JSON/YAML）
3. 将技能指令适配为 agent 工作流
4. 在 Qoder 中注册 agent 并配置权限

**参考资源：**
- [Qoder 官网](https://qoder.com/)
- Qoder agent 配置文档（请查阅 Qoder 官方文档）

### Windsurf

**推荐方式：**
1. 将技能目录复制到 `.windsurf/skills/` 或 `~/.windsurf/skills/`
2. Windsurf 使用与 Agent Skills 相同的格式，无需转换
3. 确保所有资源文件（scripts、templates 等）都被复制

**参考资源：**
- [Windsurf 官网](https://windsurf.com/)
- [Windsurf Cascade Skills 文档](https://docs.windsurf.com/windsurf/cascade/skills)

### CodeBuddy

**推荐方式：**
1. 创建 workflow 定义文件
2. 将技能转换为 step-by-step 工作流
3. 打包为 CodeBuddy 插件格式

## 最佳实践

### 1. 保持技能独立性

确保每个技能都是自包含的，不依赖特定平台特性。

### 2. 使用相对路径

在技能中使用相对路径引用资源，便于跨平台使用。

### 3. 提供平台适配文档

为每个技能创建平台特定的使用说明。

### 4. 测试兼容性

在不同平台上测试技能的功能和兼容性。

### 5. 创建转换工具

开发自动化工具将技能转换为不同平台格式。

## 转换工具示例

> **注意：** 以下转换工具示例为概念性代码，展示了基本的转换思路。实际使用时需要根据目标平台的具体 API 和格式要求进行调整和测试。

### Python 转换脚本

```python
#!/usr/bin/env python3
"""
Convert Agent Skills to different platform formats
"""
import os
import json
import yaml
from pathlib import Path

def convert_to_cursor(skill_path, output_path):
    """Convert skill to Cursor format"""
    skill_file = Path(skill_path) / "SKILL.md"
    with open(skill_file, "r") as f:
        content = f.read()
    
    # Extract frontmatter
    frontmatter_end = content.find("---", 3)
    frontmatter = yaml.safe_load(content[3:frontmatter_end])
    body = content[frontmatter_end + 3:].strip()
    
    # Create Cursor rule
    cursor_rule = f"""# {frontmatter['name']}

{frontmatter['description']}

{body}
"""
    
    with open(output_path, "w") as f:
        f.write(cursor_rule)
    
    print(f"Converted to Cursor format: {output_path}")

def convert_to_platform_manifest(skill_path, platform):
    """Convert skill to platform-specific manifest"""
    skill_file = Path(skill_path) / "SKILL.md"
    with open(skill_file, "r") as f:
        content = f.read()
    
    frontmatter_end = content.find("---", 3)
    frontmatter = yaml.safe_load(content[3:frontmatter_end])
    
    manifest = {
        "name": frontmatter['name'],
        "description": frontmatter['description'],
        "version": "1.0.0",
        "platform": platform,
        "skill_file": "SKILL.md"
    }
    
    manifest_path = Path(skill_path) / f"{platform}-manifest.json"
    with open(manifest_path, "w") as f:
        json.dump(manifest, f, indent=2)
    
    print(f"Created manifest: {manifest_path}")

if __name__ == "__main__":
    # Example usage
    skill_path = "skills/course-designer"
    convert_to_cursor(skill_path, ".cursor/rules/course-designer.md")
    convert_to_platform_manifest(skill_path, "trae")
```

## 常见问题

### Q: 技能中的脚本在其他平台能运行吗？

A: 取决于平台是否支持执行脚本。如果不支持，需要：
- 将脚本逻辑转换为平台支持的语言
- 或者将脚本功能描述为指令，让 AI 生成代码

### Q: 如何确保技能在不同平台上行为一致？

A: 
- 使用平台无关的指令描述
- 避免依赖特定平台特性
- 在多个平台上测试

### Q: 技能的资源文件如何处理？

A: 
- 使用相对路径
- 确保资源文件随技能一起复制
- 在平台配置中设置正确的资源路径

### Q: 如何让技能自动触发？

A: 
- 在支持自动触发的平台（如 Claude Code），技能会自动触发
- 在不支持的平台，需要用户明确引用或转换为命令/按钮

## 贡献适配方案

如果你为某个平台创建了适配方案，欢迎贡献：

1. Fork 本仓库
2. 在 `adapters/` 目录下创建平台适配代码
3. **提供实际测试验证**：说明在哪个平台版本上测试过，测试结果如何
4. 更新本文档，标注已验证的平台和方法
5. 提交 Pull Request

### 已验证的平台

目前以下平台的适配方法已经过实际验证：

- ✅ **Claude Code** - 原生支持，已验证
- ✅ **Claude.ai** - 原生支持，已验证
- ✅ **Claude API** - 原生支持，已验证

以下平台的方法需要社区验证：

- ⚠️ **Cursor** - 需要验证（基于 Cursor 的一般特性提出）
- ⚠️ **Trae** - 需要验证（理论性建议）
- ⚠️ **Qoder** - 需要验证（基于 agentic platform 特性提出）
- ⚠️ **Windsurf** - 需要验证（使用相同格式，转换简单）
- ⚠️ **CodeBuddy** - 需要验证（理论性建议）

如果你验证了某个平台的适配方法，请在 Pull Request 中说明：
- 测试的平台版本
- 测试环境
- 测试结果
- 遇到的问题和解决方案

### 已验证的平台

目前以下平台的适配方法已经过实际验证：

- ✅ **Claude Code** - 原生支持，已验证
- ✅ **Claude.ai** - 原生支持，已验证
- ✅ **Claude API** - 原生支持，已验证

以下平台的方法需要社区验证：

- ⚠️ **Cursor** - 需要验证
- ⚠️ **Trae** - 需要验证
- ⚠️ **Qoder** - 需要验证
- ⚠️ **CodeBuddy** - 需要验证

如果你验证了某个平台的适配方法，请在 Pull Request 中说明测试环境和结果。

## 参考资源

- [Agent Skills 规范](https://agentskills.io/)
- [Claude Skills 文档](https://support.claude.com/en/articles/12512176-what-are-skills)
- [Cursor 自定义指令文档](https://docs.cursor.com/)
- [Qoder 官网](https://qoder.com/)
- [Windsurf 官网](https://windsurf.com/)
- [Windsurf Cascade Skills 文档](https://docs.windsurf.com/windsurf/cascade/skills)
- 各平台官方文档

## 联系方式

如有问题或需要帮助，请通过 GitHub Issues 联系我们。
