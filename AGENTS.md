# AGENTS.md

本文档为 AI 编码智能体（Claude Code、Cursor、Copilot 等）在本仓库中工作时提供指导。

## 仓库概览

面向 Claude.ai 与 Claude Code 的一组技能集合，用于处理与 Vercel 部署相关的工作。技能是经过打包的说明与脚本，用于扩展 Claude 的能力。

## 创建新技能

### 目录结构

```
skills/
  {skill-name}/           # kebab-case directory name
    SKILL.md              # Required: skill definition
    scripts/              # Required: executable scripts
      {script-name}.sh    # Bash scripts (preferred)
  {skill-name}.zip        # Required: packaged for distribution
```

### 命名规范

- **技能目录**：`kebab-case`（例如 `vercel-deploy`、`log-monitor`）
- **SKILL.md**：始终使用全大写，且文件名必须严格为 `SKILL.md`
- **脚本**：`kebab-case.sh`（例如 `deploy.sh`、`fetch-logs.sh`）
- **Zip 文件**：必须与目录名严格一致：`{skill-name}.zip`

### SKILL.md 格式

```markdown
---
name: {skill-name}
description: {One sentence describing when to use this skill. Include trigger phrases like "Deploy my app", "Check logs", etc.}
---

# {Skill Title}

{Brief description of what the skill does.}

## How It Works

{Numbered list explaining the skill's workflow}

## Usage

```bash
bash /mnt/skills/user/{skill-name}/scripts/{script}.sh [args]
```

**Arguments:**
- `arg1` - Description (defaults to X)

**Examples:**
{Show 2-3 common usage patterns}

## Output

{Show example output users will see}

## Present Results to User

{Template for how Claude should format results when presenting to users}

## Troubleshooting

{Common issues and solutions, especially network/permissions errors}
```

### 上下文效率最佳实践

技能按需加载——启动时只加载技能名称与描述。只有当智能体判断某个技能相关时，完整的 `SKILL.md` 才会进入上下文。为减少上下文占用：

- **将 SKILL.md 控制在 500 行以内**——详细参考资料放在单独文件中
- **描述写得具体**——帮助智能体准确判断何时激活技能
- **渐进式披露**——引用支撑文件，仅在需要时再读取
- **优先用脚本而不是内联代码**——执行脚本不会占用上下文（只有输出会占用）
- **文件引用只支持一层深度**——从 SKILL.md 直接链接到支撑文件

### 脚本要求

- 使用 `#!/bin/bash` shebang
- 使用 `set -e` 实现失败即退出
- 将状态信息输出到 stderr：`echo "Message" >&2`
- 将机器可读输出（JSON）写入 stdout
- 为临时文件加入 cleanup trap
- 脚本路径引用格式为 `/mnt/skills/user/{skill-name}/scripts/{script}.sh`

### 创建 Zip 包

创建或更新技能后：

```bash
cd skills
zip -r {skill-name}.zip {skill-name}/
```

### 终端用户安装

为用户记录以下两种安装方式：

**Claude Code：**
```bash
cp -r skills/{skill-name} ~/.claude/skills/
```

**claude.ai：**
将技能加入项目知识，或将 SKILL.md 内容粘贴到对话中。

如果技能需要网络访问，提示用户在 `claude.ai/admin-settings/capabilities` 中添加所需域名。

