# 快速开始指南

本指南将帮助您快速搭建自己的 Skills Marketplace。

## 5 分钟快速搭建

### 步骤 1: 准备 GitHub 仓库

1. 在 GitHub 上创建一个新的公开仓库（例如：`your-username/skills`）
2. 克隆仓库到本地：

```bash
git clone https://github.com/your-username/skills.git
cd skills
```

### 步骤 2: 复制文件结构

将本项目的以下文件复制到您的仓库：

```
.claude-plugin/
└── marketplace.json
skills/
├── course-designer/
│   └── SKILL.md
├── learning-assessor/
│   └── SKILL.md
└── ...
README.md
```

### 步骤 3: 修改配置

编辑 `.claude-plugin/marketplace.json`，修改以下内容：

```json
{
  "name": "your-marketplace-name",  // 修改为您的 marketplace 名称
  "owner": {
    "name": "Your Name",            // 修改为您的名称
    "email": "your@email.com"       // 修改为您的邮箱
  },
  "metadata": {
    "description": "您的 marketplace 描述",
    "version": "1.0.0"
  },
  "plugins": [
    // 根据您的 skills 修改插件配置
  ]
}
```

### 步骤 4: 提交到 GitHub

```bash
git add .
git commit -m "Initial marketplace setup"
git push origin main
```

### 步骤 5: 在 Claude Code 中使用

在 Claude Code 中运行：

```
/plugin marketplace add your-username/skills
```

然后安装插件：

```
/plugin install your-plugin-name@your-marketplace-name
```

## 核心文件说明

### 1. `.claude-plugin/marketplace.json`

这是 marketplace 的核心配置文件，定义了：
- Marketplace 的名称和元数据
- 可用的插件列表
- 每个插件包含的技能

### 2. `skills/*/SKILL.md`

每个技能必须包含一个 `SKILL.md` 文件，格式：

```markdown
---
name: skill-name
description: 技能的简短描述
---

# 技能名称

技能内容...
```

### 3. `README.md`

项目的说明文档，帮助用户了解如何使用您的 marketplace。

## 添加新技能

### 1. 创建技能目录

```bash
mkdir -p skills/my-new-skill
```

### 2. 创建 SKILL.md

```bash
cat > skills/my-new-skill/SKILL.md << 'EOF'
---
name: my-new-skill
description: 我的新技能描述
---

# 我的新技能

技能内容...
EOF
```

### 3. 更新 marketplace.json

在 `plugins` 数组中添加新技能：

```json
{
  "name": "my-plugin",
  "skills": [
    "./skills/my-new-skill"
  ]
}
```

### 4. 提交更改

```bash
git add skills/my-new-skill .claude-plugin/marketplace.json.back
git commit -m "Add new skill: my-new-skill"
git push
```

## 验证安装

### 检查 marketplace.json

确保 JSON 格式正确：

```bash
cat .claude-plugin/marketplace.json.back | python -m json.tool
```

### 检查技能文件

确保每个技能都有 `SKILL.md` 文件：

```bash
find skills -name "SKILL.md" -type f
```

### 测试 GitHub 访问

确保文件可以通过 GitHub 访问：

```
https://raw.githubusercontent.com/your-username/skills/main/.claude-plugin/marketplace.json
```

## 常见问题

### Q: 命令执行后没有反应？

A: 检查以下几点：
1. 仓库是否为公开仓库（public）
2. `marketplace.json` 文件路径是否正确
3. JSON 格式是否正确
4. 网络连接是否正常

### Q: 如何更新技能？

A: 修改 `SKILL.md` 文件，提交并推送到 GitHub。Claude Code 会自动获取最新版本。

### Q: 可以创建私有 marketplace 吗？

A: 目前 Claude Code 只支持公开的 GitHub 仓库。如果需要私有 marketplace，可能需要其他方案。

### Q: 如何组织多个插件？

A: 在 `marketplace.json` 的 `plugins` 数组中添加多个插件对象，每个插件可以包含不同的技能集合。

## 下一步

- 阅读 [IMPLEMENTATION.md](IMPLEMENTATION.md) 了解详细实现机制
- 阅读 [README.md](README_anthropic_skills.md) 了解完整使用说明
- 参考 [agent-skills](https://github.com/anthropics/skills) 获取更多示例

## 示例命令

```bash
# 注册 marketplace
/plugin marketplace add your-username/skills

# 查看可用插件
# 在 Claude Code 界面中选择 "Browse and install plugins"

# 安装插件
/plugin install teaching-skills@your-marketplace-name

# 使用技能
# 直接在对话中提及技能即可，例如：
# "使用课程设计技能帮我设计一门课程"
```

## 总结

搭建 Skills Marketplace 只需要：

1. ✅ 创建 GitHub 仓库
2. ✅ 创建 `.claude-plugin/marketplace.json`
3. ✅ 创建 skills 目录和 `SKILL.md` 文件
4. ✅ 提交到 GitHub
5. ✅ 在 Claude Code 中使用

整个过程完全基于 GitHub，无需额外的服务器或 API！
