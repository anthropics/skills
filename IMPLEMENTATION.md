# Skills Marketplace 实现机制详解

本文档详细说明 `/plugin marketplace add` 命令的实现机制，以及如何搭建自己的免费技能市场。

## 核心机制

### 1. 命令格式

```
/plugin marketplace add <github-username>/<repository-name>
```

例如：
```
/plugin marketplace add anthropics/skills
/plugin marketplace add teaching-ai/skills
```

### 2. 工作原理

当您在 Claude Code 中执行 `/plugin marketplace add` 命令时，系统会执行以下步骤：

#### 步骤 1: 解析仓库信息

系统解析命令中的 GitHub 仓库路径：
- `anthropics/skills` → 用户名: `anthropics`, 仓库名: `skills`
- 构建 GitHub API URL: `https://api.github.com/repos/anthropics/skills`

#### 步骤 2: 获取 Marketplace 配置

系统从 GitHub 仓库获取配置文件：
- 路径: `.claude-plugin/marketplace.json`
- URL: `https://raw.githubusercontent.com/anthropics/skills/main/.claude-plugin/marketplace.json`
- 或通过 GitHub API: `https://api.github.com/repos/anthropics/skills/contents/.claude-plugin/marketplace.json`

#### 步骤 3: 解析配置

系统解析 `marketplace.json` 文件，获取：
- Marketplace 名称和元数据
- 可用的插件列表
- 每个插件包含的技能列表

#### 步骤 4: 注册 Marketplace

系统将 marketplace 信息存储到本地配置中，使其可用于后续的插件安装。

#### 步骤 5: 安装插件

当用户安装插件时，系统会：
1. 从 GitHub 仓库下载插件中定义的所有 skills
2. 将 skills 存储到本地（通常在 `~/.claude/plugins/` 或类似位置）
3. 使 skills 可用于 Claude

## 配置文件结构

### marketplace.json 格式

```json
{
  "name": "marketplace-identifier",    // Marketplace 的唯一标识符
  "owner": {                            // 所有者信息（可选）
    "name": "Owner Name",
    "email": "owner@example.com"
  },
  "metadata": {                          // 元数据
    "description": "Marketplace 描述",
    "version": "1.0.0"                   // 版本号
  },
  "plugins": [                           // 插件列表
    {
      "name": "plugin-identifier",       // 插件的唯一标识符
      "description": "插件描述",
      "source": "./",                    // 源代码根路径（相对于仓库根目录）
      "strict": false,                   // 是否严格模式（通常为 false）
      "skills": [                        // 技能路径列表（相对于 source）
        "./skills/skill1",
        "./skills/skill2"
      ]
    }
  ]
}
```

### 关键字段说明

- **name**: Marketplace 的唯一标识符，用于在系统中识别
- **plugins**: 插件数组，每个插件可以包含多个 skills
- **source**: 源代码路径，通常为 `"./"`（仓库根目录）
- **skills**: 技能路径数组，相对于 `source` 路径

## Skill 结构

### 目录结构

每个 skill 是一个目录，必须包含 `SKILL.md` 文件：

```
skill-name/
├── SKILL.md              # 必需：技能定义文件
├── scripts/              # 可选：可执行脚本
│   └── script.py
├── references/           # 可选：参考文档
│   └── reference.md
└── assets/               # 可选：资源文件
    └── template.html
```

### SKILL.md 格式

每个 `SKILL.md` 文件必须包含：

1. **YAML Frontmatter**（必需）:
```yaml
---
name: skill-name          # 技能的唯一标识符（小写，使用连字符）
description: 技能的简短描述，说明何时使用这个技能
license: 许可证信息（可选）
---
```

2. **Markdown 内容**（必需）:
```markdown
# 技能名称

## 概述
技能的详细说明...

## 核心功能
...

## 使用指南
...
```

### 关键要求

- **name**: 必须是小写，使用连字符分隔（kebab-case）
- **description**: 必须清晰描述何时使用该技能，这是 Claude 判断是否使用技能的主要依据
- **SKILL.md**: 文件名必须严格为 `SKILL.md`（全大写）

## 实现步骤

### 1. 创建 GitHub 仓库

1. 在 GitHub 上创建新仓库（例如：`teaching-ai/skills`）
2. 确保仓库是公开的（public），这样 Claude Code 才能访问

### 2. 创建目录结构

```bash
mkdir -p .claude-plugin
mkdir -p skills/your-skill-name
```

### 3. 创建 marketplace.json

在 `.claude-plugin/marketplace.json` 中定义 marketplace 配置。

### 4. 创建 Skills

为每个技能创建目录和 `SKILL.md` 文件。

### 5. 提交到 GitHub

```bash
git add .
git commit -m "Initial marketplace setup"
git push origin main
```

### 6. 在 Claude Code 中使用

```
/plugin marketplace add teaching-ai/skills
```

## 技术细节

### GitHub API 访问

Claude Code 可能使用以下方式访问 GitHub 内容：

1. **GitHub API**:
   - 获取文件内容: `GET /repos/{owner}/{repo}/contents/{path}`
   - 需要处理 Base64 编码的内容

2. **Raw GitHub URLs**:
   - 直接访问: `https://raw.githubusercontent.com/{owner}/{repo}/{branch}/{path}`
   - 更简单，但需要知道分支名

3. **GitHub CLI**:
   - 使用 `gh` 命令获取内容

### 本地存储

安装的插件和 skills 通常存储在：
- macOS/Linux: `~/.claude/plugins/` 或 `~/.config/claude/plugins/`
- Windows: `%APPDATA%\claude\plugins\`

### 技能加载机制

1. **启动时**: 只加载所有技能的 `name` 和 `description`（从 frontmatter）
2. **使用时**: 当 Claude 判断需要某个技能时，加载完整的 `SKILL.md` 内容
3. **按需加载**: 脚本、参考文档等资源按需加载

## 最佳实践

### Marketplace 设计

1. **清晰的命名**: 使用描述性的名称
2. **逻辑分组**: 将相关技能组织到同一个插件中
3. **版本管理**: 在 `metadata` 中维护版本号
4. **文档完善**: 提供清晰的 README 和使用说明

### Skill 设计

1. **精确的描述**: `description` 字段应该准确描述何时使用该技能
2. **简洁的内容**: 保持 `SKILL.md` 简洁，避免不必要的冗长
3. **结构化组织**: 使用清晰的章节和结构
4. **实用示例**: 提供实际可用的示例

### 仓库管理

1. **版本控制**: 使用 Git 进行版本控制
2. **分支策略**: 使用 `main` 或 `master` 作为主分支
3. **标签管理**: 使用 Git tags 标记版本
4. **持续更新**: 定期更新和维护 skills

## 故障排除

### 常见问题

1. **无法找到 marketplace.json**
   - 检查文件路径是否正确：`.claude-plugin/marketplace.json`
   - 确保文件已提交到 GitHub
   - 检查仓库是否为公开仓库

2. **技能无法加载**
   - 检查 `SKILL.md` 文件是否存在
   - 验证 YAML frontmatter 格式是否正确
   - 确保技能路径在 `marketplace.json` 中正确配置

3. **插件安装失败**
   - 检查 GitHub 仓库访问权限
   - 验证网络连接
   - 查看 Claude Code 的错误日志

## 扩展功能

### 添加脚本支持

在 skill 目录下创建 `scripts/` 目录，添加可执行脚本：

```bash
skills/your-skill/
├── SKILL.md
└── scripts/
    └── process.py
```

在 `SKILL.md` 中引用脚本：

```markdown
## 使用脚本

运行处理脚本：
```bash
python scripts/process.py [args]
```
```

### 添加参考文档

在 skill 目录下创建 `references/` 目录：

```bash
skills/your-skill/
├── SKILL.md
└── references/
    └── api-reference.md
```

在 `SKILL.md` 中引用：

```markdown
## API 参考

详细 API 文档请参考 [API Reference](references/api-reference.md)
```

### 添加资源文件

在 skill 目录下创建 `assets/` 目录：

```bash
skills/your-skill/
├── SKILL.md
└── assets/
    └── template.html
```

## 总结

`/plugin marketplace add` 命令的实现机制相对简单：

1. **解析命令**: 提取 GitHub 仓库信息
2. **获取配置**: 从 GitHub 下载 `marketplace.json`
3. **注册**: 将 marketplace 添加到本地配置
4. **安装**: 下载并安装插件中的 skills

要搭建自己的技能市场，只需要：
1. 创建 GitHub 仓库
2. 创建 `.claude-plugin/marketplace.json` 配置文件
3. 创建 skills 目录和 `SKILL.md` 文件
4. 提交到 GitHub
5. 在 Claude Code 中使用 `/plugin marketplace add` 命令

整个过程完全基于 GitHub 的公开仓库，无需额外的服务器或 API。
