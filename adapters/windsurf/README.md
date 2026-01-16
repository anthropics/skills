# Windsurf Adapter

将 Agent Skills 转换为 Windsurf Cascade Skills 格式的适配器。

## 使用方法

### 转换单个技能

```bash
python convert_to_windsurf.py ../../skills/course-designer windsurf-skills/
```

### 转换所有技能

```bash
python convert_to_windsurf.py --all ../../skills windsurf-skills/
```

## 输出格式

转换后会创建 Windsurf Skill 目录结构：

```
windsurf-skills/
└── course-designer/
    ├── SKILL.md
    ├── scripts/          # 如果原技能有脚本
    ├── templates/        # 如果原技能有模板
    └── ...              # 其他资源文件
```

## Windsurf Skill 结构

每个 Windsurf Skill 包含：

- `SKILL.md` - 技能定义文件（YAML frontmatter + Markdown 内容）
- `scripts/` - 可执行脚本（可选）
- `templates/` - 模板文件（可选）
- `references/` - 参考文档（可选）
- 其他资源文件

## 在 Windsurf 中使用

### 方法一：项目级技能

将技能目录放在项目根目录的 `.windsurf/skills/` 目录下：

```
my-project/
├── .windsurf/
│   └── skills/
│       ├── course-designer/
│       │   └── SKILL.md
│       └── code-generator/
│           └── SKILL.md
└── src/
```

### 方法二：全局技能

将技能目录放在 Windsurf 的全局配置目录：

```bash
# macOS/Linux
~/.windsurf/skills/

# Windows
%APPDATA%\windsurf\skills\
```

## SKILL.md 格式

Windsurf 使用与 Agent Skills 相同的格式：

```markdown
---
name: course-designer
description: 帮助设计和规划课程内容
---

# Course Designer

技能详细说明...
```

## 注意事项

- ⚠️ 此适配方案基于 Windsurf Cascade Skills 的一般特性，需要根据实际 API 验证
- Windsurf 使用与 Agent Skills 相同的 SKILL.md 格式，转换主要是复制文件结构
- 脚本会自动复制技能的所有资源文件（scripts、templates 等）
- 建议查阅 [Windsurf 官方文档](https://docs.windsurf.com/) 获取最新信息

## 参考资源

- [Windsurf Cascade Skills 文档](https://docs.windsurf.com/windsurf/cascade/skills)
- [Windsurf 官网](https://windsurf.com/)
