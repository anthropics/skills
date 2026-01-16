# 适配器示例

本目录包含转换后的示例文件，展示了不同平台的适配格式。

## 示例文件位置

### Cursor 格式示例

位置：`examples/cursor/`

- `course-designer.md` - 课程设计技能的 Cursor 自定义指令
- `code-generator.md` - 代码生成技能的 Cursor 自定义指令

**使用方法：**
```bash
# 复制到项目 .cursor/rules/ 目录
cp examples/cursor/course-designer.md .cursor/rules/
```

### Trae 格式示例

位置：`examples/trae/`

- `course-designer/trae-plugin.json` - Trae 插件配置
- `code-generator/trae-plugin.json` - Trae 插件配置

**使用方法：**
```bash
# 复制插件目录到 Trae 插件目录
cp -r examples/trae/course-designer /path/to/trae/plugins/
```

### Qoder 格式示例

位置：`examples/qoder/`

- `course-designer-agent/` - Qoder Agent 配置和模块
  - `qoder-agent-config.json` - Agent 配置文件
  - `course_designer_agent.py` - Python Agent 模块
  - `SKILL.md` - 原始技能定义

**使用方法：**
```bash
# 复制 agent 目录到 Qoder agents 目录
cp -r examples/qoder/course-designer-agent /path/to/qoder/agents/
```

### CodeBuddy 格式示例

位置：`examples/codebuddy/`

- `course-designer/` - CodeBuddy 插件
  - `manifest.json` - 插件清单
  - `workflows/course-designer.json` - 工作流定义
  - `skills/course-designer/SKILL.md` - 技能定义

**使用方法：**
```bash
# 复制插件目录到 CodeBuddy 插件目录
cp -r examples/codebuddy/course-designer /path/to/codebuddy/plugins/
```

### Windsurf 格式示例

位置：`examples/windsurf/` 或 `adapters-output/windsurf/`

- `course-designer/` - Windsurf Skill
  - `SKILL.md` - 技能定义（与 Agent Skills 格式相同）
  - `scripts/` - 脚本文件（如果原技能有）
  - `templates/` - 模板文件（如果原技能有）

**使用方法：**
```bash
# 项目级：复制到项目 .windsurf/skills/ 目录
cp -r adapters-output/windsurf/course-designer .windsurf/skills/

# 全局级：复制到 ~/.windsurf/skills/ 目录
cp -r adapters-output/windsurf/course-designer ~/.windsurf/skills/
```

## 生成更多示例

使用转换脚本生成更多示例：

```bash
# 转换所有技能到所有平台
cd adapters
python convert_all.py ../skills ../adapters-output

# 或转换单个平台
python cursor/convert_to_cursor.py --all ../skills examples/cursor
python trae/convert_to_trae.py --all ../skills examples/trae
python qoder/convert_to_qoder.py --all ../skills examples/qoder
python codebuddy/convert_to_codebuddy.py --all ../skills examples/codebuddy
python windsurf/convert_to_windsurf.py --all ../skills examples/windsurf
```

## 注意事项

- ⚠️ 这些示例文件为理论性转换结果，尚未在实际平台上验证
- 配置文件格式可能需要根据实际平台 API 调整
- 建议在实际使用前查阅目标平台的官方文档
